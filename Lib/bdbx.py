import dis
import fnmatch
import os
import sys

from dataclasses import dataclass
from inspect import CO_GENERATOR, CO_COROUTINE, CO_ASYNC_GENERATOR
from types import FrameType, CodeType
from typing import Callable


__all__ = ["BdbQuit", "Bdb", "Breakpoint"]

GENERATOR_AND_COROUTINE_FLAGS = CO_GENERATOR | CO_COROUTINE | CO_ASYNC_GENERATOR


MEVENT = sys.monitoring.events


class BdbxSetBreakpointException(Exception):
    pass


class BdbxQuit(Exception):
    pass


class Breakpoint:
    """Breakpoint class.

    Implements temporary breakpoints, ignore counts, disabling and
    (re)-enabling, and conditionals.

    Breakpoints are indexed by number through bpbynumber and by
    the (file, line) tuple using bplist.  The former points to a
    single instance of class Breakpoint.  The latter points to a
    list of such instances since there may be more than one
    breakpoint per line.

    When creating a breakpoint, its associated filename should be
    in canonical form.  If funcname is defined, a breakpoint hit will be
    counted when the first line of that function is executed.  A
    conditional breakpoint always counts a hit.
    """

    # XXX Keeping state in the class is a mistake -- this means
    # you cannot have more than one active Bdb instance.

    next = 1        # Next bp to be assigned
    bplist = {}     # indexed by (file, lineno) tuple
    bpbynumber = [None] # Each entry is None or an instance of Bpt
                # index 0 is unused, except for marking an
                # effective break .... see effective()
    monitor_genie = None

    def __init__(self, file, line, temporary=False, cond=None, funcname=None, code: CodeType | None = None):
        self.funcname = funcname
        # Needed if funcname is not None.
        self.func_first_executable_line = None
        self.file = file    # This better be in canonical form!
        self.line = line
        self.temporary = temporary
        self.cond = cond
        self.enabled = True
        self.ignore = 0
        self.hits = 0
        self.code = code
        self.number = Breakpoint.next
        Breakpoint.next += 1
        # Build the two lists
        self.bpbynumber.append(self)
        if (file, line) in self.bplist:
            self.bplist[file, line].append(self)
        else:
            self.bplist[file, line] = [self]

    @staticmethod
    def clearBreakpoints():
        for bps in Breakpoint.bplist.values():
            for bp in bps:
                Breakpoint.monitor_genie.remove_breakpoint(bp)
        Breakpoint.next = 1
        Breakpoint.bplist = {}
        Breakpoint.bpbynumber = [None]

    def deleteMe(self):
        """Delete the breakpoint from the list associated to a file:line.

        If it is the last breakpoint in that position, it also deletes
        the entry for the file:line.
        """

        index = (self.file, self.line)
        self.bpbynumber[self.number] = None   # No longer in list
        self.bplist[index].remove(self)
        self.monitor_genie.remove_breakpoint(self)
        if not self.bplist[index]:
            # No more bp for this f:l combo
            del self.bplist[index]

    def enable(self):
        """Mark the breakpoint as enabled."""
        self.enabled = True

    def disable(self):
        """Mark the breakpoint as disabled."""
        self.enabled = False

    def bpprint(self, out=None):
        """Print the output of bpformat().

        The optional out argument directs where the output is sent
        and defaults to standard output.
        """
        if out is None:
            out = sys.stdout
        print(self.bpformat(), file=out)

    def bpformat(self):
        """Return a string with information about the breakpoint.

        The information includes the breakpoint number, temporary
        status, file:line position, break condition, number of times to
        ignore, and number of times hit.

        """
        if self.temporary:
            disp = 'del  '
        else:
            disp = 'keep '
        if self.enabled:
            disp = disp + 'yes  '
        else:
            disp = disp + 'no   '
        ret = '%-4dbreakpoint   %s at %s:%d' % (self.number, disp,
                                                self.file, self.line)
        if self.cond:
            ret += '\n\tstop only if %s' % (self.cond,)
        if self.ignore:
            ret += '\n\tignore next %d hits' % (self.ignore,)
        if self.hits:
            if self.hits > 1:
                ss = 's'
            else:
                ss = ''
            ret += '\n\tbreakpoint already hit %d time%s' % (self.hits, ss)
        return ret

    def belong_to(self, code: CodeType):
        """returns True if the breakpoint belongs to the given code object"""
        if os.path.abspath(self.file) == os.path.abspath(code.co_filename) and \
                self.line >= code.co_firstlineno:
            for instr in dis.get_instructions(code):
                if instr.positions.lineno == self.line:
                    return True
        return False

    def __str__(self):
        "Return a condensed description of the breakpoint."
        return 'breakpoint %s at %s:%s' % (self.number, self.file, self.line)

# -----------end of Breakpoint class----------


class MonitorGenie:
    """
    MonitorGenie is a layer to handle PEP-669 events aka sys.monitoring.

    It saves the trouble for the debugger to handle the monitoring events.
    MonitorGenie takes file and function breakpoints, and an action to start
    the monitoring. The accepted actions are:
        "step"
        "next"
        "return"
        "continue"
    """
    def __init__(
        self,
        tool_id: int,
        debugger_entry: Callable[[FrameType, Breakpoint | None, int, dict | None], None]
    ):
        self._action = None
        self._frame = None
        self._tool_id = tool_id
        self._returning = False
        self._tasks = []
        self._until_line_number = None
        self._bound_breakpoints: dict[CodeType, list[Breakpoint]] = {}
        self._free_breakpoints: list[Breakpoint] = []
        self._debugger_entry = debugger_entry 
        self._code_with_events = set()
        sys.monitoring.use_tool_id(tool_id, "MonitorGenie")
        self._register_callbacks()

    # ========================================================================
    # ============================= Public API ===============================
    # ========================================================================

    def start_monitor(self, action: str, frame: FrameType, arg = None):
        """starts monitoring with the given action and frame"""
        self._clear_monitor()
        self._try_bind_breakpoints(frame.f_code)
        self._set_events_for_breakpoints()
        self._action, self._frame = action, frame
        if action == "step":
            self._add_global_events(MEVENT.CALL | MEVENT.LINE | MEVENT.PY_RETURN | MEVENT.PY_YIELD | MEVENT.PY_START | MEVENT.PY_RESUME)
        elif action == "next":
            if not self._returning:
                self._add_local_events(frame.f_code, MEVENT.LINE | MEVENT.PY_RETURN | MEVENT.STOP_ITERATION)
            elif frame.f_back:
                self._add_local_events(frame.f_back.f_code, MEVENT.LINE | MEVENT.PY_RETURN | MEVENT.STOP_ITERATION)
        elif action == "until":
            if not self._returning:
                self._add_local_events(frame.f_code, MEVENT.LINE | MEVENT.PY_RETURN | MEVENT.STOP_ITERATION)
            else:
                self._add_global_events(MEVENT.LINE)
            self._until_line_number = arg
        elif action == "return":
            if not self._returning:
                self._add_local_events(frame.f_code, MEVENT.PY_RETURN | MEVENT.STOP_ITERATION)
            elif frame.f_back:
                self._add_local_events(frame.f_back.f_code, MEVENT.LINE | MEVENT.PY_RETURN)
        elif action == "continue":
            pass

        self._add_global_events(MEVENT.RAISE)

        self._returning = False
        sys.monitoring.restart_events()

    def stop_monitor(self):
        """stops monitoring"""
        self._clear_monitor()

    def start_monitor_code(self, code: CodeType):
        """starts monitoring when the given code is executed"""
        self._clear_monitor()
        self._action, self._frame = "step", None
        self._add_local_events(code, MEVENT.LINE | MEVENT.CALL | MEVENT.PY_RETURN | MEVENT.PY_YIELD)
        sys.monitoring.restart_events()

    def add_breakpoint(self, breakpoint: Breakpoint):
        """adds a breakpoint to the list of breakpoints"""
        if breakpoint.code is None:
            self._free_breakpoints.append(breakpoint)
        else:
            if breakpoint.code not in self._bound_breakpoints:
                self._bound_breakpoints[breakpoint.code] = []
            self._bound_breakpoints[breakpoint.code].append(breakpoint)

    def remove_breakpoint(self, breakpoint: Breakpoint):
        """removes a breakpoint from the list of breakpoints"""
        if breakpoint.code is None:
            self._free_breakpoints.remove(breakpoint)
        else:
            self._bound_breakpoints[breakpoint.code].remove(breakpoint)

    # ========================================================================
    # ============================ Private API ===============================
    # ========================================================================

    def _clear_monitor(self):
        sys.monitoring.set_events(self._tool_id, 0)
        for code in self._code_with_events:
            sys.monitoring.set_local_events(self._tool_id, code, 0)
        self._code_with_events = set()

    def _add_global_events(self, events):
        curr_events = sys.monitoring.get_events(self._tool_id)
        sys.monitoring.set_events(self._tool_id, curr_events | events)

    def _add_local_events(self, code, events):
        curr_events = sys.monitoring.get_local_events(self._tool_id, code)
        self._code_with_events.add(code)
        sys.monitoring.set_local_events(self._tool_id, code, curr_events | events)

    def _set_events_for_breakpoints(self):
        if self._free_breakpoints:
            self._add_global_events(MEVENT.PY_START)
        for code, bp_list in self._bound_breakpoints.items():
            for breakpoint in bp_list:
                if breakpoint.line is not None:
                    self._add_local_events(code, MEVENT.LINE)
                else:
                    self._add_local_events(code, MEVENT.PY_START)

    def _try_bind_breakpoints(self, code):
        # copy the breakpoints so we can remove bp from it
        bp_dirty = False
        for bp in self._free_breakpoints[:]:
            if bp.belong_to(code):
                self.remove_breakpoint(bp)
                bp.code = code
                self.add_breakpoint(bp)
                bp_dirty = True
        if bp_dirty:
            self._set_events_for_breakpoints()
            if not self._free_breakpoints:
                sys.monitoring.set_events(self._tool_id, 0)

    def _stophere(self, code, line_number=None):
        if self._action == "step":
            return True
        elif self._action == "next":
            return (code == self._frame.f_code or
                    (self._frame.f_back and code == self._frame.f_back.f_code))
        elif self._action == "until":
            return line_number is None or self._until_line_number <= line_number
        elif self._action == "return":
            return True
        return False

    def _breakhere(self, code, line_number):
        bp_list = []
        if code in self._bound_breakpoints:
            for bp in self._bound_breakpoints[code]:
                # There are two possible cases
                # the line_number could be a real line number and match
                # or the line_number is None which only be given by PY_START
                # and will match on function breakpoints
                if bp.line == line_number:
                    bp_list.append(bp)
        return bp_list

    # Callbacks for the real sys.monitoring

    def _register_callbacks(self):
        sys.monitoring.register_callback(self._tool_id, MEVENT.LINE, self._line_callback)
        sys.monitoring.register_callback(self._tool_id, MEVENT.CALL, self._call_callback)
        sys.monitoring.register_callback(self._tool_id, MEVENT.PY_START, self._start_callback)
        sys.monitoring.register_callback(self._tool_id, MEVENT.PY_RESUME, self._start_callback)
        sys.monitoring.register_callback(self._tool_id, MEVENT.PY_YIELD, self._return_callback)
        sys.monitoring.register_callback(self._tool_id, MEVENT.PY_RETURN, self._return_callback)
        sys.monitoring.register_callback(self._tool_id, MEVENT.RAISE, self._exception_callback)
        sys.monitoring.register_callback(self._tool_id, MEVENT.STOP_ITERATION, self._stop_iteration_callback)

    def _line_callback(self, code, line_number):
        if bp := self._breakhere(code, line_number):
            self._start_debugger(sys._getframe().f_back, bp, MEVENT.LINE,
                                 {"code": code, "line_number": line_number})
        elif self._stophere(code, line_number=line_number):
            if self._action == "return" and self._frame.f_code == code:
                return
            self._start_debugger(sys._getframe().f_back, None, MEVENT.LINE,
                                 {"code": code, "line_number": line_number})
        else:
            return sys.monitoring.DISABLE

    def _call_callback(self, code, instruction_offset, callable, arg0):
        # The only possible trigget for this is "step" action
        # If the callable is instrumentable, do it, otherwise ignore it
        code = None
        if hasattr(callable, "__code__"):
            code = callable.__code__
        elif hasattr(callable, "__call__"):
            try:
                code = callable.__call__.__func__.__code__
            except AttributeError:
                pass
        if code is not None:
            self._add_local_events(code, MEVENT.LINE | MEVENT.PY_START)

    def _start_callback(self, code, instruction_offset):
        self._try_bind_breakpoints(code)
        if bp := self._breakhere(code, None):
            self._start_debugger(sys._getframe().f_back, bp, MEVENT.PY_START,
                                 {"code": code, "instruction_offset": instruction_offset})
        elif self._stophere(code):
            self._start_debugger(sys._getframe().f_back, None, MEVENT.PY_START,
                                 {"code": code, "instruction_offset": instruction_offset})
        else:
            return sys.monitoring.DISABLE

    def _return_callback(self, code, instruction_offset, retval):
        if self._stophere(code):
            self._returning = True
            self._start_debugger(sys._getframe().f_back, None, MEVENT.PY_RETURN,
                                 {"code": code, "instruction_offset": instruction_offset, "retval": retval})
        else:
            return sys.monitoring.DISABLE

    def _exception_callback(self, code, instruction_offset, exception):
        if self._stophere(code):
            self._start_debugger(sys._getframe().f_back, None, MEVENT.RAISE,
                                 {"code": code, "instruction_offset": instruction_offset, "exception": exception})

    def _stop_iteration_callback(self, code, instruction_offset, exception):
        self._start_debugger(sys._getframe().f_back, None, MEVENT.STOP_ITERATION,
                             {"code": code, "instruction_offset": instruction_offset, "exception": exception})

    def _start_debugger(self, frame, breakpoint, event, args):
        self._debugger_entry(frame, breakpoint, event, args)


@dataclass
class StopEvent:
    frame: FrameType
    line_number: int
    return_value: object = None
    exception : BaseException = None
    is_call: bool = False
    is_return: bool = False

class Bdbx:
    """Bdbx is a singleton class that implements the debugger logic"""
    _instance = None

    def __new__(cls):
        if Bdbx._instance is None:
            instance = super().__new__(cls)
            instance._tool_id = sys.monitoring.DEBUGGER_ID
            instance._monitor_genie = MonitorGenie(instance._tool_id, instance.monitor_callback)
            Bdbx._instance = instance
        return Bdbx._instance

    def __init__(self):
        self._next_action = None
        self._next_action_frame = None
        self._stop_event = None
        self._stop_frame = None
        self._curr_frame = None
        self._main_pyfile = ''
        self.clear_breakpoints()

    # ========================================================================
    # ============================= Public API ===============================
    # ========================================================================

    def break_here(self, frame=None):
        """break into the debugger as soon as possible"""
        if frame is None:
            frame = sys._getframe().f_back
        self.set_action("next", frame)
        self._monitor_genie.start_monitor(self._next_action, self._next_action_frame)

    def break_code(self, code):
        """break into the debugger when the given code is executed"""
        self.set_action("step", None)
        self._monitor_genie.start_monitor_code(code)

    def set_action(self, action, frame=None):
        """Set the next action, if frame is None, use the current frame"""
        if frame is None:
            frame = self._curr_frame

        self._next_action = action
        self._next_action_frame = frame

    def set_function_breakpoint(self, func):
        if not hasattr(func, "__code__"):
            raise BdbxSetBreakpointException(f"{func} is not a valid function!")
        abspath = os.path.abspath(func.__code__.co_filename)
        if not abspath:
            raise BdbxSetBreakpointException(f"Cann't find the source file for {func}!")
        # Setting line_number to None for function breakpoints
        bp = Breakpoint(abspath, None, func.__code__)
        self._breakpoints.append(bp)
        self._monitor_genie.add_breakpoint(bp)

    def set_file_breakpoint(self, filename, line_number):
        """Set a breakpoint at the given line number in the given file

            The caller is responsible for checking that the file exists and
            that the line number is valid.
        """
        bp = Breakpoint(filename, line_number, None)
        self._breakpoints.append(bp)
        self._monitor_genie.add_breakpoint(bp)

    def clear_breakpoints(self):
        if hasattr(self, "_breakpoints"):
            for bp in self._breakpoints:
                self._monitor_genie.remove_breakpoint(bp)
        self._breakpoints = []

    def select_frame(self, index, offset=False):
        """Select a frame in the stack"""
        if offset:
            index += self._curr_frame_idx
        if index < 0:
            index = 0
        elif index >= len(self._stack):
            index = len(self._stack) - 1
        self._curr_frame_idx = index
        self._curr_frame = self._stack[index]

    # Data accessors

    def get_current_frame(self):
        """Get the current frame"""
        return self._curr_frame

    def get_current_frame_idx(self):
        """Get the current frame index"""
        return self._curr_frame_idx

    def get_stack(self):
        """Get the current stack"""
        return self._stack

    def get_breakpoints(self):
        """Get all the breakpoints"""
        return self._breakpoints

    # Interface to be implemented by the debugger

    def dispatch_event(self, event: StopEvent):
        pass

    # communication with MonitorGenie

    def monitor_callback(self, frame, breakpoints, event, event_arg):
        """Callback entry from MonitorGenie"""
        
        self._curr_breakpoint = breakpoints
        self._stop_frame = frame
        self._curr_frame = frame
        self._stack = self._get_stack_from_frame(frame)
        self._curr_frame_idx = len(self._stack) - 1

        if event == MEVENT.LINE:
            self._stop_event = StopEvent(frame, event_arg["line_number"])
        elif event == MEVENT.PY_START or event == MEVENT.PY_RESUME:
            self._stop_event = StopEvent(frame, 0, is_call=True)
        elif event == MEVENT.PY_RETURN or event == MEVENT.PY_YIELD:
            self._stop_event = StopEvent(frame, 0, is_return=True)
        else:
            raise RuntimeError("Not supposed to be here")

        self.dispatch_event(self._stop_event)

        # After the dispatch returns, reset the monitor
        self._monitor_genie.start_monitor(self._next_action, self._next_action_frame)

    # ========================================================================
    # ======================= Helper functions ===============================
    # ========================================================================

    def _get_stack_from_frame(self, frame):
        """Get call stack from the latest frame, oldest frame at [0]"""
        stack = []
        while frame:
            stack.append(frame)
            frame = frame.f_back
        stack.reverse()
        return stack



class BdbQuit(Exception):
    """Exception to give up completely."""


class Bdb:
    """Generic Python debugger base class.

    This class takes care of details of the trace facility;
    a derived class should implement user interaction.
    The standard debugger class (pdb.Pdb) is an example.

    The optional skip argument must be an iterable of glob-style
    module name patterns.  The debugger will not step into frames
    that originate in a module that matches one of these patterns.
    Whether a frame is considered to originate in a certain module
    is determined by the __name__ in the frame globals.
    """
    _instance = None

    def __new__(cls, *args, **kwargs):
        if Bdb._instance is None:
            instance = super().__new__(cls)
            instance._tool_id = sys.monitoring.DEBUGGER_ID
            instance._monitor_genie = MonitorGenie(instance._tool_id, instance.monitor_callback)
            Breakpoint.monitor_genie = instance._monitor_genie
            Bdb._instance = instance
        return Bdb._instance

    def __init__(self, skip=None):
        self.skip = set(skip) if skip else None
        self.breaks = {}
        self.fncache = {}
        self.frame_returning = None
        self._next_action = None
        self._next_action_frame = None
        self._stop_event = None
        self._curr_frame = None
        self._main_pyfile = ''
        self._user_frame = None
        self.botframe = None

        self._load_breaks()

    # communication with MonitorGenie

    def monitor_callback(self, frame, breakpoints, event, event_arg):
        """Callback entry from MonitorGenie"""

        if self.skip and self.is_skipped_module(frame.f_globals.get('__name__')):
            return

        if event == MEVENT.PY_RETURN:
            # Ignore return events for generators unless it's a step
            if self._next_action != "step" and frame.f_code.co_flags & GENERATOR_AND_COROUTINE_FLAGS:
                self._monitor_genie.start_monitor(self._next_action, self._next_action_frame, self._next_action_arg)
                return

        valid_breakpoint = self._process_breakpoints(frame, breakpoints)

        if breakpoints and not valid_breakpoint:
            # We are stopped by a possible set of breakpoints, but none of
            # them passed the condition check
            return

        self._curr_breakpoint = valid_breakpoint
        # To make pdb happy
        self.currentbp = valid_breakpoint.number if valid_breakpoint else None
        self._curr_frame = frame
        self._next_action_frame = frame
        self._stack = self._get_stack_from_frame(frame)
        self._curr_frame_idx = len(self._stack) - 1

        if event == MEVENT.LINE:
            self._stop_event = StopEvent(frame, event_arg["line_number"])
        elif event == MEVENT.PY_START or event == MEVENT.PY_RESUME:
            self._stop_event = StopEvent(frame, 0, is_call=True)
        elif event == MEVENT.PY_RETURN or event == MEVENT.PY_YIELD:
            self._stop_event = StopEvent(frame, 0, is_return=True, return_value=event_arg["retval"])
        elif event == MEVENT.STOP_ITERATION or event == MEVENT.RAISE:
            self._stop_event = StopEvent(frame, 0, exception=event_arg["exception"])
        else:
            raise RuntimeError("Not supposed to be here")

        self.dispatch_event(self._stop_event)

        # After the dispatch returns, reset the monitor
        self._monitor_genie.start_monitor(self._next_action, self._next_action_frame, self._next_action_arg)

    def break_here(self, frame=None):
        """break into the debugger as soon as possible"""
        if frame is None:
            frame = sys._getframe().f_back
        self.set_action("step", frame)
        self._monitor_genie.start_monitor(self._next_action, self._next_action_frame)

    def break_code(self, code):
        """break into the debugger when the given code is executed"""
        self.set_action("step", None)
        self._monitor_genie.start_monitor_code(code)

    def _process_breakpoints(self, frame, breakpoints):
        """process the breakpoints and return the one that is hit"""
        if not breakpoints:
            return None
        for bp in breakpoints:
            if not bp.enabled:
                continue
            bp.hits += 1
            if bp.cond:
                try:
                    bp_cond = eval(bp.cond, frame.f_globals, frame.f_locals)
                except:
                    # If the condition expression cannot be evaluated, we
                    # stop and do not clear the temp
                    return bp
            else:
                bp_cond = True
            if bp_cond:
                if bp.ignore > 0:
                    bp.ignore -= 1
                    continue
                if bp.temporary:
                    self.do_clear(str(bp.number))
                return bp

    # Dispatch

    def dispatch_event(self, event: StopEvent):
        if self.botframe is None:
            self.botframe = event.frame.f_back
        if event.is_call:
            self.user_call(event.frame, None)
        elif event.is_return:
            self.user_return(event.frame, event.return_value)
        elif event.exception:
            # Skip the internal stop iteration exception in generators
            if (isinstance(event.exception, StopIteration) and
                event.frame.f_code.co_flags & GENERATOR_AND_COROUTINE_FLAGS and
                event.frame == self._user_frame):
                return
            self.user_exception(event.frame, (type(event.exception), event.exception, event.exception.__traceback__))
        else:
            self.user_line(event.frame)

        if self.quitting:
            raise BdbQuit

    def canonic(self, filename):
        """Return canonical form of filename.

        For real filenames, the canonical form is a case-normalized (on
        case insensitive filesystems) absolute path.  'Filenames' with
        angle brackets, such as "<stdin>", generated in interactive
        mode, are returned unchanged.
        """
        if filename == "<" + filename[1:-1] + ">":
            return filename
        canonic = self.fncache.get(filename)
        if not canonic:
            canonic = os.path.abspath(filename)
            canonic = os.path.normcase(canonic)
            self.fncache[filename] = canonic
        return canonic

    def reset(self):
        """Set values of attributes as ready to start debugging."""
        import linecache
        linecache.checkcache()
        self.botframe = None
        self._set_stopinfo(None, None)

    # Normally derived classes don't override the following
    # methods, but they may if they want to redefine the
    # definition of stopping and breakpoints.

    def is_skipped_module(self, module_name):
        "Return True if module_name matches any skip pattern."
        if module_name is None:  # some modules do not have names
            return False
        for pattern in self.skip:
            if fnmatch.fnmatch(module_name, pattern):
                return True
        return False

    def do_clear(self, arg):
        """Remove temporary breakpoint.

        Must implement in derived classes or get NotImplementedError.
        """
        raise NotImplementedError("subclass of bdb must implement do_clear()")

    def break_anywhere(self, frame):
        """Return True if there is any breakpoint for frame's filename.
        """
        return self.canonic(frame.f_code.co_filename) in self.breaks

    # Derived classes should override the user_* methods
    # to gain control.

    def user_call(self, frame, argument_list):
        """Called if we might stop in a function."""
        pass

    def user_line(self, frame):
        """Called when we stop or break at a line."""
        pass

    def user_return(self, frame, return_value):
        """Called when a return trap is set here."""
        pass

    def user_exception(self, frame, exc_info):
        """Called when we stop on an exception."""
        pass

    def _set_stopinfo(self, stopframe, returnframe, stoplineno=0):
        """Set the attributes for stopping.

        If stoplineno is greater than or equal to 0, then stop at line
        greater than or equal to the stopline.  If stoplineno is -1, then
        don't stop at all.
        """
        self.stopframe = stopframe
        self.returnframe = returnframe
        self.quitting = False
        # stoplineno >= 0 means: stop at line >= the stoplineno
        # stoplineno -1 means: don't stop at all
        self.stoplineno = stoplineno

    # Derived classes and clients can call the following methods
    # to affect the stepping state.
    def set_action(self, action, frame=None, arg=None):
        """Set the next action, if frame is None, use the current frame"""
        if frame is None:
            frame = self._curr_frame

        self._next_action = action
        self._next_action_frame = frame
        self._next_action_arg = arg
        self._user_frame = frame

    def set_until(self, frame, lineno=None):
        """Stop when the line with the lineno greater than the current one is
        reached or when returning from current frame."""
        # the name "until" is borrowed from gdb
        if lineno is None:
            lineno = frame.f_lineno + 1
        self.set_action("until", frame, lineno)

    def set_step(self):
        """Stop after one line of code."""
        self.set_action("step", None)

    def set_next(self, frame):
        """Stop on the next line in or below the given frame."""
        self.set_action("next", frame)

    def set_return(self, frame):
        """Stop when returning from the given frame."""
        self.set_action("return", frame)

    def set_trace(self, frame=None):
        """Start debugging from frame.

        If frame is not specified, debugging starts from caller's frame.
        """
        """break into the debugger as soon as possible"""
        if frame is None:
            frame = sys._getframe().f_back
        self.reset()
        self.set_action("next", frame)
        while frame:
            self.botframe = frame
            frame = frame.f_back
        self._monitor_genie.start_monitor(self._next_action, self._next_action_frame)

    def set_continue(self):
        """Stop only at breakpoints or when finished.

        If there are no breakpoints, set the system trace function to None.
        """
        self.set_action("continue", None)

    def set_quit(self):
        """Set quitting attribute to True.

        Raises BdbQuit exception in the next call to a dispatch_*() method.
        """
        self.stopframe = self.botframe
        self.returnframe = None
        self.quitting = True
        self._monitor_genie.stop_monitor()

    # Derived classes and clients can call the following methods
    # to manipulate breakpoints.  These methods return an
    # error message if something went wrong, None if all is well.
    # Set_break prints out the breakpoint line and file:lineno.
    # Call self.get_*break*() to see the breakpoints or better
    # for bp in Breakpoint.bpbynumber: if bp: bp.bpprint().

    def _add_to_breaks(self, filename, lineno):
        """Add breakpoint to breaks, if not already there."""
        bp_linenos = self.breaks.setdefault(filename, [])
        if lineno not in bp_linenos:
            bp_linenos.append(lineno)

    def set_break(self, filename, lineno, temporary=False, cond=None,
                  funcname=None, code=None):
        """Set a new breakpoint for filename:lineno.

        If lineno doesn't exist for the filename, return an error message.
        The filename should be in canonical form.
        """
        filename = self.canonic(filename)
        import linecache # Import as late as possible
        line = linecache.getline(filename, lineno)
        if not line:
            return 'Line %s:%d does not exist' % (filename, lineno)
        self._add_to_breaks(filename, lineno)
        if code:
            bp = Breakpoint(filename, lineno, temporary, cond, funcname, code)
        else:
            bp = Breakpoint(filename, lineno, temporary, cond, funcname)

        self._monitor_genie.add_breakpoint(bp)

        return None

    def _load_breaks(self):
        """Apply all breakpoints (set in other instances) to this one.

        Populates this instance's breaks list from the Breakpoint class's
        list, which can have breakpoints set by another Bdb instance. This
        is necessary for interactive sessions to keep the breakpoints
        active across multiple calls to run().
        """
        for (filename, lineno) in Breakpoint.bplist.keys():
            self._add_to_breaks(filename, lineno)

    def _prune_breaks(self, filename, lineno):
        """Prune breakpoints for filename:lineno.

        A list of breakpoints is maintained in the Bdb instance and in
        the Breakpoint class.  If a breakpoint in the Bdb instance no
        longer exists in the Breakpoint class, then it's removed from the
        Bdb instance.
        """
        if (filename, lineno) not in Breakpoint.bplist:
            self.breaks[filename].remove(lineno)
        if not self.breaks[filename]:
            del self.breaks[filename]

    def clear_break(self, filename, lineno):
        """Delete breakpoints for filename:lineno.

        If no breakpoints were set, return an error message.
        """
        filename = self.canonic(filename)
        if filename not in self.breaks:
            return 'There are no breakpoints in %s' % filename
        if lineno not in self.breaks[filename]:
            return 'There is no breakpoint at %s:%d' % (filename, lineno)
        # If there's only one bp in the list for that file,line
        # pair, then remove the breaks entry
        for bp in Breakpoint.bplist[filename, lineno][:]:
            bp.deleteMe()
        self._prune_breaks(filename, lineno)
        return None

    def clear_bpbynumber(self, arg):
        """Delete a breakpoint by its index in Breakpoint.bpbynumber.

        If arg is invalid, return an error message.
        """
        try:
            bp = self.get_bpbynumber(arg)
        except ValueError as err:
            return str(err)
        bp.deleteMe()
        self._prune_breaks(bp.file, bp.line)
        return None

    def clear_all_file_breaks(self, filename):
        """Delete all breakpoints in filename.

        If none were set, return an error message.
        """
        filename = self.canonic(filename)
        if filename not in self.breaks:
            return 'There are no breakpoints in %s' % filename
        for line in self.breaks[filename]:
            blist = Breakpoint.bplist[filename, line]
            for bp in blist:
                bp.deleteMe()
        del self.breaks[filename]
        return None

    def clear_all_breaks(self):
        """Delete all existing breakpoints.

        If none were set, return an error message.
        """
        if not self.breaks:
            return 'There are no breakpoints'
        for bp in Breakpoint.bpbynumber:
            if bp:
                bp.deleteMe()
        self.breaks = {}
        return None

    def get_bpbynumber(self, arg):
        """Return a breakpoint by its index in Breakpoint.bybpnumber.

        For invalid arg values or if the breakpoint doesn't exist,
        raise a ValueError.
        """
        if not arg:
            raise ValueError('Breakpoint number expected')
        try:
            number = int(arg)
        except ValueError:
            raise ValueError('Non-numeric breakpoint number %s' % arg) from None
        try:
            bp = Breakpoint.bpbynumber[number]
        except IndexError:
            raise ValueError('Breakpoint number %d out of range' % number) from None
        if bp is None:
            raise ValueError('Breakpoint %d already deleted' % number)
        return bp

    def get_break(self, filename, lineno):
        """Return True if there is a breakpoint for filename:lineno."""
        filename = self.canonic(filename)
        return filename in self.breaks and \
            lineno in self.breaks[filename]

    def get_breaks(self, filename, lineno):
        """Return all breakpoints for filename:lineno.

        If no breakpoints are set, return an empty list.
        """
        filename = self.canonic(filename)
        return filename in self.breaks and \
            lineno in self.breaks[filename] and \
            Breakpoint.bplist[filename, lineno] or []

    def get_file_breaks(self, filename):
        """Return all lines with breakpoints for filename.

        If no breakpoints are set, return an empty list.
        """
        filename = self.canonic(filename)
        if filename in self.breaks:
            return self.breaks[filename]
        else:
            return []

    def get_all_breaks(self):
        """Return all breakpoints that are set."""
        return self.breaks

    # Derived classes and clients can call the following method
    # to get a data structure representing a stack trace.

    def get_stack(self, f, t):
        """Return a list of (frame, lineno) in a stack trace and a size.

        List starts with original calling frame, if there is one.
        Size may be number of frames above or below f.
        """
        stack = []
        if t and t.tb_frame is f:
            t = t.tb_next
        while f is not None:
            stack.append((f, f.f_lineno))
            if f is self.botframe:
                break
            f = f.f_back
        stack.reverse()
        i = max(0, len(stack) - 1)
        while t is not None:
            stack.append((t.tb_frame, t.tb_lineno))
            t = t.tb_next
        if f is None:
            i = max(0, len(stack) - 1)
        return stack, i

    # ========================================================================
    # ======================= Helper functions ===============================
    # ========================================================================

    def _get_stack_from_frame(self, frame):
        """Get call stack from the latest frame, oldest frame at [0]"""
        stack = []
        while frame:
            stack.append(frame)
            frame = frame.f_back
        stack.reverse()
        return stack

    def format_stack_entry(self, frame_lineno, lprefix=': '):
        """Return a string with information about a stack entry.

        The stack entry frame_lineno is a (frame, lineno) tuple.  The
        return string contains the canonical filename, the function name
        or '<lambda>', the input arguments, the return value, and the
        line of code (if it exists).

        """
        import linecache, reprlib
        frame, lineno = frame_lineno
        filename = self.canonic(frame.f_code.co_filename)
        s = '%s(%r)' % (filename, lineno)
        if frame.f_code.co_name:
            s += frame.f_code.co_name
        else:
            s += "<lambda>"
        s += '()'
        if '__return__' in frame.f_locals:
            rv = frame.f_locals['__return__']
            s += '->'
            s += reprlib.repr(rv)
        if lineno is not None:
            line = linecache.getline(filename, lineno, frame.f_globals)
            if line:
                s += lprefix + line.strip()
        else:
            s += f'{lprefix}Warning: lineno is None'
        return s

    # The following methods can be called by clients to use
    # a debugger to debug a statement or an expression.
    # Both can be given as a string, or a code object.

    def run(self, cmd, globals=None, locals=None):
        """Debug a statement executed via the exec() function.

        globals defaults to __main__.dict; locals defaults to globals.
        """
        if globals is None:
            import __main__
            globals = __main__.__dict__
        if locals is None:
            locals = globals
        self.reset()
        if isinstance(cmd, str):
            cmd = compile(cmd, "<string>", "exec")

        if not isinstance(cmd, CodeType):
            raise TypeError("exec() arg 1 must be a string, bytes or code object")
        self.break_code(cmd)
        try:
            exec(cmd, globals, locals)
        except BdbQuit:
            pass
        finally:
            self.quitting = True

    def runeval(self, expr, globals=None, locals=None):
        """Debug an expression executed via the eval() function.

        globals defaults to __main__.dict; locals defaults to globals.
        """
        if globals is None:
            import __main__
            globals = __main__.__dict__
        if locals is None:
            locals = globals
        self.reset()

        if isinstance(expr, str):
            code = compile(expr, "<string>", "eval")
        else:
            code = expr
        
        if not isinstance(expr, CodeType):
            raise TypeError("eval() arg 1 must be a string, bytes or code object")

        self.break_code(code)
        try:
            return eval(code, globals, locals)
        except BdbQuit:
            pass
        finally:
            self.quitting = True

    def runctx(self, cmd, globals, locals):
        """For backwards-compatibility.  Defers to run()."""
        # B/W compatibility
        self.run(cmd, globals, locals)

    # This method is more useful to debug a single function call.

    def runcall(self, func, /, *args, **kwds):
        """Debug a single function call.

        Return the result of the function call.
        """
        self.reset()
        sys.settrace(self.trace_dispatch)
        res = None
        try:
            res = func(*args, **kwds)
        except BdbQuit:
            pass
        finally:
            self.quitting = True
            sys.settrace(None)
        return res


def set_trace():
    """Start debugging with a Bdb instance from the caller's frame."""
    Bdb().set_trace()



def checkfuncname(b, frame):
    """Return True if break should happen here.

    Whether a break should happen depends on the way that b (the breakpoint)
    was set.  If it was set via line number, check if b.line is the same as
    the one in the frame.  If it was set via function name, check if this is
    the right function and if it is on the first executable line.
    """
    if not b.funcname:
        # Breakpoint was set via line number.
        if b.line != frame.f_lineno:
            # Breakpoint was set at a line with a def statement and the function
            # defined is called: don't break.
            return False
        return True

    # Breakpoint set via function name.
    if frame.f_code.co_name != b.funcname:
        # It's not a function call, but rather execution of def statement.
        return False

    # We are in the right frame.
    if not b.func_first_executable_line:
        # The function is entered for the 1st time.
        b.func_first_executable_line = frame.f_lineno

    if b.func_first_executable_line != frame.f_lineno:
        # But we are not at the first line number: don't break.
        return False
    return True


def effective(file, line, frame):
    """Return (active breakpoint, delete temporary flag) or (None, None) as
       breakpoint to act upon.

       The "active breakpoint" is the first entry in bplist[line, file] (which
       must exist) that is enabled, for which checkfuncname is True, and that
       has neither a False condition nor a positive ignore count.  The flag,
       meaning that a temporary breakpoint should be deleted, is False only
       when the condiion cannot be evaluated (in which case, ignore count is
       ignored).

       If no such entry exists, then (None, None) is returned.
    """
    possibles = Breakpoint.bplist[file, line]
    for b in possibles:
        if not b.enabled:
            continue
        if not checkfuncname(b, frame):
            continue
        # Count every hit when bp is enabled
        b.hits += 1
        if not b.cond:
            # If unconditional, and ignoring go on to next, else break
            if b.ignore > 0:
                b.ignore -= 1
                continue
            else:
                # breakpoint and marker that it's ok to delete if temporary
                return (b, True)
        else:
            # Conditional bp.
            # Ignore count applies only to those bpt hits where the
            # condition evaluates to true.
            try:
                val = eval(b.cond, frame.f_globals, frame.f_locals)
                if val:
                    if b.ignore > 0:
                        b.ignore -= 1
                        # continue
                    else:
                        return (b, True)
                # else:
                #   continue
            except:
                # if eval fails, most conservative thing is to stop on
                # breakpoint regardless of ignore count.  Don't delete
                # temporary, as another hint to user.
                return (b, False)
    return (None, None)


# -------------------- testing --------------------

class Tdb(Bdb):
    def user_call(self, frame, args):
        name = frame.f_code.co_name
        if not name: name = '???'
        print('+++ call', name, args)
    def user_line(self, frame):
        import linecache
        name = frame.f_code.co_name
        if not name: name = '???'
        fn = self.canonic(frame.f_code.co_filename)
        line = linecache.getline(fn, frame.f_lineno, frame.f_globals)
        print('+++', fn, frame.f_lineno, name, ':', line.strip())
    def user_return(self, frame, retval):
        print('+++ return', retval)
    def user_exception(self, frame, exc_stuff):
        print('+++ exception', exc_stuff)
        self.set_continue()

def foo(n):
    print('foo(', n, ')')
    x = bar(n*10)
    print('bar returned', x)

def bar(a):
    print('bar(', a, ')')
    return a/2

def test():
    t = Tdb()
    t.run('import bdb; bdb.foo(10)')
