from timeit import default_timer as timer


class Logger:
    def __init__(self):
        self._start_timer_dict = dict()
        self._end_timer_dict = dict()

    def start_timer(self, name: str):
        assert name not in self._start_timer_dict
        self._start_timer_dict[name] = timer()

    def stop_timer(self, name: str):
        assert name not in self._end_timer_dict
        self._end_timer_dict[name] = timer()

    def reset_timer(self):
        self._start_timer_dict = dict()
        self._end_timer_dict = dict()

    def get_duration_time(self, name: str):
        assert name in self._start_timer_dict and name in self._end_timer_dict
        return self._end_timer_dict[name] - self._start_timer_dict[name]

