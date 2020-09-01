import csv
import os
from timeit import default_timer as timer


class Logger:
    def __init__(self):
        self._output_file = ""
        self._line = dict()
        self._start_timer_dict = dict()
        self._end_timer_dict = dict()

    # file_name : something.csv
    def set_output_file_name(self, file_name: str):
        self._output_file = file_name

    def add_info(self, key, value):
        self._line[str(key)] = str(value)

    def start_timer(self, name: str):
        assert name not in self._start_timer_dict
        self._start_timer_dict[name] = timer()

    def stop_timer(self, name: str):
        assert name not in self._end_timer_dict
        self._end_timer_dict[name] = timer()

    def reset_timer(self):
        self._start_timer_dict = dict()
        self._end_timer_dict = dict()

    def reset_timer_without(self, *name_args):
        new_start_timer_dict = dict()
        new_end_timer_dict = dict()
        for name in name_args:
            if name in self._start_timer_dict:
                new_start_timer_dict[name] = self._start_timer_dict[name]
            if name in self._end_timer_dict:
                new_end_timer_dict[name] = self._end_timer_dict[name]
        self._start_timer_dict = new_start_timer_dict
        self._end_timer_dict = new_end_timer_dict

    def get_duration_time(self, name: str):
        assert name in self._start_timer_dict and name in self._end_timer_dict
        return self._end_timer_dict[name] - self._start_timer_dict[name]

    def clear(self):
        self._line = dict()

    def write_to_csv(self, file_name: str = None, overwrite=False):
        if file_name is None:
            file_name = self._output_file

        write_flags = {'write': 'w', 'append': 'a+'}
        if overwrite:
            write_flags = {'write': 'w', 'append': 'w'}

        assert not (file_name == "")
        fieldnames = ['bound', 'loop', 'constraint size', 'smt solving time',
                      'preparing max literal set', 'hylaa time',
                      'loop total', 'total', 'result']
        if not os.path.exists(file_name + ".csv"):
            with open(file_name + ".csv", write_flags['write'], newline='') as csv_file:
                writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
                writer.writeheader()
                if len(self._line) > 0:
                    writer.writerow(self._line)
                    self.clear()
        else:
            with open(file_name + ".csv", write_flags['append'], newline='') as csv_file:
                writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
                if overwrite:
                    writer.writeheader()

                if len(self._line) > 0:
                    writer.writerow(self._line)
                    self.clear()

