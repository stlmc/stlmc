import csv


class Logger:
    def __init__(self):
        self.lines = list()
        self.line = dict()

    def clear_log(self):
        self.lines = list()
        self.line = dict()

    def add_bound(self, bound):
        self.line["bound"] = str(bound)

    def add_step1_time(self, step1_time):
        self.line["step1 time"] = str(step1_time)

    def add_smt_solving_time(self, smt_solving):
        self.line["smt solving time"] = str(smt_solving)

    def add_literal_set_time(self, prep_max_time):
        self.line["preparing max literal set"] = str(prep_max_time)

    def add_hylaa_time(self, hylaa_time):
        self.line["hylaa time"] = str(hylaa_time)

    def add_loop_time(self, loop):
        self.line["loop"] = str(loop)

    def add_total_time(self, total):
        self.line["total"] = str(total)

    def add_result(self, result):
        self.line["result"] = str(result)

    def concat(self, lines:dict):
        for line in lines:
            self.lines.append(line)

    def add_log_info(self):
        # assumption:
        # bound, step1 time, smt solving time, prep max literal set, hylaa time, loop, total, result
        self.lines.append(self.line)
        self.line = dict()

    def get_log_info(self):
        return self.lines

    def get_log(self):
        return self.line

    def write_to_file(self, file_name: str):
        with open(file_name, 'w', newline='') as csvfile:
            fieldnames = ['bound', 'step1 time', 'smt solving time', 'preparing max literal set', 'hylaa time', 'loop', 'total', 'result']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

            writer.writeheader()
            for line in self.lines:
                writer.writerow(line)
