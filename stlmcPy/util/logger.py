import abc


class Logger:
    def __init__(self):
        self.info = ""

    @abc.abstractmethod
    def add_log_info(self, message: str):
        self.info += message + "\n"

    @abc.abstractmethod
    def get_log_info(self):
        return self.info

    @abc.abstractmethod
    def write_to_file(self, file_name: str):
        f = open(file_name, 'w')
        f.write(self.info)
        f.close()
