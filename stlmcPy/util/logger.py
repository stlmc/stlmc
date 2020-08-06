

class Logger:
    def __init__(self):
        self.info = ""

    def add_log_info(self, message: str):
        self.info += message + "\n"

    def get_log_info(self):
        return self.info

    def write_to_file(self, file_name: str):
        f = open(file_name, 'w')
        f.write(self.info)
        f.close()
