import abc

class ModelParser:
    @abc.abstractmethod
    def get_parse_tree(self, file_name: str):
        pass