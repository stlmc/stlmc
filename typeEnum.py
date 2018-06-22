import enum

@enum.unique
class Type(enum.Enum):
    BOOL, INT, REAL = range(3)

