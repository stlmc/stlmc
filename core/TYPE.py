import enum

@enum.unique
class Type(enum.Enum):
    Bool, Int, Real = range(3)

