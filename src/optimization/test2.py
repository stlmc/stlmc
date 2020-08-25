from ctypes import *

BOOL = 0
INT = 1
REAL = 2


# class term_t(Structure):
#     _fields_ = [("_id", c_char_p),
#                 ("_type", c_int)]
#
#     def __init__(self, id: str, type):
#         Structure.__init__(self, id.encode('utf-8'), type)
#
#     def id(self):
#         return self._id.decode('utf-8')
#
#     def type(self):
#         return self._type


tt = cdll.LoadLibrary("libtest.so")
#tt.substitution_wrapper.restype = None
#tt.substitution_wrapper.argtypes = [POINTER(term_t)]


make_term = tt.make_term
make_term.restype = c_int
make_term.argtypes = [c_char_p, c_int]

print_table = tt.print_term_table
print_table.restype = None

init_symbol_table = tt.init_symbol_table
init_symbol_table.restype = None

delete_symbol_table = tt.delete_symbol_table
delete_symbol_table.restype = None

print_child = tt.print_child
print_child.restype = None
print_child.argtypes = [c_int]

add_child = tt.add_child
add_child.restype = None
add_child.argtypes = [c_int, c_int]

init_symbol_table()
sival = make_term(b"abcccccx", 2)
sival2 = make_term(b"abcccccx2123", 2)
sival3 = make_term(b"abcccccx21234", 2)
sival4 = make_term(b"abcccccx21235", 2)
sival5 = make_term(b"abcccccx21236", 2)
# print(sival)

add_child(sival, sival2)
add_child(sival, sival3)
add_child(sival, sival4)

# print_table()
print_child(sival)
delete_symbol_table()

#bbb = make_term(b"iii", 0)
#print(bbb.id())
'''
v = term_t("xyz", BOOL)
v1 = term_t("xyz2", BOOL)
v2 = term_t("xyz3", BOOL)
# print(v.id())
# print(v.type())
# ccc = b"iii"
# v.id = ccc
# print(ccc)
tt.substitution_wrapper(v)


class subst_pair(Structure):
    _fields_ = [("from", POINTER(term_t)),
                ("to", POINTER(term_t))]

    def __init__(self, f: term_t, t: term_t):
        Structure.__init__(self, f, t)


class SubstDict:
    def __init__(self):
        self._dict = dict()

    def add(self, key: term_t, value: term_t):
        self._dict[key] = subst_pair(key, value)


ss = SubstDict()
ss.add(v, v1)

tt.substitutions()


'''