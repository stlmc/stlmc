import os
import unittest

from stlmcPy.exception.exception import NotSupportedError
from stlmcPy.parser.config_visitor import ConfigVisitor


class ConfigVisitorTest(unittest.TestCase):

    def _generate_test_case_1(self):
        bound_config = "bound = \"{}, {}, {}\"".format(1, 2, 1)
        formula_config = "formula = \"{}, {}, {}\"".format(4, 5, 1)
        tb_config = "time-bound = {}".format(40)
        formula_encoding = "formula-encoding = \"{}\"".format("model-with-goal-enhanced")
        print_output = "print-output = \"{}\"".format("verbose")
        delta = "delta = {}".format(2)
        logic = "logic \"QF_LRA\""
        yices = "yices {{\n {} \n}}\n".format(logic)

        result_dict = dict()
        result_dict["lower_bound"] = 1
        result_dict["upper_bound"] = 2
        result_dict["step_bound"] = 1

        result_dict["lower_formula"] = 4
        result_dict["upper_formula"] = 5
        result_dict["step_formula"] = 1

        result_dict["time-bound"] = 40
        result_dict["formula-encoding"] = "model-with-goal-enhanced"
        result_dict["print-output"] = "verbose"
        result_dict["delta"] = 2

        yices_dict = dict()
        yices_dict["solver"] = "yices"
        yices_dict["logic"] = "QF_LRA"

        result_dict["solvers"] = [yices_dict]
        return "{}\n{}\n{}\n{}\n{}\n{}\n{}".format(bound_config, formula_config, tb_config, formula_encoding,
                                                   print_output, delta, yices), result_dict

    def _generate_test_case_2(self):
        bound_config = "bound = \"{}, {}\"".format(2, 5)
        formula_config = "formula = \"{}\"".format(4)
        tb_config = "time-bound = {}".format(10)
        formula_encoding = "formula-encoding = \"{}\"".format("model-with-goal-enhanced-assertion-test")
        logic = "logic \"QF_LRA\""
        yices = "yices {{\n {} \n}}\n".format(logic)

        result_dict = dict()
        result_dict["lower_bound"] = 2
        result_dict["upper_bound"] = 5
        result_dict["step_bound"] = 1

        result_dict["lower_formula"] = 4
        result_dict["upper_formula"] = 4
        result_dict["step_formula"] = 1

        result_dict["time-bound"] = 40
        result_dict["formula-encoding"] = "model-with-goal-enhanced-assertion-test"

        yices_dict = dict()
        yices_dict["solver"] = "yices"
        yices_dict["logic"] = "QF_LRA"

        result_dict["solvers"] = [yices_dict]
        return "{}\n{}\n{}\n{}\n{}".format(bound_config, formula_config, tb_config, formula_encoding,
                                           yices), result_dict

    def _generate_test_case_3(self):
        bound_config = "bound = \"{}, {}\"".format(5, 10)
        formula_config = "formula = \"{}\"".format(5)
        tb_config = "time-bound = {}".format(10)
        formula_encoding = "formula-encoding = \"{}\"".format("model-with-goal-enhanced")
        print_output = "print-output = \"{}\"".format("verbose")
        delta = "delta = {}".format(22)
        logic = "logic \"QF_NRA\""
        yices = "yices {{\n {} \n}}\n".format(logic)

        result_dict = dict()
        result_dict["lower_bound"] = 5
        result_dict["upper_bound"] = 10
        result_dict["step_bound"] = 1

        result_dict["lower_formula"] = 5
        result_dict["upper_formula"] = 5
        result_dict["step_formula"] = 1

        result_dict["time-bound"] = 10
        result_dict["formula-encoding"] = "model-with-goal-enhanced"
        result_dict["print-output"] = "verbose"
        result_dict["delta"] = 22

        yices_dict = dict()
        yices_dict["solver"] = "yices"
        yices_dict["logic"] = "QF_NRA"

        result_dict["solvers"] = [yices_dict]
        return "{}\n{}\n{}\n{}\n{}\n{}\n{}".format(bound_config, formula_config, tb_config, formula_encoding,
                                                   print_output, delta, yices), result_dict

    def _generate_test_case_4(self):
        bound_config = "bound = \"{}, {}\"".format(5, 10)
        formula_config = "formula = \"{}\"".format(5)
        tb_config = "time-bound = {}".format(10)
        formula_encoding = "formula-encoding = \"{}\"".format("model-with-goal-enhanced")
        print_output = "print-output = \"{}\"".format("verbose")
        delta = "delta = {}".format(22)

        fixed_steps = "fixed steps 0.01"
        time = "time 1"
        rme = "remainder estimation 1e-2"
        id_pred = "identity precondition"
        gnuplot_octagon = "gnuplot octagon d1, g1"
        ad_orders = "adaptive orders { min 4, max 8 }"
        cutoff = "cutoff 1e-12"
        precision = "precision 53"
        no_output = "no output"
        max_jumps = "max jumps 10"

        flowstar = "flowstar {{\n {}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{} \n}}\n".format(fixed_steps, time, rme, id_pred,
                                                                                        gnuplot_octagon, ad_orders,
                                                                                        cutoff, precision, no_output,
                                                                                        max_jumps)

        result_dict = dict()
        result_dict["lower_bound"] = 5
        result_dict["upper_bound"] = 10
        result_dict["step_bound"] = 1

        result_dict["lower_formula"] = 5
        result_dict["upper_formula"] = 5
        result_dict["step_formula"] = 1

        result_dict["time-bound"] = 10
        result_dict["formula-encoding"] = "model-with-goal-enhanced"
        result_dict["print-output"] = "verbose"
        result_dict["delta"] = 22

        fs_dict = dict()
        fs_dict["solver"] = "flowstar"
        fs_dict["fixed steps"] = "0.01"
        fs_dict["time"] = "1"
        fs_dict["remainder estimation"] = "1e-2"
        fs_dict["identity precondition"] = ""
        fs_dict["gnuplot octagon"] = "d1, g1"
        fs_dict["adaptive orders"] = "{ min 4, max 8 }"
        fs_dict["cutoff"] = "1e-12"
        fs_dict["precision"] = "53"
        fs_dict["no output"] = ""
        fs_dict["max jumps"] = "10"

        result_dict["solvers"] = [fs_dict]
        return "{}\n{}\n{}\n{}\n{}\n{}\n{}".format(bound_config, formula_config, tb_config, formula_encoding,
                                                   print_output, delta, flowstar), result_dict

    def test_parsing_1(self):
        file_string, result_dict = self._generate_test_case_1()

        file_name = "./test1.conf"
        f = open(file_name, "w")
        f.write(file_string)
        f.close()

        solvers = ["yices", "z3", "dreal"]
        yices_setting = dict()
        yices_setting["logic"] = "QF_NRA"

        solver_defaults = dict()
        solver_defaults["yices"] = yices_setting

        print_options = ["verbose", "debug", "normal"]
        encoding_list = ["model-with-goal-enhanced", "model-with-goal", "only-goal-stl",
                         "only-goal-stl-enhanced"]
        cv = ConfigVisitor(solvers, solver_defaults, encoding_list, print_options)
        conf_dict = cv.get_config_dict(file_name)

        if os.path.isfile(file_name):
            os.remove(file_name)

        self.assertEqual(conf_dict, result_dict, "parse wrong")

    def test_assertion_1(self):
        file_string, _ = self._generate_test_case_2()

        file_name = "./test2.conf"
        f = open(file_name, "w")
        f.write(file_string)
        f.close()

        solvers = ["yices", "z3", "dreal"]
        yices_setting = dict()
        yices_setting["logic"] = "QF_NRA"

        solver_defaults = dict()
        solver_defaults["yices"] = yices_setting

        print_options = ["verbose", "debug", "normal"]
        encoding_list = ["model-with-goal-enhanced", "model-with-goal", "only-goal-stl",
                         "only-goal-stl-enhanced"]
        cv = ConfigVisitor(solvers, solver_defaults, encoding_list, print_options)
        with self.assertRaises(NotSupportedError):
            _ = cv.get_config_dict(file_name)

        if os.path.isfile(file_name):
            os.remove(file_name)

    def test_parsing_2(self):
        file_string, result_dict = self._generate_test_case_3()

        file_name = "./test3.conf"
        f = open(file_name, "w")
        f.write(file_string)
        f.close()

        solvers = ["yices", "z3", "dreal"]
        yices_setting = dict()
        yices_setting["logic"] = "QF_NRA"

        solver_defaults = dict()
        solver_defaults["yices"] = yices_setting

        print_options = ["verbose", "debug", "normal"]
        encoding_list = ["model-with-goal-enhanced", "model-with-goal", "only-goal-stl",
                         "only-goal-stl-enhanced"]
        cv = ConfigVisitor(solvers, solver_defaults, encoding_list, print_options)
        conf_dict = cv.get_config_dict(file_name)

        if os.path.isfile(file_name):
            os.remove(file_name)

        self.assertEqual(conf_dict, result_dict, "parse wrong")

    def test_parsing_3(self):
        file_string, result_dict = self._generate_test_case_4()

        file_name = "./test4.conf"
        f = open(file_name, "w")
        f.write(file_string)
        f.close()

        solvers = ["yices", "z3", "dreal", "flowstar"]
        flowstar_setting = dict()

        solver_defaults = dict()
        solver_defaults["flowstar"] = flowstar_setting

        print_options = ["verbose", "debug", "normal"]
        encoding_list = ["model-with-goal-enhanced", "model-with-goal", "only-goal-stl",
                         "only-goal-stl-enhanced"]
        cv = ConfigVisitor(solvers, solver_defaults, encoding_list, print_options)
        conf_dict = cv.get_config_dict(file_name)

        if os.path.isfile(file_name):
            os.remove(file_name)

        self.assertEqual(conf_dict, result_dict, "parse wrong")
