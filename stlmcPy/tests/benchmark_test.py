import unittest

from stlmcPy.driver.driver import Driver


class BenchmarkTestCase(unittest.TestCase):

    def test_linear_railroad(self):
        driver = Driver()
        results = driver.run(["./stlmcPy/tests/benchmark_models/linear/railroadLinear.model"])

        self.assertEqual(repr(results), '[FalseResult, TrueResult, FalseResult, TrueResult]',
                         'incorrect solving results')

    def test_linear_simple(self):
        driver = Driver()
        results = driver.run(["./stlmcPy/tests/benchmark_models/linear/simple.model"])

        self.assertEqual(repr(results), '[FalseResult]',
                         'incorrect solving results')

    def test_linear_battery(self):
        driver = Driver()
        results = driver.run(["./stlmcPy/tests/benchmark_models/linear/twoBatteryLinear.model"])

        self.assertEqual(repr(results), '[FalseResult, TrueResult, FalseResult, FalseResult]',
                         'incorrect solving results')

    def test_linear_car(self):
        driver = Driver()
        results = driver.run(["./stlmcPy/tests/benchmark_models/linear/twoCarLinear.model"])

        self.assertEqual(repr(results), '[FalseResult, TrueResult, TrueResult, FalseResult]',
                         'incorrect solving results')

    def test_linear_thermostat(self):
        driver = Driver()
        results = driver.run(["./stlmcPy/tests/benchmark_models/linear/twoThermostatLinear.model"])

        self.assertEqual(repr(results), '[FalseResult, FalseResult, FalseResult, TrueResult]',
                         'incorrect solving results')

    def test_linear_water(self):
        driver = Driver()
        results = driver.run(["./stlmcPy/tests/benchmark_models/linear/twoWatertankLinear.model"])

        self.assertEqual(repr(results), '[FalseResult, FalseResult, TrueResult, TrueResult]',
                         'incorrect solving results')