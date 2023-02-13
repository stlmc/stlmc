import os
import subprocess
from typing import Optional

from .converter import Converter
from .spaceex import _make_model, _make_conf
from ..hybrid_automaton import *
from ..utils import get_ha_vars
from ...constraints.constraints import *
from ...objects.configuration import Configuration


class DreachConverter(Converter):
    def __init__(self, config: Configuration):
        self._model_string = ""
        self._config_string = ""
        self._config: Configuration = config
        self._names: Optional[Tuple[str, str]] = None

    def convert(self, ha: HybridAutomaton):
        self._reset()
        self._preprocessing_hyst(ha)

        # use spaceex converter
        self._model_string = _make_model(ha)
        self._config_string = _make_conf(ha, self._config)

        # generate intermediate files
        self._names = self._write_tmp()

    def _write_tmp(self) -> Tuple[str, str] :
        common_section = self._config.get_section("common")
        g_n, b = common_section.get_value("goal"), common_section.get_value("bound")

        m_n = "tmp$$_{}_b{}_se.xml".format(g_n, b)
        c_n = "tmp$$_{}_b{}_se.cfg".format(g_n, b)

        f = open(m_n, "w")
        f.write(self._model_string)
        f.close()

        f = open(c_n, "w")
        f.write(self._config_string)
        f.close()
        # print("write tmp hybrid automaton to {} and {}".format(m_n, c_n))
        return m_n, c_n

    def write(self, file_name: str):
        assert self._names is not None
        m_n, c_n = self._names[0], self._names[1]

        common_section = self._config.get_section("common")
        g_n, b = common_section.get_value("goal"), common_section.get_value("bound")

        o_n = "{}_{}_b{}_dreach.drh".format(file_name, g_n, b)

        # get hycomp converter binary
        dreach_section = self._config.get_section("dreach")
        hyst_path = dreach_section.get_value("converter-path")
        hycomp_jar = "{}/Hyst.jar".format(hyst_path)

        proc = subprocess.Popen(
            ["java", "-jar", hycomp_jar, "-input", m_n,
             "-t", "dreach", "\"\"", "-o", o_n],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)

        stdout, stderr = proc.communicate()

        self._remove_tmp()

        if stdout:
            print(f'\n{stdout.decode()}')

        if stderr:
            print()
            print("error occurred during hycomp converting")
            print(f'{stderr.decode()}')
        else:
            print("write hybrid automaton to {}".format(o_n))

    def _reset(self):
        self._model_string = ""
        self._config_string = ""
        self._names = None

    def _remove_tmp(self):
        if self._names is not None:
            m_n, c_n = self._names[0], self._names[1]
            if os.path.isfile(m_n):
                os.remove(m_n)

            if os.path.isfile(c_n):
                os.remove(c_n)

    @classmethod
    def _preprocessing_hyst(cls, ha: HybridAutomaton):
        zero, one, delta = RealVal("0.0"), RealVal("1.0"), RealVal("0.001")
        g_clk = Real("gClk")

        # get initial and final modes
        init, final = set(), set()
        for mode in ha.get_modes():
            if mode.is_initial():
                init.add(mode)

            if mode.is_final():
                final.add(mode)

        # make new initial and final mode
        init_m = Mode(100001)
        init_m.set_as_initial()
        init_m.add_invariant(g_clk <= delta)

        final_m = Mode(100002)
        final_m.set_as_final()

        v_s = get_ha_vars(ha)
        for v in v_s:
            if v.id == g_clk.id:
                init_m.add_dynamic((v, one))
            else:
                init_m.add_dynamic((v, zero))

        for v in v_s:
            final_m.add_dynamic((v, zero))

        ha.add_mode(init_m)
        ha.add_mode(final_m)

        for m in init:
            m.set_as_non_initial()
            tr = Transition(init_m, m)
            tr.add_guard(g_clk >= zero)
            ha.add_transition(tr)

        for m in final:
            m.set_as_non_final()
            tr = Transition(m, final_m)
            ha.add_transition(tr)
