"""Bokeh is an optional HTML renderer, never an artifact/text/PDF prerequisite."""
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parent.parent
BLOCK_BOKEH = """
import importlib.abc, sys
class NoBokeh(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname == 'bokeh' or fullname.startswith('bokeh.'):
            raise ModuleNotFoundError('Bokeh deliberately unavailable', name=fullname)
sys.meta_path.insert(0, NoBokeh())
"""
ARTIFACT = """
from stlmc.artifacts.codec import dump_artifact
from pathlib import Path
from stlmc.parser.model_visitor import ModelVisitor
from stlmc.constraints.constraints import Real, RealVal
source = 'real unused; [0, 5] x; { mode: true; inv: x >= 0; flow: x(t) = x(0) + t; jump: } init: x = 0; proposition: goal: [f1]: x >= 2;'
Path('simple.model').write_text(source)
model, props, goals, labels = ModelVisitor().get_parse_tree('simple.model')
assignment = {Real(k): RealVal(v) for k,v in dict(currentMode_0='0',tau_0='0',tau_1='1',x_0_0='0',x_0_t='1').items()}
artifact = Path('simple.counterexample')
dump_artifact(artifact,(assignment,model.modules,model.mode_var_dict,model.prop_dict,model.range_dict,props,goals[0][0],'f1',0.0,model.init,model.const_dict))
Path('simple.cfg').write_text('{\\noutput = html\\ngroup {\\n}\\n}\\n')
"""


class OptionalBokehTest(unittest.TestCase):
    def run_without_bokeh(self, script):
        environment = dict(os.environ, PYTHONPATH=str(ROOT / "src"),
                           STLMC_DISABLE_UPDATE_CHECK="1", OPENBLAS_NUM_THREADS="1")
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run([sys.executable, "-c", BLOCK_BOKEH + textwrap.dedent(script)],
                                    cwd=directory, env=environment, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        return result

    def test_facade_and_plot_module_import_without_bokeh(self):
        self.run_without_bokeh("""
            from stlmc.visualize.visualizer import Visualizer
            from stlmc.visualize.plotting import build_plot
            assert not any(x == 'bokeh' or x.startswith('bokeh.') for x in sys.modules)
        """)

    def test_text_output_without_bokeh(self):
        self.run_without_bokeh(ARTIFACT + """
from stlmc.cli.visualize import main
sys.argv=['stlmc-vis',str(artifact),'-output','text']
assert main() is None
assert Path(str(artifact)+'.txt').is_file()
assert 'bokeh' not in sys.modules
""")

    @unittest.skipUnless(importlib.util.find_spec("matplotlib"), "optional Matplotlib PDF renderer not installed")
    def test_pdf_sampling_and_rendering_without_bokeh(self):
        self.run_without_bokeh(ARTIFACT + """
class NoSolver(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname.split('.')[0] in {'z3','yices','cvc5'}:
            raise ModuleNotFoundError('solver deliberately unavailable', name=fullname)
sys.meta_path.insert(0, NoSolver())
from stlmc.cli.visualize import main
sys.argv=['stlmc-vis',str(artifact),'-cfg','simple.cfg','-output','pdf']
assert main() is None
pdfs = list(Path('.').glob('*.pdf'))
assert len(pdfs) >= 2
assert all(path.read_bytes().startswith(b'%PDF-') for path in pdfs)
assert not list(Path('.').glob('*.gnu'))
assert 'bokeh' not in sys.modules
assert not any(name.split('.')[0] in {'z3','yices','cvc5'} for name in sys.modules)
""")

    @unittest.skipUnless(importlib.util.find_spec("matplotlib"), "optional Matplotlib PDF renderer not installed")
    def test_pdf_groups_discontinuities_and_threshold_without_bokeh(self):
        self.run_without_bokeh("""
from pathlib import Path
from unittest.mock import patch
from matplotlib.backends.backend_pdf import FigureCanvasPdf
from stlmc.constraints.constraints import Real
from stlmc.visualize.pdf import write_pdf
x, y = Real('x'), Real('y')
seen = []
original = FigureCanvasPdf.print_pdf
def inspect(canvas, filename):
    axes = canvas.figure.axes[0]
    seen.append((filename, [(list(line.get_xdata()),list(line.get_ydata())) for line in axes.lines]))
    return original(canvas, filename)
with patch.object(FigureCanvasPdf, 'print_pdf', inspect):
    files = write_pdf('trace', {0:{'x'},1:{'f_0'}}, {'phi':0},
                     {x:[[0,1],[5,6]], y:[[2,3],[4,5]]},
                     {'phi':[[1,2],[-2,-1]]}, [[0,1],[1,2]], .25, 'f')
assert set(files) == {'state_x.pdf','state_y.pdf','rob_f_0.pdf'}
state = dict(seen)['state_x.pdf']
assert state == [([0,1],[0,1]),([1,2],[5,6])], state
rob = dict(seen)['rob_f_0.pdf']
assert rob[-2][1] == [0,0] and rob[-1][1] == [.25,.25], rob
assert all(Path(path).read_bytes().startswith(b'%PDF-') for path in files)
assert 'bokeh' not in sys.modules
""")

    def test_html_has_actionable_failure_before_sampling(self):
        result = self.run_without_bokeh(ARTIFACT + """
from unittest.mock import patch
from stlmc.cli.visualize import main
sys.argv=['stlmc-vis',str(artifact),'-cfg','simple.cfg','-output','html']
with patch('stlmc.visualize.visualizer.Visualizer.generate_data',side_effect=AssertionError('sampled before checking Bokeh')):
    assert main() == 2
""")
        self.assertIn("HTML visualization requires Bokeh", result.stdout)
        self.assertIn("stlmc-installer install --visualize html", result.stdout)

    @unittest.skipUnless(importlib.util.find_spec("z3"), "optional Z3 solver not installed")
    def test_model_checking_writes_artifacts_without_bokeh(self):
        self.run_without_bokeh("""
from pathlib import Path
from stlmc.cli.mc import main
Path('simple.model').write_text('[0,5] x; {mode:true; inv:x>=0; flow:x(t)=x(0)+t; jump:} init:x=0; proposition: goal:[f1]:x>=2;')
sys.argv=['stlmc','simple.model','-solver','z3','-bound','0','-time-bound','1','-threshold','0','-goal','f1','-visualize']
assert main() == 0
assert len(list(Path('.').glob('*.counterexample'))) == 1
assert 'bokeh' not in sys.modules
""")


if __name__ == "__main__":
    unittest.main()
