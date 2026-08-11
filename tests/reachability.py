import os
import subprocess
import tempfile
import unittest
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
DREAL = Path(
    os.environ.get(
        "STLMC_DREAL",
        PROJECT_ROOT / "3rd_party" / "dReal3" / "dReal",
    )
)
STLMC = os.environ.get("STLMC", "stlmc")


MODEL = """\
bool active;
[0, 10] x;
{{
    mode: active = true;
    inv: (and (x >= 0) (x <= 10));
    flow: d/dt[x] = 1;
    jump: x >= 10 => (and (not active') (x' = 0));
}}
{{
    mode: active = false;
    inv: (and (x >= 0) (x <= 10));
    flow: d/dt[x] = 0;
    jump:
}}
init: (and active (x = 0));
proposition:
goal:
    {goal};
"""


class ReachabilityIntegrationTest(unittest.TestCase):
    def run_model(self, goal, *, threshold="0.01", two_step=False,
                  extra_args=(), visualize=False, solver="dreal", bound=0,
                  scenario_batch_size=1):
        with tempfile.TemporaryDirectory(prefix="stlmc-reach-") as directory:
            work = Path(directory)
            model = work / "reach.model"
            config = work / "reach.cfg"
            model.write_text(MODEL.format(goal=goal), encoding="utf-8")
            config.write_text(
                """\
common {{
    bound = {bound}
    time-bound = 10
    threshold = {threshold}
    solver = "{solver}"
    two-step = "{two_step}"
    parallel = "false"
    scenario-batch-size = {scenario_batch_size}
    visualize = "{visualize}"
    verbose = "false"
}}
dreal {{
    precision = 0.001
    ode-order = 20
    executable-path = "{dreal}"
}}
""".format(
                    threshold=threshold,
                    bound=bound,
                    two_step=str(two_step).lower(),
                    visualize=str(visualize).lower(),
                    solver=solver,
                    scenario_batch_size=scenario_batch_size,
                    dreal=DREAL,
                ),
                encoding="utf-8",
            )
            completed = subprocess.run(
                [STLMC, str(model), "-model-cfg", str(config), *extra_args],
                cwd=work,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=30,
            )
            artifacts = sorted(path.name for path in work.glob("reach_b0_*") )
            return completed, artifacts

    def test_reachable_at_zero_jump_bound(self):
        completed, _ = self.run_model(
            "reach (and (x >= 4) (x <= 6))"
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn("query       : reachability goal", completed.stdout)
        self.assertIn("status      : reachable at bound 0", completed.stdout)

    def test_unreachable_up_to_zero_jump_bound(self):
        completed, _ = self.run_model("reach (x >= 11)")
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn("status      : unreachable up to bound 0", completed.stdout)

    def test_search_stops_at_first_reachable_jump_bound(self):
        completed, _ = self.run_model(
            "reach (not active)", bound=2
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn("bound=0", completed.stdout)
        self.assertIn("bound=1", completed.stdout)
        self.assertNotIn("bound=2", completed.stdout)
        self.assertIn("status      : reachable at bound 1", completed.stdout)

    def test_threshold_relaxes_reach_target(self):
        completed, _ = self.run_model(
            "reach (x >= 10.5)", threshold="0.6"
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn("status      : reachable at bound 0", completed.stdout)

    def test_two_step_uses_same_reach_semantics(self):
        completed, _ = self.run_model(
            "reach (and (x >= 4) (x <= 6))", two_step=True
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn("algorithm   : two-step reachability", completed.stdout)
        self.assertIn("status      : reachable at bound 0", completed.stdout)
        self.assertIn("witness=scenario", completed.stdout)
        self.assertNotIn("counterexample=scenario", completed.stdout)

    def test_two_step_flushes_partial_scenario_batch(self):
        completed, _ = self.run_model(
            "reach (and (x >= 4) (x <= 6))",
            two_step=True,
            scenario_batch_size=8,
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn("status      : reachable at bound 0", completed.stdout)

    def test_supported_solvers_agree_on_reachable_target(self):
        for solver in ("z3", "yices", "dreal"):
            with self.subTest(solver=solver):
                completed, _ = self.run_model(
                    "reach (and (x >= 4) (x <= 6))", solver=solver
                )
                self.assertEqual(completed.returncode, 0, completed.stdout)
                self.assertIn(
                    "status      : reachable at bound 0", completed.stdout
                )

    def test_reach_option_rejects_temporal_goal(self):
        completed, _ = self.run_model(
            "<>[0, 1] (x >= 4)", extra_args=("-reach",)
        )
        self.assertEqual(completed.returncode, 2, completed.stdout)
        self.assertIn(
            "reachability requires a state formula without temporal operators",
            completed.stdout,
        )

    def test_reach_option_wraps_an_ordinary_state_goal(self):
        completed, _ = self.run_model("x >= 4", extra_args=("-reach",))
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn("status      : reachable at bound 0", completed.stdout)

    def test_reachable_query_writes_witness_artifact(self):
        completed, artifacts = self.run_model(
            "reach (and (x >= 4) (x <= 6))", visualize=True
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertTrue(
            any(name.endswith(".witness") for name in artifacts), artifacts
        )
        self.assertFalse(
            any(name.endswith(".counterexample") for name in artifacts),
            artifacts,
        )


if __name__ == "__main__":
    unittest.main()
