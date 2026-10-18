import argparse
import sys
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "src"))

from stlmc.constraints.operations import substitution
from stlmc.artifacts.codec import load_artifact
from stlmc.solver.dreal import DrealInterval
from stlmc.visualize.visualizer import Visualizer


def discover_artifacts(paths):
    artifacts = []
    for raw_path in paths:
        path = Path(raw_path)
        if path.is_dir():
            artifacts.extend(path.rglob("*.counterexample"))
        elif path.name.endswith(".counterexample"):
            artifacts.append(path)
        else:
            raise ValueError("not a counterexample artifact: {}".format(path))
    return sorted(set(artifacts))


def validate_counterexample(path, tolerance):
    data = load_artifact(path)

    assignment = data[0]
    interval_count = 0
    for value in assignment.values():
        if isinstance(value, DrealInterval):
            interval_count += 1
            midpoint = float(value.midpoint)
            if not float(value.lower) <= midpoint <= float(value.upper):
                raise ValueError("dReal midpoint lies outside its interval")

    visualizer = Visualizer()
    _, robustness_values, _, _, _, epsilon = visualizer.generate_data(*data[:9])
    expanded_formula = substitution(data[6], data[5])
    rho_zero = robustness_values[expanded_formula][0][0]
    valid = rho_zero <= float(epsilon) + tolerance
    return valid, rho_zero, float(epsilon), interval_count


def main():
    parser = argparse.ArgumentParser(
        description=(
            "Numerically reconstruct counterexample trajectories and check "
            "the robust STL condition rho(phi, 0) <= epsilon."
        )
    )
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--tolerance", type=float, default=1e-7)
    args = parser.parse_args()

    artifacts = discover_artifacts(args.paths)
    if not artifacts:
        raise SystemExit("no counterexample artifacts found")
    failures = 0
    for artifact in artifacts:
        try:
            valid, rho_zero, epsilon, interval_count = (
                validate_counterexample(artifact, args.tolerance)
            )
            outcome = "PASS" if valid else "FAIL"
            failures += 0 if valid else 1
            print(
                "{} {} rho0={} epsilon={} dreal_intervals={}".format(
                    outcome, artifact, rho_zero, epsilon, interval_count
                )
            )
        except Exception as error:
            failures += 1
            print("ERROR {}: {}".format(artifact, error))
    if failures:
        raise SystemExit("{} artifact validation(s) failed".format(failures))
    print(
        "All artifacts passed numerical reconstruction; this supplements, "
        "but does not replace, an SMT/delta-SAT certificate."
    )


if __name__ == "__main__":
    main()
