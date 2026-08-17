from dataclasses import dataclass
from typing import List, Optional, Tuple

from ..constraints.constraints import And, BoolVal, Formula
from ..objects.model import Model, StlMC


@dataclass(frozen=True)
class TransitionChoice:
    source: int
    jump_index: int
    target: int


@dataclass(frozen=True)
class PathCandidate:
    index: int
    transitions: Tuple[TransitionChoice, ...]
    constraint: Formula


class PathProvider:
    name = "symbolic"

    def candidates(self, model: Model, bound: int) -> List[PathCandidate]:
        raise NotImplementedError


class SymbolicPathProvider(PathProvider):
    name = "symbolic"

    def candidates(self, model: Model, bound: int) -> List[PathCandidate]:
        return [PathCandidate(0, tuple(), BoolVal("True"))]


class ExplicitPathProvider(PathProvider):
    """Enumerate exact transition paths, including STL steady transitions."""

    name = "explicit"

    @staticmethod
    def _outgoing(model: StlMC, source: int) -> List[TransitionChoice]:
        module = model.modules[source]
        result = []
        for jump_index, guard in enumerate(module["jump"]):
            target = module["jp_d"].get(guard)
            targets = (
                [target]
                if target is not None
                else range(len(model.modules))
            )
            result.extend(
                TransitionChoice(source, jump_index, candidate_target)
                for candidate_target in targets
            )

        # Normal STL encoding permits a steady transition at a variable point.
        # Reachability encoding intentionally omits it.
        if not model.is_gen_reach_condition():
            result.append(TransitionChoice(source, len(module["jump"]), source))
        return result

    def _enumerate(self, model: StlMC, bound: int):
        initial_modes = (
            [model.init_mode]
            if model.init_mode is not None
            else list(range(len(model.modules)))
        )
        paths = [(mode, tuple()) for mode in initial_modes]
        for _ in range(bound):
            next_paths = []
            for mode, transitions in paths:
                for transition in self._outgoing(model, mode):
                    next_paths.append((
                        transition.target,
                        transitions + (transition,),
                    ))
            paths = next_paths
        return paths

    @staticmethod
    def _constraint(model: StlMC, final_mode: int,
                    transitions: Tuple[TransitionChoice, ...]) -> Formula:
        children = []
        mode = transitions[0].source if transitions else final_mode
        for depth, transition in enumerate(transitions):
            mode_consts, _ = model.make_mode_consts(depth)
            children.append(mode_consts[mode])

            _, jump_tracks = model.make_jump_consts(depth)
            jump_id = "m_{}@jump^{}_{}".format(
                transition.source, transition.jump_index, depth
            )
            selected = next(
                constraint for variable, constraint in jump_tracks.items()
                if variable.id == jump_id
            )
            children.append(selected)
            mode = transition.target

        final_mode_consts, _ = model.make_mode_consts(len(transitions))
        children.append(final_mode_consts[final_mode])
        return And(children)

    def candidates(self, model: Model, bound: int) -> List[PathCandidate]:
        if not isinstance(model, StlMC):
            raise TypeError("explicit paths require an StlMC hybrid model")
        return [
            PathCandidate(index, transitions,
                          self._constraint(model, final_mode, transitions))
            for index, (final_mode, transitions) in enumerate(
                self._enumerate(model, bound)
            )
        ]


def make_path_provider(name: Optional[str]) -> PathProvider:
    if name in (None, "symbolic"):
        return SymbolicPathProvider()
    if name == "explicit":
        return ExplicitPathProvider()
    raise ValueError("unknown path strategy: {}".format(name))
