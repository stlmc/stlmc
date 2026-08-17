from ..objects.algorithm import Algorithm


class ModelCheckingAlgorithm(Algorithm):
    """Compose discrete path exploration with a continuous solving engine."""

    def __init__(self, path_provider, continuous_solving):
        self.path_provider = path_provider
        self.continuous_solving = continuous_solving

    @property
    def runner(self):
        return getattr(self.continuous_solving, "runner", None)

    def set_debug(self, msg: str):
        self.continuous_solving.set_debug(msg)

    def run(self, model, goal, prop_dict, config, solver, logger, printer):
        return self.continuous_solving.run(
            model, goal, prop_dict, config, solver, logger, printer
        )
