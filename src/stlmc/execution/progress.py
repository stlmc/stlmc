"""Progress accounting independent of solver scheduling."""

from dataclasses import dataclass


@dataclass
class ProgressTracker:
    generated_scenarios: int = 0
    submitted_scenarios: int = 0
    completed_scenarios: int = 0
    submitted_jobs: int = 0
    completed_jobs: int = 0

    def reset(self):
        self.generated_scenarios = 0
        self.submitted_scenarios = 0
        self.completed_scenarios = 0
        self.submitted_jobs = 0
        self.completed_jobs = 0

    def scenario_generated(self, count=1):
        self.generated_scenarios += count

    def job_submitted(self, scenario_count=1):
        self.submitted_jobs += 1
        self.submitted_scenarios += scenario_count

    def job_completed(self, scenario_count=1):
        self.completed_jobs += 1
        self.completed_scenarios += scenario_count

    def snapshot(self, active_workers=0):
        return {
            "generated": self.generated_scenarios,
            "submitted": self.submitted_scenarios,
            "completed": self.completed_scenarios,
            "pending": max(
                self.submitted_scenarios - self.completed_scenarios, 0
            ),
            "submitted_jobs": self.submitted_jobs,
            "completed_jobs": self.completed_jobs,
            "active_workers": active_workers,
        }
