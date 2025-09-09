from dataclasses import dataclass
from time import perf_counter


@dataclass(frozen=True)
class Deadline:
    """
    Per-run time budget helper.

    Construct with a duration in seconds using from_duration().
    Use remaining_ms() when passing timeouts to solvers and expired() for early exits.
    """

    end: float  # absolute timestamp based on perf_counter()

    @staticmethod
    def from_duration(seconds: float) -> "Deadline":
        return Deadline(perf_counter() + max(0.0, seconds))

    def remaining_seconds(self) -> float:
        return max(0.0, self.end - perf_counter())

    def remaining_ms(self) -> int:
        return int(self.remaining_seconds() * 1000)

    def expired(self) -> bool:
        return self.remaining_seconds() <= 0.0

    def sub(self, seconds: float) -> "Deadline":
        return Deadline.from_duration(min(seconds, self.remaining_seconds()))
