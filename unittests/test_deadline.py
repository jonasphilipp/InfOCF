from inference.deadline import Deadline
import inference.deadline as deadline_mod


def test_deadline_from_duration_negative_is_immediately_expired(monkeypatch):
    # freeze perf_counter
    monkeypatch.setattr(deadline_mod, "perf_counter", lambda: 100.0)

    d = Deadline.from_duration(-5.0)
    assert d.expired() is True
    assert d.remaining_seconds() == 0.0
    assert d.remaining_ms() == 0


def test_deadline_remaining_ms_rounds_down(monkeypatch):
    # perf_counter now=10.0; deadline end=10.999 -> remaining_seconds=0.999 -> ms=999
    monkeypatch.setattr(deadline_mod, "perf_counter", lambda: 10.0)
    d = Deadline(end=10.999)
    assert d.remaining_ms() == 999


def test_deadline_sub_clamps_to_remaining(monkeypatch):
    # end=20.0, now=10.0 => remaining=10s
    monkeypatch.setattr(deadline_mod, "perf_counter", lambda: 10.0)
    d = Deadline(end=20.0)

    # sub(999) should clamp to remaining (10s)
    d2 = d.sub(999.0)
    # with perf_counter fixed, remaining should be ~10s (not more)
    assert d2.remaining_seconds() <= 10.0
