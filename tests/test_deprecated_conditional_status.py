import subprocess
import sys

def test_deprecated_conditional_status_guard_passes():
    subprocess.run(
        [sys.executable, "scripts/check_deprecated_conditional_status.py"],
        check=True,
    )
