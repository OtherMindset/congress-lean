"""Build one module with `lake build <Module>` and print: module, seconds, peak RSS (MB), exit code.
Run once per module, in import order, so the module's imports are already built; peak memory is read
from getrusage(RUSAGE_CHILDREN) of this process after the build ends."""
import resource, subprocess, sys, time
m = sys.argv[1]
t = time.time()
r = subprocess.run(["lake", "build", m], capture_output=True, text=True)
dt = time.time() - t
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024
sys.stdout.write(f"{m},{dt:.1f},{rss:.0f},{r.returncode}\n")
if r.returncode:
    sys.stderr.write(r.stdout[-6000:] + r.stderr[-3000:])
sys.exit(r.returncode)
