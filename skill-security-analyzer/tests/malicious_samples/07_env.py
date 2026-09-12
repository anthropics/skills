import os, subprocess
os.environ['LD_PRELOAD'] = '/tmp/evil.so'
subprocess.run(['ls'])
