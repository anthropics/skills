import sys, importlib.abc
class Hook(importlib.abc.MetaPathFinder): pass
sys.meta_path.insert(0, Hook())
