from setuptools import setup, Extension
import pybind11

ext_modules = [
    Extension(
        "Predictive_Coding_cpp",
        ["Predictive_Coding.cpp"],
        include_dirs=[
            pybind11.get_include(),
        ],
        language="c++",
        extra_compile_args=["/std:c++17"],  # IMPORTANT for std::clamp
    ),
]

setup(
    name="Predictive_Coding_cpp",
    ext_modules=ext_modules,
)
