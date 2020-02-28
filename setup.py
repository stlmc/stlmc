import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="stlmc",  # Replace with your own username
    version="0.1.0.dev4",
    include_package_data=True,
    scripts=['./stlmc', './stlmc-server'],
    author="Geunyeol Yu",
    author_email="rgyen@postech.ac.kr",
    description="A small example package",
    install_requires=[
        "z3-solver",
        "yices>=1.1.0",
        "scipy",
        "numpy",
        "antlr4-python3-runtime>=4.7.2,<4.8.1"],
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/stlmc/stlmc",
    packages=setuptools.find_packages(),
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',
)
