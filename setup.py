import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="example-pkg-rgyenr2", # Replace with your own username
    version="0.0.6a18.post10",
    include_package_data=True,
    scripts=['./stlmc', './stlmc-server'],
    author="Example Author",
    author_email="author@example.com",
    description="A small example package",
    # install_requires=[
    #     "z3-solver>=4.8.0.0.post1",
    #     "yices>=1.1.0",
    #     "scipy",
    #     "numpy",
    #     "antlr4-python3-runtime>=4.7.2,<4.8.1"],
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/pypa/sampleproject",
    packages=setuptools.find_packages(),
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',
)
