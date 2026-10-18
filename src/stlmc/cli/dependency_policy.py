"""Managed solver targets and pinned native download information.

These are installation/check targets, not a claim that every other version is
incompatible. Runtime solver discovery remains independent of this policy.
The official dReal target has known correctness limitations. Its version/hash
identify the distribution, not a certificate of ODE correctness.
"""

Z3_VERSION = "4.15.4.0"
CVC5_VERSION = "1.3.4"
YICES_BINDING_VERSION = "1.1.6"
YICES_NATIVE_VERSION = "2.7.0"
DREAL_VERSION = "3.16.06.02"
# Official source snapshot containing the parameter-invariant fix. These pins
# identify build inputs, not a claim that every host/toolchain is validated.
DREAL_SOURCE_VERSION = "3.16.12"
DREAL_SOURCE_COMMIT = "6fa469fb1f8485b695b00edc69aa9e9a35e7ba97"
DREAL_SOURCE_URL = "https://codeload.github.com/dreal/dreal3/tar.gz/" + DREAL_SOURCE_COMMIT
DREAL_SOURCE_SHA256 = "281eb506f72de7bab6b6c969db84aaec2757eda09034d4cad4480756c82a7221"
DREAL_KNOWN_LIMITATIONS_WARNING = (
    "Warning: official dReal 3.16.06.02 has known correctness limitations: "
    "zero-derivative parameter invariants may be ignored and ODE witnesses "
    "may be incorrect (upstream issue #325). Execution is allowed with these "
    "limitations; successful installation or checks do not certify ODE correctness."
)

Z3_PACKAGE = "z3-solver==" + Z3_VERSION
CVC5_PACKAGE = "cvc5==" + CVC5_VERSION
YICES_PACKAGE = "yices==" + YICES_BINDING_VERSION
YICES_SOURCE_URL = "https://github.com/SRI-CSL/yices2/archive/refs/tags/yices-{}.tar.gz".format(YICES_NATIVE_VERSION)
YICES_SOURCE_SHA256 = "584db72abf6643927b2c3ba98ff793f602216b452b8ff2f34a8851d35904804a"

# Do not invent "validated" pins for interpreters not exercised by the tests.
# More profiles can be added after the same installer and renderer smoke tests.
VISUALIZE_PROFILES = {
    (3, 10): {"numpy": "numpy==2.2.6", "scipy": "scipy==1.15.3",
              "bokeh": "bokeh==3.1.1", "matplotlib": "matplotlib==3.10.8"},
}


def visualization_packages(python_version):
    key = tuple(python_version[:2])
    if key not in VISUALIZE_PROFILES:
        raise RuntimeError(
            "No validated visualization installation profile for Python {}.{}. "
            "Use Python 3.10 for the managed visualization installer; "
            "model-checking Python support is independent of this profile.".format(*key))
    return dict(VISUALIZE_PROFILES[key])

# SHA256 of the fixed official GitHub release assets fetched on 2026-10-18:
# https://github.com/dreal/dreal3/releases/tag/v3.16.06.02
# These are locally recorded content pins, NOT upstream-published checksums or
# signature verification. They prevent subsequent downloads silently changing.
DREAL_ARCHIVE_SHA256 = {
    "dReal-3.16.06.02-linux.tar.gz": "375bafaafb50096cefe93b6f33a62b2e189a3b86fff3638f86e265fb5a57e327",
    "dReal-3.16.06.02-darwin.zip": "7a878e6aa1223f10f077e20221f38d63a7ba6d4503f8c612fdfbd2a3157b5bc6",
}
