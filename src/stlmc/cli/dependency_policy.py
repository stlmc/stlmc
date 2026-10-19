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

# Official upstream assets; locally recorded content pins, not signatures or
# upstream-published checksum attestations. "static-gmp" is not fully static.
YICES_BINARY_RELEASE_URL = "https://github.com/SRI-CSL/yices2/releases/download/yices-2.7.0/"
YICES_BINARY_MIN_MACOS = {"x86_64": (12, 0), "arm64": (15, 0)}
CUDD_VERSION = "3.0.0"
CUDD_RPM_URL = (
    "https://download.opensuse.org/distribution/leap/15.6/repo/oss/x86_64/"
    "libcudd-3_0_0-0-3.0.0-bp156.4.4.x86_64.rpm")
CUDD_RPM_SHA256 = "9bddec2fb86a467f4e8fa08c5e94a163559077d1c7f67e0800d36be6543e6647"
CUDD_LIBRARY_PATH = "usr/lib64/libcudd-3.0.0.so.0.0.0"
CUDD_LICENSE_PATH = "usr/share/licenses/libcudd-3_0_0-0/LICENSE"
CUDD_LIBRARY_SHA256 = "967cf46b342f8a46beca76659092e52c5f3acf6af57b08eee14b5f29fa5ef5ae"
YICES_BINARY_ARCHIVES = {
    ("linux", "x86_64"): (
        "yices-2.7.0-x86_64-pc-linux-gnu-static-gmp.tar.gz",
        "49566b6f817692820538df78fe406878400d79810631c9372b2495bc81d3e00a"),
    ("darwin", "x86_64"): (
        "yices-2.7.0-x86_64-apple-darwin21.6.0-static-gmp.tar.gz",
        "dff40838ae5674abed2c08c383d702c1358ad64627c15799d2a15e67d1b4495a"),
    ("darwin", "arm64"): (
        "yices-2.7.0-arm-apple-darwin24.5.0-static-gmp.tar.gz",
        "5682fedf13add7818e8d05796b9133e67844fce2bb72fd1ecc75dcb73167c7ac"),
}

# Keep the numerical packages identical to the base-package requirements.
# Release CI exercises installation and rendering on each supported interpreter.
_VISUALIZE_PACKAGES = {
    "numpy": "numpy==2.3.5", "scipy": "scipy==1.16.3",
    "bokeh": "bokeh==3.8.2", "matplotlib": "matplotlib==3.10.8",
}
VISUALIZE_PROFILES = {
    (3, minor): dict(_VISUALIZE_PACKAGES) for minor in range(11, 15)
}


def visualization_packages(python_version):
    key = tuple(python_version[:2])
    if key not in VISUALIZE_PROFILES:
        raise RuntimeError(
            "No supported visualization installation profile for Python {}.{}. "
            "Use CPython 3.11 through 3.14.".format(*key))
    return dict(VISUALIZE_PROFILES[key])

# SHA256 of the fixed official GitHub release assets fetched on 2026-10-18:
# https://github.com/dreal/dreal3/releases/tag/v3.16.06.02
# These are locally recorded content pins, NOT upstream-published checksums or
# signature verification. They prevent subsequent downloads silently changing.
DREAL_ARCHIVE_SHA256 = {
    "dReal-3.16.06.02-linux.tar.gz": "375bafaafb50096cefe93b6f33a62b2e189a3b86fff3638f86e265fb5a57e327",
    "dReal-3.16.06.02-darwin.zip": "7a878e6aa1223f10f077e20221f38d63a7ba6d4503f8c612fdfbd2a3157b5bc6",
}
