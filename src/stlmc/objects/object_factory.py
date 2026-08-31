"""Compatibility facade for :mod:`stlmc.application.model_loader`."""

from ..application.model_loader import (
    NewStlObjectManager, ObjectFactory, ObjectManager, OldObjectManager,
    OldStlObjectManager, build_goals,
)

__all__ = [
    "NewStlObjectManager", "ObjectFactory", "ObjectManager",
    "OldObjectManager", "OldStlObjectManager", "build_goals",
]
