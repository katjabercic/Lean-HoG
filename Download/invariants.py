import json
import math
from typing import Dict, Optional, Union

# Values HoG uses for "there is no finite value here". It is not consistent about
# which one it picks: a disconnected graph can come back with diameter
# "Infinity" but radius null, and an acyclic one with girth null rather than
# "Infinity", so both spellings have to be handled for the same situation.
NO_VALUE_STRINGS = ("Infinity", "-Infinity", "NaN")


def coerceValue(typeName : str, value) -> Optional[Union[bool, int, float]]:
    """
    Convert a raw HoG invariant value to the type its metadata declares.

    Returns None when HoG has no usable value, which callers should read as
    "invariant absent" rather than as an error: around half the graphs in HoG
    have at least one, so treating it as an error means most of the database
    cannot be downloaded at all.
    """
    if value is None:
        return None
    if isinstance(value, str) and value in NO_VALUE_STRINGS:
        return None
    if isinstance(value, float) and not math.isfinite(value):
        return None
    if typeName == "b":
        return bool(value)
    if typeName == "i":
        return int(value)
    return value


class Invariant():

    id : int
    name : str
    fieldName : str
    # None when HoG has no finite value for this invariant on this graph.
    value : Optional[Union[bool, int, float]]

    def _setFieldName(self):
        """Convert invariant names"""
        s = self.name.title()
        s = s.replace(' ', '')
        s = s.replace('-', '')
        # s is not empty
        self.fieldName = s[0].lower() + s[1:] # the first letter should not be capitalized

    def __init__(self, id : int, name : str, typeName : str, value : float):
        self.id = id
        self.name = name
        self._setFieldName()
        self.value = coerceValue(typeName, value)


class Invariants():
    """An object representing values of invariants for a graph"""

    invariant_values : Dict[int, Invariant]

    def __init__(self, values, metadata) -> None:
        # Per instance, deliberately. As a class attribute with a `= {}` default
        # this dict was shared by every Invariants ever built, so downloading
        # several graphs in one process wrote each graph's invariants into the
        # next graph's JSON. Harmless while downloadGraph.py was one graph per
        # process; silent data corruption for anything that batches.
        self.invariant_values = {}
        raw_invariant_values = Invariants._parse_invariants(values)
        for e in metadata["_embedded"]["invariantModelList"]:
            id = e["entity"]["invariantId"]
            # `.get`: HoG may omit an invariant from a graph's list entirely,
            # which is the same situation as an explicit null.
            invariant = Invariant(id, e["entity"]["invariantName"], e["entity"]["typeName"],
                                  raw_invariant_values.get(id))
            # Absent invariants are left out of the JSON rather than written as
            # null. Every field of `RawHoGData` is an `Option`, and Lean's
            # derived `FromJson` reads a missing field as `none`.
            if invariant.value is not None:
                self.invariant_values[id] = invariant

    @staticmethod
    def _parse_invariants(invariants_data) -> Dict[int, Union[bool, int, float]]:
        """Return dictionary mapping invariant ID to the corresponding invariant value for this graph."""
        raw_invariant_values : Dict[int, Union[bool, int, float]] = {}
        for x in invariants_data["_embedded"]["graphInvariantModelList"]:
            raw_invariant_values[x["entity"]["invariantId"]] = x["entity"]["invariantValue"]
        return raw_invariant_values
    
    def to_json(self):
        return { e.fieldName: e.value for e in self.invariant_values.values() }
                

