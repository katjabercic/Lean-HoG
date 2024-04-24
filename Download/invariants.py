import json
from typing import Dict, Union


class Invariant():

    id : int
    name : str
    fieldName : str
    value : Union[bool, int, float]
    
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
        if typeName == "b":
            self.value = bool(value)
        elif typeName == "i":
            self.value = int(value)
        else:
            self.value = value


class Invariants():
    """An object representing values of invariants for a graph"""

    invariant_values : Dict[int, Invariant] = {}

    def __init__(self, values, metadata) -> None:
        raw_invariant_values = Invariants._parse_invariants(values)
        for e in metadata["_embedded"]["invariantModelList"]:
            id = e["entity"]["invariantId"]
            value = raw_invariant_values[id]
            self.invariant_values[id] = Invariant(id, e["entity"]["invariantName"], e["entity"]["typeName"], value)

    @staticmethod
    def _parse_invariants(invariants_data) -> Dict[int, Union[bool, int, float]]:
        """Return dictionary mapping invariant ID to the corresponding invariant value for this graph."""
        raw_invariant_values : Dict[int, Union[bool, int, float]] = {}
        for x in invariants_data["_embedded"]["graphInvariantModelList"]:
            raw_invariant_values[x["entity"]["invariantId"]] = x["entity"]["invariantValue"]
        return raw_invariant_values
    
    def to_json(self):
        return { e.fieldName: e.value for e in self.invariant_values.values() }
                

