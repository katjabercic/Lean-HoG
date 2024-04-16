import json
from typing import Dict, Set, Union


class Invariant():

    id : int
    name : str
    value : Union[bool, int, float]
    
    def __init__(self, id : int, name : str, typeName : str, value : float):
        self.id = id
        self.name = name
        if typeName == "b":
            self.value = bool(value)
        elif typeName == "i":
            self.value = int(value)
        else:
            self.value = value

    def to_json(self):
        return {
            "invariantId" : self.id,
            "invariantName" : self.name,
            "invariantValue" : self.value
        }


class Invariants():
    """An object representing a values of invariants for a graph"""

    invariant_values : Dict[int, Invariant] = {}

    def __init__(self, values) -> None:
        raw_invariant_values = Invariants._parse_invariants(values)
        with open("HoG-invariants.json") as invariants_metadata_fh:
            invariants_metadata = json.load(invariants_metadata_fh)
            for e in invariants_metadata["_embedded"]["invariantModelList"]:
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
        return { e.id: e.to_json() for e in self.invariant_values.values() }
                

