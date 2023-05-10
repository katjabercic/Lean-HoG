from typing import Dict, List, Any, Optional

class TreeMap():
    """A map (dictionary) represented as a binary search tree."""

    def __init__(self, key=None, val=None, left=None, right=None):
        if key is None:
            # empty map
            self.key = None
            self.val = None
            self.left = None
            self.right = None
        else:
            self.key = key
            self.val = val
            self.left = left
            self.right = right

    @staticmethod
    def from_dict(d : Dict):
        def build(lst : List):
            n : int = len(lst)
            if n == 0:
                return TreeMap()
            else:
                mid = n // 2
                (key, val) = lst[mid]
                left = build(lst[0:mid])
                right = build(lst[mid+1:])
                return TreeMap(key=key, val=val, left=left, right=right)

        return build(sorted(list(d.items()))) # type: ignore

    def is_empty(self) -> bool:
        return (self.key is None)

    def is_leaf(self) -> bool:
        return ((self.key is not None) and
                (self.left is None or self.left.is_empty()) and
                (self.right is None or self.right.is_empty()))

    def get_left(self):
        return self.left if self.left else TreeMap()

    def get_right(self):
        return self.right if self.right else TreeMap()

    def __str__(self):
        if self.is_empty():
            return "Map()"
        elif self.is_leaf():
            return "Map({0},{1})".format(self.key, self.val)
        else:
            return f"Map({self.key},{self.val},{self.left},{self.right})"

    def to_json(self):
        """The map in JSON format."""
        if self.is_empty():
            return []
        elif self.is_leaf():
            return [self.key, self.val]
        else:
            return [self.key, self.val, self.get_left().to_json(), self.get_right().to_json()]

class Map():
    emptyDomain : bool # is this a map on an empty domain?
    defaultValue : Any # if the codomain is not empty, this holds a default value
    tree : TreeMap  # the underlying tree

    def __init__(self, emptyDomain : bool, defaultValue : Optional[Any] = None, tree : TreeMap = TreeMap()):
        self.emptyDomain = emptyDomain
        if self.emptyDomain:
            self.defaultValue = None
            self.tree = TreeMap()
        else:
           self.defaultValue = defaultValue
           self.tree = tree

    def to_json(self):
        """The map in JSON format."""
        if self.emptyDomain:
            return []
        else:
            return [self.tree, self.defaultValue]
