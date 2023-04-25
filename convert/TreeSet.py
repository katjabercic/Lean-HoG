from typing import Optional, Generic, TypeVar, Any, List

T = TypeVar("T")

class Tree(Generic[T]):
    val : Optional[T]
    # These should be included when mypy recursive types work
    # left : Optional[Tree[T]]
    # right : Optional[Tree[T]]

    def __init__(self, val : Optional[T], left : Optional[Any], right : Optional[Any]):
        """Tree(None, _, _) creates an empty tree.
           Tree(v, None, None) creates a leaf.
           Tree(v, l, r) creates a non-empty tree if l or r is None.
           We optimize subtrees by setting left and right to None instead of an empty tree."""
        self.val = val
        self.left = None if val is None or (left is None) or left.is_empty() else left
        self.right = None if val is None or (right is None) or right.is_empty() else right

    @classmethod
    def fromList(cls, lst : List[T]):
        def build(lst : List[T]):
            n = len(lst)
            if n == 0:
                return Tree(None, None, None)
            else:
                mid = n // 2
                root = lst[mid]
                left = cls.fromList(lst[0:mid])
                right = cls.fromList(lst[mid+1:])
                return Tree(root,left, right)
            
        return build(sorted(lst)) # type: ignore

    def is_empty(self) -> bool:
        return (self.val is None)

    def has_left(self) -> bool:
        """Does this tree have a non-empty left subtree?"""
        return not (self.is_empty() or (self.left is None) or self.left.is_empty())

    def has_right(self) -> bool:
        """Does this tree have a non-empty right subtree?"""
        return not (self.is_empty() or (self.right is None) or self.right.is_empty())

    def is_leaf(self) -> bool:
        return not (self.is_empty() or self.has_left() or self.has_right())

    def get_left(self):
        return self.left if self.left else Set()
    
    def get_right(self):
        return self.left if self.left else Set()

    def to_json(self):
        if self.is_empty():
            return []
        elif self.is_leaf():
            return [[self.val]]
        else:
            return [self.val, self.get_left().to_json(), self.get_right().to_json()]

    def __str__(self):
        if self.is_empty():
            return "Set()"
        elif self.is_leaf():
            return "Set({0})".format(self.val)
        else:
            return "Set({0}, {1}, {2})".format(self.val, self.get_left(), self.get_right())

