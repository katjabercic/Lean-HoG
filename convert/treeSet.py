from typing import Optional, Generic, TypeVar, Any, List, Set

T = TypeVar("T")

class Tree(Generic[T]):
    val : Optional[T]
    # These should be included when mypy recursive types work
    # left : Optional[Tree[T]]
    # right : Optional[Tree[T]]

    def __init__(self, val : Optional[T] = None, left: Optional[Any] = None , right : Optional[Any] = None):
        """Tree(None, _, _) creates an empty tree.
           Tree(v, None, None) creates a leaf.
           Tree(v, l, r) creates a non-empty tree if l or r is None.
           We optimize subtrees by setting left and right to None instead of an empty tree."""
        if val is None:
            self.val = None
            self.left = None
            self.right = None
        else:
            self.val = val
            self.left = None if (left is None) or left.is_empty() else left
            self.right = None if (right is None) or right.is_empty() else right

    @classmethod
    def fromSet(cls, edges : Set[T]):
        print ("Bulding from {0}".format(str(sorted(edges)))) # type: ignore
        def build(lst : List[T]):
            n : int = len(lst)
            if n == 0:
                return Tree()
            else:
                mid = n // 2
                root = lst[mid]
                left = build(lst[0:mid])
                right = build(lst[mid+1:])
                return Tree(root,left,right)

        return build(sorted(edges)) # type: ignore

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
        return self.left if self.has_left() else Tree()

    def get_right(self):
        return self.right if self.has_right() else Tree()

    def to_json(self):
        if self.is_empty():
            return []
        elif self.is_leaf():
            return [self.val]
        else:
            return [self.val, self.get_left().to_json(), self.get_right().to_json()]

    def __str__(self):
        if self.is_empty():
            return "Set()"
        elif self.is_leaf():
            return "Set({0})".format(self.val)
        else:
            return "Set({0}, {1}, {2})".format(self.val, self.get_left(), self.get_right())
