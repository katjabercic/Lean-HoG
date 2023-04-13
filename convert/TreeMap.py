class Smap:
    def __init__(self, key, val, left, right):
        self.key = key
        self.val = val
        self.left = left
        self.right = right

    def __str__(self):
        if self.val is None:
            return "Smap.empty (by first | bool_reflect | rfl)"
        if self.left is None and self.right is None:
            return "Smap.leaf " + str(self.key) + " (" + str(self.val) + ") " + " (by first | bool_reflect | rfl) (by first | bool_reflect | rfl)"
        if self.left is None:
            left = "Smap.empty (by first | bool_reflect | rfl)"
        else:
            left = str(self.left)
        if self.right is None:
            right = "Smap.empty (by first | bool_reflect | rfl)"
        else:
            right = str(self.right)
        return "Smap.node " + str(self.key) + " (" + str(self.val) + ") " + "\n(" + left + ")\n(" + right + ")"
