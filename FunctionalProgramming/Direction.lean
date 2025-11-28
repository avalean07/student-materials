inductive Direction where | left | right
  deriving Repr, DecidableEq

def Direction.opposite : Direction → Direction
  | .left => .right
  | .right => .left
