notation α " ⇀ " β => α -> Option β


inductive Location
  | X
  | Y
  deriving Repr


structure State  where
  lookup : Location -> Nat

def x := State.lookup
