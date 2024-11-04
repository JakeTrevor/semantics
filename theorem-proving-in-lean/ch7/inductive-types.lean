-- ex 1. (See natural number game)

-- ex 2.

inductive MyList (α : Type u) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

namespace MyList
  notation a " : " b => cons a b
  notation "[]" => nil
  notation "[" x "]" => cons x []

  def length (a: MyList α) : Nat :=
    match a with
      | .nil => 0
      | .cons _ rest => 1 + length rest

  theorem len_nil {α} : (length (@nil α))= 0 := rfl

  theorem len_cons : length (a : b) = 1 + length b := rfl


  def append (a b : MyList α) : MyList α :=
    match a with
      | .nil => b
      | .cons x rest => x : (append rest b)

  notation a " ++ " b => append a b

  theorem nil_append (a : MyList α) : ([] ++ a) = a := rfl
  theorem append_nil (a : MyList α) : (a ++ []) = a := by
    induction a with
    | nil => rw [nil_append]
    | cons x rest hd => rw [append, hd]


  theorem singleton_append : ([a] ++ b) = a : b := rfl

  theorem append_assoc : (a ++ b ++ c) = ((a ++ b) ++ c) := by
    induction a with
      | nil =>
        rw [nil_append, nil_append]
      | cons x rest hd =>
        rw [append, hd, append, append]


  def reverse (a : MyList α) : MyList α :=
    match a with
      | .nil => []
      | .cons x rest => (reverse rest) ++ [x]

  theorem reverse_nil {α} : reverse (@nil α) = [] := rfl

  theorem reverse_append : reverse (a ++ b) = (reverse b ) ++ reverse a := by
    induction a with
    | nil => rw [reverse_nil, nil_append, append_nil]
    | cons x rest hd =>
      rw [append, reverse, reverse, hd, append_assoc]


  -- a.
  theorem len_append : length (s ++ t) = length s + length t := by
    induction s with
      | nil => rw [nil_append, len_nil, Nat.zero_add]
      | cons x rest hd =>
        rw [append, len_cons, len_cons, hd, Nat.add_assoc]


  -- b.
  example : length (reverse t) = length t := by
    induction t with
    | nil => rw [reverse_nil, len_nil]
    | cons x rest hd =>
      rw [reverse, len_append]
      repeat rw [len_cons]
      rw [len_nil, Nat.add_zero, Nat.add_comm, hd]

  -- c.
  example: reverse (reverse t) = t := by
    induction t with
    | nil =>
      repeat rw [reverse_nil]
    | cons x rest hd =>
      rw [reverse, reverse_append, hd, reverse, reverse_nil, nil_append, singleton_append]
end MyList



-- ex 3
inductive ArithExpr where
  | const : Nat -> ArithExpr
  | var : Nat -> ArithExpr
  | plus : ArithExpr -> ArithExpr -> ArithExpr
  | times : ArithExpr -> ArithExpr -> ArithExpr
  deriving Repr


-- Not sure why this doesnt work
def eval (ctx : List Nat) (expr : ArithExpr) : Nat :=
  have evl := eval ctx
  match expr with
  | .const n => n
  | .var n => ctx.get! n
  | .plus s t => (evl s) + (evl t)
  | .times s t => (evl s) * (evl t)

#check @ArithExpr.casesOn
