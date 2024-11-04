set_option linter.unusedVariables false
open Option (some none)

notation α " ⇀ " β => α -> Option β


def inDomain (f : α ⇀ β) (a) :=
  ∃ x, f a = some x
notation elt " ∈ Dom(" fn ") " => inDomain fn elt

-- not derivable;
axiom Option.em {α} (a : Option α) : (a = none ∨ ∃x, a = some x)

theorem notInDomainEqNone (a_not_in_f : ¬(a ∈ Dom(f))) : f a = none :=
  (Option.em (f a)).elim
    id
    (λ ex => absurd ex a_not_in_f)

namespace Relation
  def Relation (α) := α -> α -> Prop

  def Reflexive (rel : Relation α) :=
    ∀ a, (rel a a)

  def Transitive (rel : Relation α) :=
    ∀ a b c, (rel a b) -> (rel b c) -> (rel a c)

  def AntiSymmetric (rel : Relation α) :=
    ∀ a b, (rel a b) -> (rel b a) -> (a = b)

  def PartialOrder (rel: Relation α) :=
    Reflexive rel ∧ Transitive rel ∧ AntiSymmetric rel

  def isBottom {rel : Relation α} (_: PartialOrder rel) (bot) :=
    ∀ a, rel bot a


  def Symmetric (rel : Relation α) :=
    ∀ a b, (rel a b) -> (rel b a)

  def EquivalenceRelation (rel : Relation α) :=
    Reflexive rel ∧ Transitive rel ∧ Symmetric rel

end Relation

open Relation

-- Our relation:
def fn_lte (f g : (γ ⇀ δ)) : Prop :=
    ∀ a,  a ∈ Dom(f) -> f a = g a
notation lhs " ⊑ " rhs => fn_lte lhs rhs

-- 1.i

theorem fn_lte_reflexive : Reflexive (@fn_lte γ δ) :=
  λ _f _a _a_in_dom => rfl

theorem fn_lte_trans : Transitive (@fn_lte γ δ) :=
  (λ f g h f_g g_h a a_in_dom_f =>
      have fa_ga := (f_g a) a_in_dom_f

      have a_in_dom_g : a ∈ Dom(g) :=
        a_in_dom_f.elim
          (λ x fa_x =>
            have ga_x : g a = some x := (fa_x ▸ fa_ga).symm
            Exists.intro x ga_x
          )

      have ga_ha := (g_h a) a_in_dom_g
      ga_ha ▸ fa_ga
  )

open Classical


theorem fn_lte_antiSymm : AntiSymmetric (@fn_lte γ δ) :=
  (λ f g f_g g_f => funext (λ a =>
    (em (a ∈ Dom(f))).elim
      (f_g a)
      (λ a_not_in_f =>
        (em (a ∈ Dom(g))).elim
          (λ a_in_dom_g =>
            have ga_fa := (g_f a) a_in_dom_g
            a_in_dom_g.elim (λ x ga_x =>
              have fa_x : f a = some x := (ga_x ▸ ga_fa).symm
              have a_in_dom_f : a ∈ Dom(f) := Exists.intro x fa_x
              absurd a_in_dom_f a_not_in_f
            )
          )
          (λ a_not_in_g =>
            have fa_none := notInDomainEqNone a_not_in_f
            have ga_none := notInDomainEqNone a_not_in_g
            (ga_none ▸ fa_none)
          )
      )
  ))



theorem fn_lte_po : PartialOrder (@fn_lte γ δ) :=
  And.intro
    fn_lte_reflexive
  (And.intro
    fn_lte_trans
    fn_lte_antiSymm
  )


-- 1.ii

-- consider some chain of functions C:
-- C 0 ⊑ C 1 ⊑ C 2 ⊑ C 3 ... ⊑ C n ⊑ C n+1
-- where C (n) : α ⇀ β
-- in general we have that:
-- ∀ n, C 0 ⊑ C n
-- and ∀ n, C n ⊑ C (n+1)
-- show that:
-- the lub of the chain `lub C` is given by:

namespace Poset
  variable {rel : Relation α}
  variable {rel2 : Relation β}
  variable (po_rel : PartialOrder rel)
  variable (po_rel2 : PartialOrder rel2)


  def Monotonic (f: α -> β) : Prop :=
    ∀ a b, rel a b -> rel2 (f a) (f b)

  def FixedPoint (f : α -> α) (a : α) : Prop := a = f a

  def const (b : β) (_ : α) := b

  axiom constIsConst (b : β) (c : α) : (const b c = b)

  theorem constMonotone {α β} {rel : Relation α} {rel2 : Relation β}
    : ∀ a, @Monotonic α β rel rel2 (@const α β a)
  :=
    λ x a b relab =>
      have ca_x : const x a = x := constIsConst x a
      have cb_x : const x a = x := constIsConst x b
    sorry

end Poset

-- def lub (C: Nat -> (α  ⇀ α)) (n: Nat) (a) : α ⇀ α :=
--   if (a ∈ Dom(C n)) then (C n a) else none

-- 1.iii
def undefined_fn : γ ⇀ δ := λ _ => none
notation " ⊥ " => undefined_fn

-- true, but is it derivable?
axiom domBotEmpty {γ δ} : ∀ x, ¬(x ∈ Dom(@undefined_fn γ δ))

example : isBottom (@fn_lte_po γ δ) ⊥ :=
  λ _ x b_dom_bot => absurd b_dom_bot (domBotEmpty x)
