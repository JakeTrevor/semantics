variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (λ x_pq => And.intro
      (λ x => (x_pq x).left)
      (λ x => (x_pq x).right)
    )
    (λ ⟨px, qx⟩ x => And.intro (px x) (qx x))


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ pa_qa pa x =>
    have px := pa x
    have px_qx := pa_qa x
    px_qx px


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ pa_qa x => Or.elim pa_qa
    (λ pa => Or.inl (pa x))
    (λ qa => Or.inr (qa x))
/-
the reverse does not hold, since:

the conclusion sates:
  for all x, px or qx

in contrast, our premise states:
  either:
    for all x, px
      OR
    for all x, qx

the premise requires that p or q holds for all x

whereas the conclusion allows for p to hold for some x, but not others, so long as q holds in its absence

thus you cannot derive the premise from the conclusion
-/

--- ex 2:

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _x : α, r) ↔ r) :=
  λ a => Iff.intro
    (λ a_r => a_r a)
    λ r _ => r

section req_classical
open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (λ ax_px_r => (em r).elim
      Or.inr
      (λ nr => Or.inl (λ a => (ax_px_r a).elim
        id
        (λ r => absurd r nr)
      ))
    )
    (λ ax_px_r a => ax_px_r.elim
      (λ ax_px => Or.inl (ax_px a))
      Or.inr
    )

end req_classical


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (λ ax_r_px r a => ax_r_px a r )
    (λ r_ax_px  a  r => r_ax_px r a)



--- ex 3: barbers paradox
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  (h barber).elim (λ s_ns ns_s =>
  have s : shaves barber barber := sorry
  absurd s (s_ns s)
  )

--- this is easy with classical reasoning:
section req_classical
open Classical

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  (h barber).elim (λ s_ns ns_s =>
  (em (shaves barber barber)).elim
    (λ s => absurd s (s_ns s))
    (λ ns => absurd (ns_s ns) ns)
  )

end req_classical
--- ex 4: various Nat props

def even (n : Nat) : Prop := ∃ x : Nat, n = 2*x

def prime (n : Nat) : Prop := (∀ p q : Nat, (n = p * q) -> (p=1 ∧ q=n)∨ (p=n ∧ q=1))

def infinitely_many_primes : Prop := (∀ x : Nat, ∃x' : Nat, x' > x ∧ prime x')

def Fermat_prime (n : Nat) : Prop := ∃ p : Nat, n = (2 ^ (2 ^ p)) + 1

def infinitely_many_Fermat_primes : Prop := ∀ x : Nat, ∃ x', x' > x ∧ Fermat_prime x'

def goldbach_conjecture : Prop := ∀ x, x > 2 ∧ even x -> ∃ p q, prime p ∧ prime q ∧ x = p + q

def Goldbach's_weak_conjecture : Prop := ∀ x, x > 5 ∧ ¬ even x -> ∃ p q r, prime p ∧ prime q ∧ prime r ∧ x = p + q + r

def Fermat's_last_theorem : Prop := ¬∃ n : Nat, n > 2 ∧ ∃ p q r : Nat,  (p^n) + (q ^ n )= (r ^ n)
