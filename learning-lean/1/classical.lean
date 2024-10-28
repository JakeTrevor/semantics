open Classical

variable (p q r : Prop)


example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (λ p_qr =>  (em p).elim
    (λ p => (p_qr p).elim
      (Or.inl ∘ λ x _ => x)
      (Or.inr ∘ λ x _ => x)
    )
    (λ np => Or.inl (λ p => absurd p np)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (λ npq => (em p).elim
    (λ p => (em q).elim
      (λ q =>
        have pq := (And.intro p q )
        absurd pq npq
      )
      (Or.inr)
    )
    (Or.inl))


example : ¬(p → q) → p ∧ ¬q :=
  λ npq => (em p).elim
    (λ p => (em q).elim
      (λ q =>
        have pq := λ _ => q
        absurd pq npq
      )
      (λ nq => And.intro p nq)
    )
    (λ np => (em q).elim
      sorry
      sorry
    )

example : (p → q) → (¬p ∨ q) :=
  (λ p_q => (em p).elim (Or.inr ∘  p_q) Or.inl)


  -- if you give me a p I can solve this
example : (¬q → ¬p) → (p → q) :=
  λ nq_np p => (em q).elim id (λ q => absurd p (nq_np q))

example : p ∨ ¬p := (em p)
-- is that it?

example : (((p → q) → p) → p) :=
 (λ pqp =>
    (em q).elim
      (λ q =>
        have pq := λ _ => q
        pqp pq
      )
      sorry
  )
