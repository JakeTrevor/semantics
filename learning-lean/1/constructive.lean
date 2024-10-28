variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
   (λ pq => And.intro pq.right pq.left)
   (λ qp => And.intro qp.right qp.left)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (λ pq => pq.elim Or.inr Or.inl)
    (λ pq => pq.elim Or.inr Or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
  (λ pq_r  =>
    have p := pq_r.left.left
    have q := pq_r.left.right
    have r := pq_r.right
    And.intro (p) (And.intro q r)
  )
  (λ p_qr =>
    have p := p_qr.left
    have q := p_qr.right.left
    have r := p_qr.right.right
    And.intro (And.intro p q) r
  )


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (λ pq_r =>  pq_r.elim
      (λ pq => pq.elim
        (Or.inl)            --p
        (Or.inr ∘ Or.inl)   --q
      )
      (Or.inr ∘ Or.inr)     --r
    )
    (λ p_qr => p_qr.elim
      (Or.inl ∘ Or.inl )    --p
      (λ qr => qr.elim
        (Or.inl ∘ Or.inr)   --q
        (Or.inr)            --r
      )
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ pqr =>
    have p' := pqr.left
    have qr := pqr.right
    Or.elim qr
      (Or.inl ∘ And.intro p' )
      (Or.inr ∘ And.intro p')
    )
    (λ pq_pr => Or.elim pq_pr
      (λ pq =>
        have p := pq.left
        have q := pq.right
        And.intro p (Or.inl q)
      )
      (λ pr =>
      have p := pr.left
      have r := pr.right
      And.intro p (Or.inr r)
      )
    )


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (λ pqr =>
      Or.elim pqr
        (λ p => And.intro (Or.inl p) (Or.inl p))
        (λ qr =>
        have q := qr.left
        have r := qr.right
        And.intro (Or.inr q) (Or.inr r))
    )
    (λ pq_pr =>
      And.elim (
        λ (pq : p ∨ q ) (pr : p ∨ r) =>
          Or.elim pq Or.inl (Or.elim pr
            (λ q _ => Or.inl q)
            (λ r q => Or.inr (And.intro q r))
          )
      ) (pq_pr)
    )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (λ p_q_r => (λ pq => (p_q_r pq.left pq.right)))
    (λ pq_r => (λ p q => (pq_r (And.intro p q))))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (λ pq_r => And.intro (pq_r ∘ Or.inl) (pq_r ∘ Or.inr))
  (λ pr_qr => And.elim (
    λ pq pr => (λ p_q => Or.elim p_q pq pr)
  ) pr_qr)


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ n_pq =>
      And.intro (n_pq ∘ Or.inl) (n_pq ∘ Or.inr)
    )
    (λ np_nq => And.elim
      (λ np nq => (λ p_or_q => p_or_q.elim np nq ))
    np_nq)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (λ np => np.elim
    (λ np npq => np npq.left)
    (λ nq npq => nq npq.right)
  )

example : ¬(p ∧ ¬p) :=  -- i.e. p ∧ ¬p -> false
  (λ p_np => absurd p_np.left p_np.right)


example : p ∧ ¬q → ¬(p → q) :=
  (λ p_and_nq pq =>
    have q := pq p_and_nq.left
    have nq := p_and_nq.right
    absurd q nq
  )


example : ¬p → (p → q) :=
  (λ np p => absurd p np)


example : (¬p ∨ q) → (p → q) :=
  (λ np_or_q p => np_or_q.elim (λ np => absurd p np ) id)


example : p ∨ False ↔ p :=
  Iff.intro
    (λ p_f => p_f.elim id (False.elim))
    (Or.inl)


example : p ∧ False ↔ False :=
  Iff.intro
    (λ p_f => p_f.elim (λ _ f => f))
    (False.elim)

example : (p → q) → (¬q → ¬p) :=
  (λ p_q nq p => absurd (p_q p) nq)
