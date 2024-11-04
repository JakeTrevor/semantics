-- open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r :=
  λ a_r => a_r.elim (λ _ r => r)

example : (a : α) → r → (∃ _x : α, r) :=
  λ a r => Exists.intro a r

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (λ px_r => px_r.elim
      (λ a pa_r =>
      have ⟨pa, r⟩ := pa_r
      And.intro (Exists.intro a pa) r
    ))
    (λ ⟨px_r, r⟩ => px_r.elim (λ a pa =>
      Exists.intro a (And.intro pa r))
    )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (λ px_qx => px_qx.elim (λ a pa_qa =>
      pa_qa.elim
        (λ pa => Or.inl (Exists.intro a pa))
        (λ qa => Or.inr (Exists.intro a qa))
    ))
    (λ px_qx => px_qx.elim
      (λ px => px.elim (λ a pa => Exists.intro a (Or.inl pa)))
      (λ qx => qx.elim (λ a qa => Exists.intro a (Or.inr qa)))
    )


-- excluded middle: (p ∨ ¬p)
-- without em, we cannot say
-- p != ¬¬p


section requiresClassical
open Classical

-- here for use
theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (λ ax_px np => np.elim (λ a npa =>
      have pa := ax_px a
      absurd pa npa
    ))
    (λ nex_npx x => byContradiction (λ npx =>
      have ex_npx := Exists.intro x npx
      absurd ex_npx nex_npx
    ))



example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (λ ex_px ax_npx => ex_px.elim (λ a pa =>
      have npa := ax_npx a
      absurd pa npa
    ))
   (λ ax_npx => (em (∃x, p x )).elim
      id
      (λ nex_px => ax_npx.elim
        (λ a npa =>
          have ex_px := Exists.intro a npa
          absurd ex_px nex_px
        ))
    )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    -- note *em* was required here:
    (λ nex_px a => (em (p a)).elim
      (λ pa => nex_px.elim (Exists.intro a pa))
      id
    )
    (λ ax_npx nex_px => nex_px.elim (λ a pa =>
      have npa := ax_npx a
      absurd pa npa
    ))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (λ nax_px => (em (∃ x, ¬ p x)).elim
      id
      (λ nex_npx => nex_npx.elim (sorry)
      )
    )
    (λ ex_npx ax_px => ex_npx.elim (λ a npa =>
      have pa := ax_px a
      absurd pa npa
    ))

end requiresClassical

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (λ px_r ex_px => ex_px.elim (λ a pa =>
      have pa_r := px_r a
      pa_r pa
    ))
    (λ ex_px_r a pa =>
      have ea_pa :=  Exists.intro a pa
      ex_px_r ea_pa
    )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (λ ex_px_r ax_px => ex_px_r.elim (λ x px_r =>
      have  px := ax_px x
      px_r px
    ))
    (λ ax_px_r => Exists.intro a (λ pa => sorry )
    )


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (λ ex_r_px r => ex_r_px.elim
      (λ x px => Exists.intro x (px r)))
    (λ r_ex_px => sorry
    )
