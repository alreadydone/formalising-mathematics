import week_7.Part_A_quotients
import week_7.Part_B_universal_property

/-

# `Z ≃ ℤ` 

Let's use the previous parts to show that Z and ℤ are isomorphic.

-/

-- Let's define pℤ to be the usual subtraction function ℕ² → ℤ
def pℤ (ab : N2) : ℤ := (ab.1 : ℤ) - ab.2

@[simp] lemma pℤ_def (a b : ℕ) : pℤ (a, b) = (a : ℤ) - b := rfl

-- Start with `intro z, apply int.induction_on z` to prove this.
theorem pℤsurj : function.surjective pℤ :=
begin
  intro z, cases z,
  use (z,0), refl,
  use (0,z.succ), refl
  /-intro z, apply int.induction_on z,
  use (0,0), refl,
  rintro i ⟨⟨a,b⟩,h⟩, use (a.succ,b),
  rw pℤ_def at *, rw ← h, push_cast, abel,
  rintro i ⟨⟨a,b⟩,h⟩, use (a,b.succ),
  rw pℤ_def at *, rw ← h, push_cast, abel-/
end

-- The fibres of pℤ are equivalence classes.
theorem pℤequiv (ab cd : N2) : ab ≈ cd ↔ pℤ ab = pℤ cd :=
begin
  cases ab, cases cd,
  rw [N2.equiv_def', pℤ_def, pℤ_def],
  rw sub_eq_sub_iff_add_eq_add,
  norm_cast
end

-- It's helpful to have a random one-sided inverse coming from surjectivity
noncomputable def invp : ℤ → N2 :=
λ z, classical.some (pℤsurj z)

-- Here's the proof that it is an inverse.
@[simp] theorem invp_inv (z : ℤ) : pℤ (invp z) = z :=
classical.some_spec (pℤsurj z)

-- Now we can prove that ℤ and pℤ are universal.
theorem int_is_universal : is_universal ℤ pℤ :=
begin
  --rcases @quotient_is_universal N2 _ with ⟨h,H⟩,
  split, exact λ x y, (pℤequiv x y).1,
  intros T f h, use f ∘ invp, split,
    ext, apply h, rw pℤequiv, simp,
    rintros k rfl, ext, simp
end

-- and now we can prove they're in bijection
noncomputable example : ℤ ≃ Z :=
universal_equiv_quotient _ _ _ int_is_universal 
