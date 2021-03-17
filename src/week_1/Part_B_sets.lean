import tactic

-- Let `Ω` be a "big underlying set" and let `X` and `Y` and `Z` be subsets

variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

namespace xena

/-!

# subsets

Let's think about `X ⊆ Y`. Typeset `⊆` with `\sub` or `\ss`
-/

-- `X ⊆ Y` is the same as `∀ a, a ∈ X → a ∈ Y` , by definition.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  -- true by definition
  refl
end

lemma subset_refl : X ⊆ X :=
begin
  intro a, exact id
end

lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  -- If you start with `rw subset_def at *` then you
  -- will have things like `hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z`
  -- You need to think of `hYZ` as a function, which has two
  -- inputs: first a term `a` of type `Ω`, and second a proof `haY` that `a ∈ Y`.
  -- It then produces one output `haZ`, a proof that `a ∈ Z`.
  -- You can also think of it as an implication:
  -- "if a is in Ω, and if a ∈ Y, then a ∈ Z". Because it's an implication,
  -- you can `apply hYZ`. This is a really useful skill!
  intro a, exact (@hYZ a) ∘ (@hXY a)
end

/-!

# Equality of sets

Two sets are equal if and only if they have the same elements.
The name of this theorem is `set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff
end

-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 


lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
  -- start with `ext a`,
  ext a, exact ⟨@hXY a, @hYX a⟩
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  -- true by definition
  refl,
end


-- You can rewrite with those lemmas above if you're not comfortable with
-- assuming they're true by definition.

-- union lemmas

lemma union_self : X ∪ X = X :=
begin
  ext a, split, {intro h, cases h, exacts [h,h]},
  intro h, left, exact h
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  intro, exact or.inl
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
  exact λ_, or.inr
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split, intro h, split,
  exact λ_ x, h(or.inl x),
  exact λ_ y, h(or.inr y), 
  exact λ⟨h1,h2⟩ a, or.rec (@h1 a) (@h2 a)
end

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  exact λa, or.imp (@hWX a) (@hYZ a)
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  exact λa, or.imp_left (@hXY a)
end

-- etc etc

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  exact λ_ h, h.1
end

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X :=
begin
  ext a, split, intro h, exact h.1,
  intro h, exact ⟨h,h⟩
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  ext a, rw [inter_def, and.comm], refl
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  ext a, repeat {rw inter_def}, rw and.assoc
end

/-!

### Forall and exists

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  split, intros ne b bX, exact ne ⟨b,bX⟩,
  rintros an ⟨a,aX⟩, exact an a aX
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split, intro na, by_contra nen,
  apply na, intro a, by_contra aX, exact nen ⟨a,aX⟩,
  rintro ⟨b,bX⟩, exact λh, bX (h b)
end

end xena

