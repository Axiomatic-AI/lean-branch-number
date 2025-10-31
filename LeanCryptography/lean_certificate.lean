import Mathlib

set_option diagnostics true
open Classical

-- Branch number of invertible matrices over finite fields

noncomputable instance {p q : ℕ} [Fact p.Prime] [Fact (0 < q)] : Fintype (GaloisField p q) :=
  Fintype.ofFinite (GaloisField p q)

variable (p q n : ℕ) [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]

-- ========================================
-- SECTION 1: INTRO DEFINITIONS
-- ========================================

-- Hamming weight function
noncomputable def wH
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(x : Fin n → GaloisField p q)
:
ℕ := (Finset.univ.filter (fun i => x i ≠ 0)).card


-- Branch function h(M,x) = wₕ(x) + wₕ(Mx)
noncomputable def h
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(_hM : IsUnit (M.det))
(x : Fin n → GaloisField p q)
(_hx : x ≠ 0)
:
ℕ := wH x + wH (M.mulVec x)

-- ========================================
-- SECTION 2: CORE SETS + FINITE TYPES INSTANCES
-- ========================================

-- Helper : nonzero vectors
noncomputable def nonzero_vectors
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
:
Finset (Fin n → GaloisField p q) := {x | x ≠ 0}

-- Vectors with low Hamming weight: 1 ≤ wH(x) ≤ ⌊(n+1)/2⌋
noncomputable def low_weight_vectors
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
:
Finset (Fin n → GaloisField p q) := {x | 1 ≤ wH x ∧ wH x ≤ (n + 1) / 2}

-- Membership lemma to avoid computational unfolding
lemma mem_low_weight_vectors_iff {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (x : Fin n → GaloisField p q) :
  x ∈ low_weight_vectors ↔ 1 ≤ wH x ∧ wH x ≤ (n + 1) / 2 := by
  simp [low_weight_vectors]

-- Vectors with high Hamming weight: ⌊(n+1)/2⌋ < wH(x) ≤ n
noncomputable def high_weight_vectors
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
:
Finset (Fin n → GaloisField p q) := {x | (n + 1) / 2 < wH x ∧ wH x ≤ n}


-- ========================================
-- FINITE TYPES INSTANCES
-- ========================================

-- Essential Fintype instances
noncomputable instance {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) :
  Fintype { wH x + wH (M.mulVec x) | x ∈ nonzero_vectors } :=
  Set.Finite.fintype (Set.Finite.image (fun x => wH x + wH (M.mulVec x)) nonzero_vectors.finite_toSet)

noncomputable instance {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) :
  Fintype { wH x + wH (M.mulVec x) | x ∈ low_weight_vectors } :=
  Set.Finite.fintype (Set.Finite.image (fun x => wH x + wH (M.mulVec x)) low_weight_vectors.finite_toSet)

noncomputable instance {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) :
  Fintype { wH x + wH (M.mulVec x) | x ∈ high_weight_vectors } :=
  Set.Finite.fintype (Set.Finite.image (fun x => wH x + wH (M.mulVec x)) high_weight_vectors.finite_toSet)

-- Fintype instance for branch values over union of low and high weight vectors
noncomputable instance union_weight_branch_values_fintype
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
:
Fintype { wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) ∪ (@high_weight_vectors p q n _ _ _) } :=
Set.Finite.fintype (Set.Finite.image (fun x => wH x + wH (M.mulVec x)) ((@low_weight_vectors p q n _ _ _) ∪ (@high_weight_vectors p q n _ _ _)).finite_toSet)

-- Fintype instance for branch values over high weight vectors with low Mx weight
noncomputable instance high_weight_low_mx_branch_values_fintype
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
:
Fintype { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } :=
Set.Finite.fintype (Set.Finite.image (fun x => wH x + wH (M.mulVec x)) { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 }.finite_toSet)

-- Fintype instance for branch values over high weight vectors with high Mx weight
noncomputable instance high_weight_high_mx_branch_values_fintype
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
:
Fintype { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } } :=
Set.Finite.fintype (Set.Finite.image (fun x => wH x + wH (M.mulVec x)) { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 }.finite_toSet)

-- Fintype instance for constrained low-weight branch values
noncomputable instance constrained_low_weight_branch_values_fintype
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
:
Fintype { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } :=
Set.Finite.fintype (Set.Finite.image (fun x => wH x + wH (M.mulVec x)) { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 }.finite_toSet)

-- Fintype instance for constrained nonzero-weight branch values (for D)
noncomputable instance constrained_nonzero_weight_branch_values_fintype
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
:
Fintype { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@nonzero_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } :=
Set.Finite.fintype (Set.Finite.image (fun x => wH x + wH (M.mulVec x)) { y ∈ (@nonzero_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 }.finite_toSet)

-- Fintype instance for matrix inverse constrained set
noncomputable instance fintype_matrix_inverse_constrained
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q)) :
Fintype { wH y + wH ((M⁻¹).mulVec y) | y ∈ { y | ∃ x, M.mulVec x = y ∧ 1 ≤ wH x ∧ wH x ≤ n ∧ 1 ≤ wH y ∧ wH y ≤ (n + 1) / 2 } } :=
Set.Finite.fintype (Set.Finite.image (fun y => wH y + wH ((M⁻¹).mulVec y))
  ({ y | ∃ x, M.mulVec x = y ∧ 1 ≤ wH x ∧ wH x ≤ n ∧ 1 ≤ wH y ∧ wH y ≤ (n + 1) / 2 } : Set _).toFinite)

-- Fintype instance for simplified weight-constrained set
noncomputable instance fintype_weight_constrained
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q)) :
Fintype { wH y + wH ((M⁻¹).mulVec y) | y ∈ { y | 1 ≤ wH y ∧ wH y ≤ (n + 1) / 2 } } :=
Set.Finite.fintype (Set.Finite.image (fun y => wH y + wH ((M⁻¹).mulVec y))
  ({ y | 1 ≤ wH y ∧ wH y ≤ (n + 1) / 2 } : Set _).toFinite)



-- ========================================
-- SECTION 3: HELPER LEMMAS
-- ========================================

-- ----------------------------------------
-- 3.1: Basic Vector Properties
-- ----------------------------------------

-- Helper lemma: the Hamming weight of any vector is at most n
lemma wH_le_n
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(x : Fin n → GaloisField p q)
:
wH x ≤ n := by
  simp only [wH]
  -- The filtered set is a subset of the universal set
  calc (Finset.univ.filter (fun i => x i ≠ 0)).card
    ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by simp [Finset.card_univ]

-- Helper lemma: standard basis vector has Hamming weight 1 and is nonzero
lemma standard_basis_vector_properties
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(i₀ : Fin n)
:
let e := fun i => if i = i₀ then (1 : GaloisField p q) else 0
e ≠ 0 ∧ wH e = 1 := by
  let e := fun i => if i = i₀ then (1 : GaloisField p q) else 0
  constructor
  · -- e ≠ 0
    intro h_zero
    have h_eq : e i₀ = (0 : Fin n → GaloisField p q) i₀ := congrFun h_zero i₀
    simp [e] at h_eq
  · -- wH e = 1
    simp only [wH]
    have h_filter_eq : (Finset.univ.filter (fun i => (if i = i₀ then (1 : GaloisField p q) else 0) ≠ 0)) = {i₀} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      split_ifs with h <;> simp [h]
    rw [h_filter_eq, Finset.card_singleton]

lemma floor_arithmetic_bound (n : ℕ) : 2 * ((n + 1) / 2) ≥ n := by omega
lemma nat_gt_floor_bound (x n : ℕ) (h : x > (n + 1) / 2) : x ≥ (n + 1) / 2 + 1 := by omega


-- Helper lemma: positive Hamming weight => x ≠ 0
lemma nonzero_of_pos_weight
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(x : Fin n → GaloisField p q)
(h : 1 ≤ wH x)
:
x ≠ 0 := by
  intro h_zero
  have h_wH_zero : wH x = 0 := by simp [wH, h_zero]
  rw [h_wH_zero] at h
  omega

lemma nonzero_hamming_weight_pos
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(x : Fin n → GaloisField p q)
(hx_ne_zero : x ≠ 0)
:
1 ≤ wH x := by
  by_contra h_not
  simp at h_not
  have h_x_zero : x = 0 := by
    ext i
    by_contra h_ne
    have h_wH_pos : 1 ≤ wH x := by
      simp only [wH]
      apply Nat.succ_le_iff.mpr
      rw [Finset.card_pos]
      use i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_ne
    rw [h_not] at h_wH_pos
    norm_num at h_wH_pos
  exact hx_ne_zero h_x_zero


-- ----------------------------------------
-- 3.2: Weight Vector Set Properties
-- ----------------------------------------

-- Helper lemma: elements of low_weight_vectors are nonzero
lemma low_weight_vectors_mem_nonzero
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
{x : Fin n → GaloisField p q}
(hx : x ∈ low_weight_vectors)
:
x ≠ 0 := by
  rw [low_weight_vectors] at hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact nonzero_of_pos_weight x hx.1


-- Helper lemma: elements of high_weight_vectors are nonzero
lemma high_weight_vectors_mem_nonzero
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
{x : Fin n → GaloisField p q}
(hx : x ∈ high_weight_vectors)
:
x ≠ 0 := by
  rw [high_weight_vectors] at hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have h_ge_one : 1 ≤ wH x := by
    have h_pos : 1 < n := Fact.out
    have h_bound : 1 ≤ (n + 1) / 2 := by omega
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt h_bound hx.1)
  exact nonzero_of_pos_weight x h_ge_one



-- ----------------------------------------
-- 3.2: Non Empty Set Properties
-- ----------------------------------------

-- Helper lemma: Nonzero vectors nonempty
lemma nonzero_vectors_nonempty
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
:
(nonzero_vectors : Finset (Fin n → GaloisField p q)).Nonempty := by
  simp [nonzero_vectors, Finset.Nonempty]
  have h_nonempty : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.lt_trans (Nat.zero_lt_one) (Fact.out : 1 < n))
  cases' h_nonempty with i₀
  use fun i => if i = i₀ then 1 else 0
  intro h_zero
  have : (1 : GaloisField p q) = 0 := by
    have h_eq : (fun i => if i = i₀ then 1 else 0) i₀ = (0 : Fin n → GaloisField p q) i₀ :=
      congrFun h_zero i₀
    simp at h_eq
  exact one_ne_zero this


-- Helper lemma: low weight vectors nonempty
lemma low_weight_vectors_nonempty
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
:
(low_weight_vectors : Finset (Fin n → GaloisField p q)).Nonempty := by
  simp [low_weight_vectors, Finset.Nonempty]
  have h_nonempty : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.lt_trans (Nat.zero_lt_one) (Fact.out : 1 < n))
  cases' h_nonempty with i₀
  let x := fun i => if i = i₀ then (1 : GaloisField p q) else 0
  use x
  have h_props := @standard_basis_vector_properties p q n _ _ _ i₀
  constructor
  · rw [h_props.2]
  · rw [h_props.2]
    have h_pos : 1 < n := Fact.out
    omega

-- Helper lemma: high weight vectors nonempty
lemma high_weight_vectors_nonempty
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
:
(high_weight_vectors : Finset (Fin n → GaloisField p q)).Nonempty := by
  simp [high_weight_vectors, Finset.Nonempty]
  let x := fun _ : Fin n => (1 : GaloisField p q)
  use x
  have h_wH_eq_n : wH x = n := by
    simp only [wH, x]
    have h_filter_eq : (Finset.univ : Finset (Fin n)).filter (fun _ => (1 : GaloisField p q) ≠ 0) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp
    rw [h_filter_eq, Finset.card_univ, Fintype.card_fin]
  constructor
  · rw [h_wH_eq_n]
    have h_pos : 1 < n := Fact.out
    omega
  · rw [h_wH_eq_n]

-- Helper lemma: branch function values over high weight vectors form nonempty finset
lemma high_weight_branch_values_nonempty
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
:
({ wH x + wH (M.mulVec x) | x ∈ (@high_weight_vectors p q n _ _ _) } : Set ℕ).toFinset.Nonempty := by
  rw [Set.toFinset_nonempty]
  obtain ⟨x, hx⟩ := @high_weight_vectors_nonempty p q n _ _ _
  use wH x + wH (M.mulVec x)
  simp only [Set.mem_setOf_eq]
  exact ⟨x, hx, rfl⟩


-- Helper lemma: branch function values over low weight vectors form nonempty finset
lemma low_weight_branch_values_nonempty
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
:
({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) } : Set ℕ).toFinset.Nonempty := by
  rw [Set.toFinset_nonempty]
  obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
  use wH x + wH (M.mulVec x)
  simp only [Set.mem_setOf_eq]
  exact ⟨x, hx, rfl⟩


lemma high_weight_low_image_branch_values_nonempty
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(h_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 }.Nonempty)
:
({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } : Set ℕ).toFinset.Nonempty := by
  rw [Set.toFinset_nonempty]
  obtain ⟨x, hx⟩ := h_set_nonempty
  use wH x + wH (M.mulVec x)
  simp only [Set.mem_setOf_eq]
  exact ⟨x, hx, rfl⟩


lemma high_weight_high_image_branch_values_nonempty
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(h_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 }.Nonempty)
:
({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } } : Set ℕ).toFinset.Nonempty := by
  rw [Set.toFinset_nonempty]
  obtain ⟨x, hx⟩ := h_set_nonempty
  use wH x + wH (M.mulVec x)
  simp only [Set.mem_setOf_eq]
  exact ⟨x, hx, rfl⟩


-- ----------------------------------------
-- 3.3: Weight Partition Theorems
-- ----------------------------------------

-- Helper lemma: Weight range partition covers all nonzero vectors
theorem weight_partition_covers
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(x : Fin n → GaloisField p q)
(hx_ne_zero : x ≠ 0)
:
x ∈ low_weight_vectors ∨ x ∈ high_weight_vectors := by
  have h_wH_pos : 1 ≤ wH x := nonzero_hamming_weight_pos x hx_ne_zero
  have h_wH_bound : wH x ≤ n := by
    simp only [wH]
    have : (Finset.univ.filter (fun j => x j ≠ 0)) ⊆ Finset.univ := Finset.filter_subset _ _
    have : (Finset.univ.filter (fun j => x j ≠ 0)).card ≤ Finset.univ.card := Finset.card_le_card this
    simp only [Finset.card_fin] at this
    exact this
  -- Either wH(x) ≤ ⌊(n+1)/2⌋ or wH(x) > ⌊(n+1)/2⌋
  by_cases h : wH x ≤ (n + 1) / 2
  · left
    simp only [low_weight_vectors]
    simp
    exact ⟨h_wH_pos, h⟩
  · right
    simp only [high_weight_vectors]
    simp at h
    simp
    exact ⟨h, h_wH_bound⟩

-- Theorem: Nonzero vectors partition into low and high weight vectors
theorem nonzero_vectors_partition
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
:
(@nonzero_vectors p q n _ _ _) = (@low_weight_vectors p q n _ _ _) ∪ (@high_weight_vectors p q n _ _ _) := by
  ext x
  simp only [nonzero_vectors, low_weight_vectors, high_weight_vectors, Finset.mem_union]
  constructor
  · intro hx_nonzero
    have hx_ne_zero : x ≠ 0 := by simpa using hx_nonzero
    exact weight_partition_covers x hx_ne_zero
  · intro h_in_partition
    cases h_in_partition with
    | inl h_low =>
      simpa using low_weight_vectors_mem_nonzero h_low
    | inr h_high =>
      simpa using high_weight_vectors_mem_nonzero h_high


-- ----------------------------------------
-- 3.4: Fintype Instances
-- ----------------------------------------

noncomputable instance fintype_efficient_branch_set
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit (M.det))
:
Fintype { y | ∃ (x : Fin n → GaloisField p q) (hx_weight : 1 ≤ wH x ∧ wH x ≤ (n + 1) / 2),
    y = min (h M hM x (nonzero_of_pos_weight x hx_weight.1))
        (h (M⁻¹) (by rw [Matrix.det_nonsing_inv]; exact hM.ringInverse) x (nonzero_of_pos_weight x hx_weight.1)) } := by
  have h_eq : { y | ∃ (x : Fin n → GaloisField p q) (hx_weight : 1 ≤ wH x ∧ wH x ≤ (n + 1) / 2),
      y = min (h M hM x (nonzero_of_pos_weight x hx_weight.1))
          (h (M⁻¹) (by rw [Matrix.det_nonsing_inv]; exact hM.ringInverse) x (nonzero_of_pos_weight x hx_weight.1)) } =
    (low_weight_vectors.attach.image (fun ⟨x, hx⟩ =>
      min (h M hM x (low_weight_vectors_mem_nonzero hx))
          (h (M⁻¹) (by rw [Matrix.det_nonsing_inv]; exact hM.ringInverse) x (low_weight_vectors_mem_nonzero hx)))) := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro ⟨x, hx_weight, hy_eq⟩
      rw [hy_eq]
      apply Finset.mem_image.mpr
      use ⟨x, by
        simp only [low_weight_vectors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx_weight⟩
      simp only [Finset.mem_attach, true_and]
    · intro h_mem
      have h_mem' : y ∈ (low_weight_vectors.attach.image (fun ⟨x, hx⟩ =>
        min (h M hM x (low_weight_vectors_mem_nonzero hx))
            (h (M⁻¹) (by rw [Matrix.det_nonsing_inv]; exact hM.ringInverse) x (low_weight_vectors_mem_nonzero hx)))) := h_mem
      rw [Finset.mem_image] at h_mem'
      obtain ⟨⟨x, hx_mem⟩, _, hy_eq⟩ := h_mem'
      use x, by
        rw [low_weight_vectors] at hx_mem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx_mem
        exact hx_mem
      simp only at hy_eq
      exact hy_eq.symm
  rw [h_eq]
  exact Set.Finite.fintype (Finset.finite_toSet _)



-- ----------------------------------------
-- 4.1: Utility Lemmas for Minimization
-- ----------------------------------------

lemma finset_min_three_elements (a b c : ℕ) :
  ({a, b, c} : Finset ℕ).min' (by simp : ({a, b, c} : Finset ℕ).Nonempty) = min a (min b c) := by
  have h_mem := Finset.min'_mem ({a, b, c} : Finset ℕ) (by simp)
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h_mem
  have h_le_a := Finset.min'_le ({a, b, c} : Finset ℕ) a (by simp)
  have h_le_b := Finset.min'_le ({a, b, c} : Finset ℕ) b (by simp)
  have h_le_c := Finset.min'_le ({a, b, c} : Finset ℕ) c (by simp)
  omega



-- ========================================
-- SECTION 3: MAIN DEFINITIONS
-- ========================================

-- Branch number definition: B(M) = min{h(M,x) | x ∈ 𝔽^n, x ≠ 0} for invertible M
noncomputable def Branchnumber
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(_hM : IsUnit (M.det))
:
ℕ := { wH x + wH (M.mulVec x) | x ∈ nonzero_vectors }.toFinset.min'
(by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := @nonzero_vectors_nonempty p q n _ _ _
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    exact ⟨x, hx, rfl⟩
  )

-- Efficient branch number: min{min{h(M,x), h(M⁻¹,x)} | x ∈ Fq^n, 1 ≤ wH(x) ≤ ⌊(n+1)/2⌋}
noncomputable def Branchnumber_efficient
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit (M.det))
:
ℕ :=
-- Direct LaTeX definition: min{min{h(M,x), h(M⁻¹,x)} | x ∈ Fq^n, 1 ≤ wH(x) ≤ ⌊(n+1)/2⌋}
let M_inv := M⁻¹
let hM_inv : IsUnit M_inv.det := by
  rw [Matrix.det_nonsing_inv]
  exact hM.ringInverse
{ y | ∃ (x : Fin n → GaloisField p q) (hx_weight : 1 ≤ wH x ∧ wH x ≤ (n + 1) / 2),
    y = min (h M hM x (nonzero_of_pos_weight x hx_weight.1))
        (h M_inv hM_inv x (nonzero_of_pos_weight x hx_weight.1)) }.toFinset.min'
(by
  rw [Set.toFinset_nonempty]
  -- Use the existing nonemptiness proof for low weight vectors
  obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
  have hx_weight : 1 ≤ wH x ∧ wH x ≤ (n + 1) / 2 := by
    rw [low_weight_vectors] at hx; simp at hx; exact hx
  use min (h M hM x (nonzero_of_pos_weight x hx_weight.1))
          (h M_inv hM_inv x (nonzero_of_pos_weight x hx_weight.1))
  simp only [Set.mem_setOf_eq]
  exact ⟨x, hx_weight, rfl⟩
)

-- ========================================
-- SECTION: MINOR THEOREMS
-- ========================================


-- ----------------------------------------
-- Step 1: Partition Formula
-- ----------------------------------------
-- B(M) = min{ min{h(M,x) | 1≤wH(x)≤⌊(n+1)/2⌋}, min{h(M,x) | ⌊(n+1)/2⌋ < wH(x) ≤ n}}
theorem step1
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit (M.det))
:
Branchnumber M hM = min
    ({ wH x + wH (M.mulVec x) | x ∈ low_weight_vectors }.toFinset.min'
      (low_weight_branch_values_nonempty M))
    ({ wH x + wH (M.mulVec x) | x ∈ high_weight_vectors }.toFinset.min'
      (high_weight_branch_values_nonempty M)) := by

  -- Partition nonzero vectors into low and high weight sets
  have h_partition_cover := @nonzero_vectors_partition p q n _ _ _
  have h_image_eq : { wH x + wH (M.mulVec x) | x ∈ (@nonzero_vectors p q n _ _ _) } =
    { wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) ∪ (@high_weight_vectors p q n _ _ _) } := by
    rw [h_partition_cover]
  rw [Branchnumber]
  simp only [h_image_eq]

  -- min over union = min of mins
  have h_min_union : { wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) ∪ (@high_weight_vectors p q n _ _ _) }.toFinset.min'
    (by rw [Set.toFinset_nonempty, ← h_partition_cover];
        obtain ⟨x, hx⟩ := @nonzero_vectors_nonempty p q n _ _ _
        use wH x + wH (M.mulVec x)
        simp only [Set.mem_setOf_eq]
        exact ⟨x, hx, rfl⟩) =
    min
      ({ wH x + wH (M.mulVec x) | x ∈ low_weight_vectors }.toFinset.min'
        (low_weight_branch_values_nonempty M))
      ({ wH x + wH (M.mulVec x) | x ∈ high_weight_vectors }.toFinset.min'
        (high_weight_branch_values_nonempty M)) := by
    -- Image of union = union of images
    have h_image_union : { wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) ∪ (@high_weight_vectors p q n _ _ _) } =
      { wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) } ∪
      { wH x + wH (M.mulVec x) | x ∈ (@high_weight_vectors p q n _ _ _) } := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_union, Finset.mem_union]
      constructor
      · intro ⟨x, hx_union, hxy⟩
        cases hx_union with
        | inl h_low => left; exact ⟨x, h_low, hxy⟩
        | inr h_high => right; exact ⟨x, h_high, hxy⟩
      · intro h_union
        cases h_union with
        | inl h_left =>
          obtain ⟨x, h_low, hxy⟩ := h_left
          exact ⟨x, Or.inl h_low, hxy⟩
        | inr h_right =>
          obtain ⟨x, h_high, hxy⟩ := h_right
          exact ⟨x, Or.inr h_high, hxy⟩

    simp only [h_image_union, Set.toFinset_union]
    apply Finset.min'_union
  exact h_min_union

-- ----------------------------------------
-- Step 2: High Weight Partition
-- ----------------------------------------
-- min{h(M,x) | high weight} = min{min{h(M,x) | high wH(x), low wH(Mx)}, min{h(M,x) | high wH(x), high wH(Mx)}}
theorem step2
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(_hM : IsUnit (M.det))
(h_first_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 }.Nonempty)
(h_second_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 }.Nonempty)
:
{ wH x + wH (M.mulVec x) | x ∈ (@high_weight_vectors p q n _ _ _) }.toFinset.min'
  (high_weight_branch_values_nonempty M) =
min
  ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min'
    (by rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_first_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩))
  ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min'
    (by rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_second_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) := by
  have h_partition : (@high_weight_vectors p q n _ _ _) =
    { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } ∪
    { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } := by
    ext x; simp; constructor
    · intro hx; by_cases h : wH (M.mulVec x) ≤ (n + 1) / 2
      · left; exact ⟨hx, h⟩
      · right; exact ⟨hx, lt_of_not_ge h⟩
    · intro h; cases h with | inl h => exact h.1 | inr h => exact h.1
  have h_image_eq : { wH x + wH (M.mulVec x) | x ∈ (@high_weight_vectors p q n _ _ _) } =
    { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } ∪
    { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } } := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_union]; constructor
    · intro ⟨x, hx, hxz⟩
      by_cases h : wH (M.mulVec x) ≤ (n + 1) / 2
      · left; use x; simp; exact ⟨⟨hx, h⟩, hxz⟩
      · right; use x; simp; exact ⟨⟨hx, lt_of_not_ge h⟩, hxz⟩
    · intro h; cases h with
      | inl h_left => simp at h_left; obtain ⟨x, ⟨hx, _⟩, hxz⟩ := h_left; use x, hx, hxz
      | inr h_right => simp at h_right; obtain ⟨x, ⟨hx, _⟩, hxz⟩ := h_right; use x, hx, hxz
  simp only [h_image_eq, Set.toFinset_union]
  exact Finset.min'_union _ _



-- ----------------------------------------
-- Step 3: Partition Formula
-- ----------------------------------------
-- Theorem: Branch number upper bound
theorem branch_number_upper_bound
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit (M.det))
:
Branchnumber M hM ≤ n + 1 := by
  have h_nonempty : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.lt_trans (Nat.zero_lt_one) (Fact.out : 1 < n))
  cases' h_nonempty with i₀
  have h_props := @standard_basis_vector_properties p q n _ _ _ i₀
  let e := fun i : Fin n => if i = i₀ then (1 : GaloisField p q) else 0
  have h_e_nonzero : e ≠ 0 := h_props.1
  have h_wH_e : wH e = 1 := h_props.2
  have h_branch_bound : wH e + wH (M.mulVec e) ≤ n + 1 := by
    calc wH e + wH (M.mulVec e)
      = 1 + wH (M.mulVec e) := by rw [h_wH_e]
      _ ≤ 1 + n := by linarith [wH_le_n (M.mulVec e)]
      _ = n + 1 := by ring
  simp only [Branchnumber]
  have h_e_in_set : e ∈ (@nonzero_vectors p q n _ _ _) := by
    simp [nonzero_vectors, h_e_nonzero]
  have h_value_in_image : wH e + wH (M.mulVec e) ∈ { wH x + wH (M.mulVec x) | x ∈ (@nonzero_vectors p q n _ _ _) } := by
    simp only [Set.mem_setOf_eq]
    exact ⟨e, h_e_in_set, rfl⟩
  have h_min_le : { wH x + wH (M.mulVec x) | x ∈ (@nonzero_vectors p q n _ _ _) }.toFinset.min' (by
      rw [Set.toFinset_nonempty]
      obtain ⟨x, hx⟩ := @nonzero_vectors_nonempty p q n _ _ _
      use wH x + wH (M.mulVec x)
      simp only [Set.mem_setOf_eq]
      exact ⟨x, hx, rfl⟩) ≤ wH e + wH (M.mulVec e) := by
    apply Finset.min'_le
    rwa [Set.mem_toFinset]
  linarith [h_min_le, h_branch_bound]


-- ----------------------------------------
-- Step 3: Partition Formula
-- ----------------------------------------
-- Theorem: The second term exceeds the upper bound
theorem second_term_strictly_exceeds_upper_bound
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(_hM : IsUnit (M.det))
(h_second_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 }.Nonempty)
:
(
  { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min'
  (high_weight_high_image_branch_values_nonempty M h_second_set_nonempty)
)
> n + 1 := by
  have h_all_large : ∀ b ∈ { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset, b > n + 1 := by
    intro b hb
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hb
    obtain ⟨x, hx_mem, hb_eq⟩ := hb
    rw [← hb_eq]
    simp at hx_mem
    have h_x_in_high : x ∈ (@high_weight_vectors p q n _ _ _) := hx_mem.1
    have h_mx_large : wH (M.mulVec x) > (n + 1) / 2 := hx_mem.2
    simp [high_weight_vectors] at h_x_in_high
    have h_x_bound := nat_gt_floor_bound (wH x) n h_x_in_high.1
    have h_mx_bound := nat_gt_floor_bound (wH (M.mulVec x)) n h_mx_large
    calc wH x + wH (M.mulVec x)
      ≥ ((n + 1) / 2 + 1) + ((n + 1) / 2 + 1) := by linarith [h_x_bound, h_mx_bound]
      _ = 2 * ((n + 1) / 2) + 2 := by ring
      _ ≥ n + 2 := by linarith [floor_arithmetic_bound n]
      _ > n + 1 := by omega
  exact h_all_large _ (Finset.min'_mem _ _)


-- ----------------------------------------
-- Step 3: Partition Formula
-- ----------------------------------------
-- Theorem: The second term in the high weight partition does not contribute to the minimum
theorem second_term_irrelevant_for_branch_number
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit (M.det))
(h_first_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 }.Nonempty)
(h_second_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 }.Nonempty)
:
Branchnumber M hM = min
  ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min'
    (low_weight_branch_values_nonempty M))
  ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min'
    (high_weight_low_image_branch_values_nonempty M h_first_set_nonempty)) := by
  have h_second_large := second_term_strictly_exceeds_upper_bound M hM h_second_set_nonempty
  have h_upper := branch_number_upper_bound M hM
  have h_three_way := step1 M hM
  have h_high_partition := step2 M hM h_first_set_nonempty h_second_set_nonempty
  by_cases h_case : ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_first_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) ≤ ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_second_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩))
  · rw [h_three_way, h_high_partition]
    rw [min_eq_left h_case]
  · push_neg at h_case
    have h_min_cd_eq_d : min ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_first_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_second_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) = ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_second_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) := by
      exact min_eq_right (le_of_lt h_case)
    have h_min_cd_large : min ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_first_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_second_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) > n + 1 := by
      rw [h_min_cd_eq_d]; exact h_second_large
    have h_a_eq_b : Branchnumber M hM = ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) := by
      rw [h_three_way, h_high_partition, h_min_cd_eq_d]
      have h_cd_gt : min ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
        rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_first_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min' (by
        rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_second_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) > n + 1 := h_min_cd_large
      rw [h_min_cd_eq_d] at h_cd_gt
      have h_b_le : ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
        rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) ≤ n + 1 := by
        by_contra h_not
        push_neg at h_not
        have h_min_gt : min ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
          rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩))
                            (min ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
          rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_first_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩))
                                 ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min' (by
          rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_second_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩))) > n + 1 := by
          exact lt_min h_not h_min_cd_large
        have h_a_gt : Branchnumber M hM > n + 1 := by
          rw [h_three_way, h_high_partition]
          exact h_min_gt
        exact not_le.mpr h_a_gt h_upper
      exact min_eq_left (le_of_lt (lt_of_le_of_lt h_b_le h_cd_gt))
    rw [h_a_eq_b]
    have h_c_large : ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_first_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) > n + 1 := by
      exact lt_trans h_second_large h_case
    have h_b_le : ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) ≤ n + 1 := by
      rw [← h_a_eq_b]; exact h_upper
    have h_b_lt_c : ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) < ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
      rw [Set.toFinset_nonempty]; obtain ⟨x, hx⟩ := h_first_set_nonempty; use wH x + wH (M.mulVec x); simp only [Set.mem_setOf_eq]; exact ⟨x, hx, rfl⟩)) := lt_of_le_of_lt h_b_le h_c_large
    exact (min_eq_left (le_of_lt h_b_lt_c)).symm



-- ----------------------------------------
-- Step 4: Partition Formula
-- ----------------------------------------

-- Observation: Low-weight vectors with low-weight outputs form a subset
lemma low_weight_with_constraint_subset
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
:
{ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } ⊆
{ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) } := by
  -- This follows directly from the definition: adding a constraint can only make the set smaller
  intro h hh
  simp only [Set.mem_setOf_eq] at hh ⊢
  obtain ⟨x, hx_mem, hx_eq⟩ := hh
  use x
  simp at hx_mem
  exact ⟨hx_mem.1, hx_eq⟩


-- Theorem: Equation 4 - Formalized using explicit finite sets to avoid Fintype issues
-- This represents: min{h(M,x) | x ∈ low_weight} ≤ min{h(M,x) | x ∈ low_weight, wH(Mx) ≤ ⌊(n+1)/2⌋}
theorem low_weight_min_inequality
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(low_min : ℕ)
(constrained_min : ℕ)
(h_low_min : low_min = ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
  rw [Set.toFinset_nonempty]
  obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
  use wH x + wH (M.mulVec x)
  simp only [Set.mem_setOf_eq]
  exact ⟨x, hx, rfl⟩)))
(h_constrained_min : constrained_min ∈ { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } })
:
low_min ≤ constrained_min := by
  rw [h_low_min]
  apply Finset.min'_le
  rw [Set.mem_toFinset]
  exact low_weight_with_constraint_subset M h_constrained_min




-- ----------------------------------------
-- Step 4: Partition Formula
-- ----------------------------------------
-- Theorem: The second term in the high weight partition does not contribute to the minimum
theorem branchnumber_with_extra_term
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(_hM : IsUnit (M.det))
(h_first_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 }.Nonempty)
(h_constrained_low_nonempty : ({ x ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec x) ≤ (n + 1) / 2 }).Nonempty)
:
min
  ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    exact ⟨x, hx, rfl⟩))
  ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := h_first_set_nonempty
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    use x)) =
({({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    exact ⟨x, hx, rfl⟩)),
  ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    have h_converted : { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.Nonempty := by
      obtain ⟨x, hx⟩ := h_constrained_low_nonempty
      use wH x + wH (M.mulVec x)
      simp only [Set.mem_setOf_eq]
      use x
    exact h_converted)),
  ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := h_first_set_nonempty
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    use x))} : Finset ℕ).min' (by simp) := by
  -- Let A, B, C be the three terms for readability
  let A := ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    exact ⟨x, hx, rfl⟩))
  let B := ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    have h_converted : { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.Nonempty := by
      obtain ⟨x, hx⟩ := h_constrained_low_nonempty
      use wH x + wH (M.mulVec x)
      simp only [Set.mem_setOf_eq]
      use x
    exact h_converted))
  let C := ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := h_first_set_nonempty
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    use x))

  have h_A_le_B : A ≤ B := by
    apply low_weight_min_inequality M A B
    · rfl
    · simp only [Set.mem_setOf_eq]
      have h_min_mem : B ∈ { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset := by
        apply Finset.min'_mem
      rw [Set.mem_toFinset] at h_min_mem
      simp only [Set.mem_setOf_eq] at h_min_mem
      exact h_min_mem

  show min A C = ({A, B, C} : Finset ℕ).min' (by simp)

  have h_finset_eq : ({A, B, C} : Finset ℕ).min' (by simp) = min A C := by
    rw [finset_min_three_elements]
    rw [← min_assoc, Nat.min_eq_left h_A_le_B]

  exact h_finset_eq.symm




-- ----------------------------------------
-- Step 5: Union over union equals union of unions
-- ----------------------------------------
-- Theorem: The second term in the high weight partition does not contribute to the minimum

lemma min_union_eq_min_mins {α : Type*} [LinearOrder α] (A B C : Finset α)
  (hA : A = B ∪ C) (hB_nonempty : B.Nonempty) (hC_nonempty : C.Nonempty)
  (hA_nonempty : A.Nonempty) :
  A.min' hA_nonempty = min (B.min' hB_nonempty) (C.min' hC_nonempty) := by
  apply le_antisymm
  · apply le_min
    · apply Finset.min'_le
      rw [hA]
      exact Finset.mem_union_left C (Finset.min'_mem B hB_nonempty)
    · apply Finset.min'_le
      rw [hA]
      exact Finset.mem_union_right B (Finset.min'_mem C hC_nonempty)
  · have h_min_mem : A.min' hA_nonempty ∈ A := Finset.min'_mem A hA_nonempty
    have h_min_in_union : A.min' hA_nonempty ∈ B ∪ C := by
      rwa [← hA]
    simp [Finset.mem_union] at h_min_in_union
    cases' h_min_in_union with h_in_B h_in_C
    · have h_B_le_A : B.min' hB_nonempty ≤ A.min' hA_nonempty :=
        Finset.min'_le B (A.min' hA_nonempty) h_in_B
      exact le_trans (min_le_left _ _) h_B_le_A
    · have h_C_le_A : C.min' hC_nonempty ≤ A.min' hA_nonempty :=
        Finset.min'_le C (A.min' hA_nonempty) h_in_C
      exact le_trans (min_le_right _ _) h_C_le_A

-- Lemma: Partition of constrained nonzero vectors into low and high weight
lemma constrained_nonzero_partition {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) :
  { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@nonzero_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } =
  { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } ∪
  { wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } := by
  ext val
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro ⟨y, hy_mem, hy_eq⟩
    simp at hy_mem
    have hy_in_nonzero : y ≠ 0 := by
      simp [nonzero_vectors] at hy_mem
      exact hy_mem.1
    have hy_constraint : wH (M.mulVec y) ≤ (n + 1) / 2 := hy_mem.2
    have hy_partition := weight_partition_covers y hy_in_nonzero
    cases hy_partition with
    | inl h_low =>
      left
      use y
      simp
      exact ⟨⟨h_low, hy_constraint⟩, hy_eq⟩
    | inr h_high =>
      right
      use y
      simp
      exact ⟨⟨h_high, hy_constraint⟩, hy_eq⟩
  · intro h
    cases h with
    | inl h_left =>
      obtain ⟨y, hy_mem, hy_eq⟩ := h_left
      use y
      simp at hy_mem ⊢
      exact ⟨⟨by simp [nonzero_vectors]; exact low_weight_vectors_mem_nonzero hy_mem.1, hy_mem.2⟩, hy_eq⟩
    | inr h_right =>
      obtain ⟨y, hy_mem, hy_eq⟩ := h_right
      use y
      simp at hy_mem ⊢
      exact ⟨⟨by simp [nonzero_vectors]; exact high_weight_vectors_mem_nonzero hy_mem.1, hy_mem.2⟩, hy_eq⟩




-- ----------------------------------------
-- Step 6: Matrix relations
-- ----------------------------------------

-- Matrix inverse relation: Mx = y ⟹ x = M⁻¹y
lemma matrix_inverse_relation {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) (hM : IsUnit M.det) :
  ∀ (x y : Fin n → GaloisField p q), M.mulVec x = y → x = (M⁻¹).mulVec y := by
  intro x y h_eq
  have h_inv_mul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hM
  calc x
    = (1 : Matrix (Fin n) (Fin n) (GaloisField p q)).mulVec x := by rw [Matrix.one_mulVec]
    _ = (M⁻¹ * M).mulVec x := by rw [← h_inv_mul]
    _ = M⁻¹.mulVec (M.mulVec x) := by rw [Matrix.mulVec_mulVec]
    _ = M⁻¹.mulVec y := by rw [h_eq]

-- Nonzero preservation: x ≠ 0 ↔ y ≠ 0 when Mx = y (since M is invertible)
lemma nonzero_equivalence {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) (hM : IsUnit M.det) :
  ∀ (x y : Fin n → GaloisField p q), M.mulVec x = y → (x ≠ 0 ↔ y ≠ 0) := by
  intro x y h_eq
  constructor
  · intro hx_nonzero hy_zero
    have h_zero : M.mulVec x = 0 := by rwa [h_eq]
    have h_injective : Function.Injective M.mulVec := by
      intro u v huv
      have h_diff : M.mulVec (u - v) = 0 := by
        rw [Matrix.mulVec_sub, huv, sub_self]
      have h_ker_trivial : ∀ w, M.mulVec w = 0 → w = 0 := by
        intro w hw
        have h_inv_mul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hM
        calc w
          = (1 : Matrix (Fin n) (Fin n) (GaloisField p q)).mulVec w := by rw [Matrix.one_mulVec]
          _ = (M⁻¹ * M).mulVec w := by rw [← h_inv_mul]
          _ = M⁻¹.mulVec (M.mulVec w) := by rw [Matrix.mulVec_mulVec]
          _ = M⁻¹.mulVec 0 := by rw [hw]
          _ = 0 := by rw [Matrix.mulVec_zero]
      have h_uv_zero : u - v = 0 := h_ker_trivial (u - v) h_diff
      exact sub_eq_zero.mp h_uv_zero
    have h_x_zero : x = 0 := by
      apply h_injective
      rw [h_zero, Matrix.mulVec_zero]
    exact hx_nonzero h_x_zero
  · intro hy_nonzero hx_zero
    have h_zero : y = 0 := by rw [← h_eq, hx_zero, Matrix.mulVec_zero]
    exact hy_nonzero h_zero

-- Branch function equivalence: h(M,x) = h(M⁻¹,y) when Mx = y
lemma branch_function_equivalence {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) (hM : IsUnit M.det) :
  ∀ (x y : Fin n → GaloisField p q) (hx : x ≠ 0) (hy : y ≠ 0),
  M.mulVec x = y →
  h M hM x hx = h (M⁻¹) (by rw [Matrix.det_nonsing_inv]; exact hM.ringInverse) y hy := by
  intro x y hx hy h_eq
  simp only [h]
  have h_x_eq : x = (M⁻¹).mulVec y := matrix_inverse_relation M hM x y h_eq
  rw [h_x_eq]
  have h_m_minv_y : M.mulVec (M⁻¹.mulVec y) = y := by
    have h_mul_inv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
    calc M.mulVec (M⁻¹.mulVec y)
      = (M * M⁻¹).mulVec y := by rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) (GaloisField p q)).mulVec y := by rw [h_mul_inv]
      _ = y := by rw [Matrix.one_mulVec]
  rw [h_m_minv_y, add_comm]






-- Nonemptiness of matrix inverse constrained set
lemma matrix_inverse_constrained_nonempty {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) (hM : IsUnit M.det) :
  { wH y + wH (M⁻¹.mulVec y) | y ∈ { y | ∃ x, M.mulVec x = y ∧
                    1 ≤ wH x ∧ wH x ≤ n ∧
                    1 ≤ wH y ∧ wH y ≤ (n + 1) / 2 } }.toFinset.Nonempty := by
  rw [Set.toFinset_nonempty]
  -- Use a standard basis vector approach
  have h_nonempty : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.lt_trans (Nat.zero_lt_one) (Fact.out : 1 < n))
  cases' h_nonempty with i₀
  let y_vec := fun i : Fin n => if i = i₀ then (1 : GaloisField p q) else 0
  let x_vec := (M⁻¹).mulVec y_vec
  use (wH y_vec + wH (M⁻¹.mulVec y_vec))
  simp only [Set.mem_setOf_eq]
  use y_vec
  constructor
  · use x_vec
    constructor
    · calc M.mulVec x_vec
        = M.mulVec ((M⁻¹).mulVec y_vec) := rfl
        _ = (M * M⁻¹).mulVec y_vec := by rw [Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin n) (Fin n) (GaloisField p q)).mulVec y_vec := by rw [Matrix.mul_nonsing_inv M hM]
        _ = y_vec := by rw [Matrix.one_mulVec]
    constructor
    · have hy_nonzero : y_vec ≠ 0 := by
        simp only [y_vec]
        intro h_eq_zero
        have h_at_i₀ : (1 : GaloisField p q) = 0 := by
          have h_apply := congr_fun h_eq_zero i₀
          simp at h_apply
        exact one_ne_zero h_at_i₀
      have hx_nonzero : x_vec ≠ 0 := (nonzero_equivalence M hM x_vec y_vec (by
        calc M.mulVec x_vec
          = M.mulVec ((M⁻¹).mulVec y_vec) := rfl
          _ = (M * M⁻¹).mulVec y_vec := by rw [Matrix.mulVec_mulVec]
          _ = (1 : Matrix (Fin n) (Fin n) (GaloisField p q)).mulVec y_vec := by rw [Matrix.mul_nonsing_inv M hM]
          _ = y_vec := by rw [Matrix.one_mulVec])).mpr hy_nonzero
      exact nonzero_hamming_weight_pos x_vec hx_nonzero
    constructor
    · exact wH_le_n x_vec
    constructor
    · simp only [wH, y_vec]
      have h_filter_eq : Finset.univ.filter (fun i => (if i = i₀ then (1 : GaloisField p q) else 0) ≠ 0) = {i₀} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        split_ifs with h
        · simp [h]
        · simp; exact h
      rw [h_filter_eq, Finset.card_singleton]
    · simp only [wH, y_vec]
      have h_filter_eq : Finset.univ.filter (fun i => (if i = i₀ then (1 : GaloisField p q) else 0) ≠ 0) = {i₀} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        split_ifs with h
        · simp [h]
        · simp; exact h
      rw [h_filter_eq, Finset.card_singleton]
      have h_n_pos : 1 < n := Fact.out
      cases' n with n'
      · contradiction
      · cases' n' with n''
        · simp
        · have h_ge_two : 2 ≤ n'' + 1 + 1 + 1 := by linarith
          exact Nat.succ_le_iff.mpr (Nat.div_pos h_ge_two (by norm_num))
  · rfl


-- ----------------------------------------
-- Step 7: Drop trivial conditions
-- ----------------------------------------
-- Nonemptiness of simplified weight-constrained set
lemma weight_constrained_nonempty {p q n : ℕ} [Fact p.Prime] [Fact (0 < q)] [Fact (1 < n)]
  (M : Matrix (Fin n) (Fin n) (GaloisField p q)) :
  { x | ∃ y ∈ {y | 1 ≤ wH y ∧ wH y ≤ (n + 1) / 2}, wH y + wH (M⁻¹.mulVec y) = x }.toFinset.Nonempty := by
  rw [Set.toFinset_nonempty]
  have h_nonempty : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.lt_trans (Nat.zero_lt_one) (Fact.out : 1 < n))
  cases' h_nonempty with i₀
  let y := fun i : Fin n => if i = i₀ then (1 : GaloisField p q) else 0
  use (wH y + wH (M⁻¹.mulVec y))
  simp only [Set.mem_setOf_eq]
  use y
  constructor
  · constructor
    · simp only [wH, y]
      have h_filter_eq : Finset.univ.filter (fun i => (if i = i₀ then (1 : GaloisField p q) else 0) ≠ 0) = {i₀} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        split_ifs with h
        · simp [h]
        · simp; exact h
      rw [h_filter_eq, Finset.card_singleton]
    · simp only [wH, y]
      have h_filter_eq : Finset.univ.filter (fun i => (if i = i₀ then (1 : GaloisField p q) else 0) ≠ 0) = {i₀} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        split_ifs with h
        · simp [h]
        · simp; exact h
      rw [h_filter_eq, Finset.card_singleton]
      have h_n_pos : 1 < n := Fact.out
      cases' n with n'; · contradiction
      cases' n' with n''; · simp
      have h_ge_two : 2 ≤ n'' + 1 + 1 + 1 := by linarith
      exact Nat.succ_le_iff.mpr (Nat.div_pos h_ge_two (by norm_num))
  · rfl

-- Branch number reformulation using matrix inverse
lemma branch_number_matrix_inverse_reformulation
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit M.det)
(h_constrained_low_nonempty : {x ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec x) ≤ (n + 1) / 2}.Nonempty) :
({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@nonzero_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := h_constrained_low_nonempty
    simp at hx
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    use x
    constructor
    · have hx_nonzero : x ∈ nonzero_vectors := by
        simp [nonzero_vectors]
        exact low_weight_vectors_mem_nonzero hx.1
      simp
      exact ⟨hx_nonzero, hx.2⟩
    · rfl)) =
  ({ wH y + wH (M⁻¹.mulVec y) | y ∈ { y | ∃ x, M.mulVec x = y ∧
                    1 ≤ wH x ∧ wH x ≤ n ∧
                    1 ≤ wH y ∧ wH y ≤ (n + 1) / 2 } }.toFinset.min' (by
      -- This set is nonempty since we can find suitable (x,y) with Mx = y
      exact matrix_inverse_constrained_nonempty M hM)) := by
  -- Prove set equality and apply min_finset_min_eq
  have h_sets_eq : { wH x_1 + wH (M.mulVec x_1) | x_1 ∈ { y ∈ (@nonzero_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } } =
    { wH y + wH (M⁻¹.mulVec y) | y ∈ { y | ∃ x, M.mulVec x = y ∧ 1 ≤ wH x ∧ wH x ≤ n ∧ 1 ≤ wH y ∧ wH y ≤ (n + 1) / 2 } } := by
    ext w
    constructor
    · intro hw_left
      simp only [Set.mem_setOf_eq] at hw_left ⊢
      obtain ⟨x_1, hx1_mem, hx1_eq⟩ := hw_left
      simp at hx1_mem
      have hx1_nonzero : x_1 ∈ (@nonzero_vectors p q n _ _ _) := hx1_mem.1
      have hx1_constraint : wH (M.mulVec x_1) ≤ (n + 1) / 2 := hx1_mem.2
      let y := M.mulVec x_1
      use y
      constructor
      · use x_1
        constructor
        · rfl
        constructor
        · have hx1_ne_zero : x_1 ≠ 0 := by simpa [nonzero_vectors] using hx1_nonzero
          exact nonzero_hamming_weight_pos x_1 hx1_ne_zero
        constructor
        · exact wH_le_n x_1
        constructor
        · simp only [y]
          have hy_nonzero : M.mulVec x_1 ≠ 0 := by
            intro h_zero
            have : x_1 = 0 := by
              have h_inv_mul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hM
              calc x_1
                = (1 : Matrix (Fin n) (Fin n) (GaloisField p q)).mulVec x_1 := by rw [Matrix.one_mulVec]
                _ = (M⁻¹ * M).mulVec x_1 := by rw [← h_inv_mul]
                _ = M⁻¹.mulVec (M.mulVec x_1) := by rw [Matrix.mulVec_mulVec]
                _ = M⁻¹.mulVec 0 := by rw [h_zero]
                _ = 0 := by rw [Matrix.mulVec_zero]
            have hx1_ne_zero : x_1 ≠ 0 := by simpa [nonzero_vectors] using hx1_nonzero
            exact hx1_ne_zero this
          exact nonzero_hamming_weight_pos (M.mulVec x_1) hy_nonzero
        · simp only [y]; exact hx1_constraint
      · simp only [y]
        have h_inv_y : M⁻¹.mulVec y = x_1 := by
          simp only [y]
          exact (matrix_inverse_relation M hM x_1 (M.mulVec x_1) rfl).symm
        rw [h_inv_y, add_comm]
        exact hx1_eq
    · intro hw_right
      simp only [Set.mem_setOf_eq] at hw_right ⊢
      obtain ⟨y, hy_mem, hy_eq⟩ := hw_right
      obtain ⟨x, hx_eq, hx_wt_low, hx_wt_high, hy_wt_low, hy_wt_high⟩ := hy_mem
      have hx_eq_inv : x = M⁻¹.mulVec y := matrix_inverse_relation M hM x y hx_eq
      use x
      constructor
      · simp
        constructor
        · simp [nonzero_vectors]
          intro h_zero
          rw [h_zero] at hx_wt_low
          have h_zero_weight : wH (0 : Fin n → GaloisField p q) = 0 := by simp [wH]
          rw [h_zero_weight] at hx_wt_low
          exact Nat.not_le.mpr (Nat.zero_lt_one) hx_wt_low
        · rw [hx_eq]
          exact hy_wt_high
      · rw [hx_eq, hx_eq_inv, add_comm]
        exact hy_eq
  -- Apply the finset equality lemma
  congr 1
  rw [Set.toFinset_inj]
  exact h_sets_eq



-- Lemma showing equivalence between our direct definition and Branchnumber_efficient
lemma min_distribution_set_eq_branchnumber_efficient
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit M.det) :
(low_weight_vectors.image (fun x => min (wH x + wH (M.mulVec x)) (wH x + wH (M⁻¹.mulVec x)))).min'
  (by simp [Finset.image_nonempty]; exact low_weight_vectors_nonempty) =
Branchnumber_efficient M hM := by
  unfold Branchnumber_efficient
  congr 1
  ext y
  simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · intro ⟨x, hx_mem, hy_eq⟩
    use x
    have hx_weight : 1 ≤ wH x ∧ wH x ≤ (n + 1) / 2 := by
      rwa [← mem_low_weight_vectors_iff]
    use hx_weight
    rw [← hy_eq]
    rfl
  · intro ⟨x, hx_weight, hy_eq⟩
    use x
    constructor
    · rwa [mem_low_weight_vectors_iff]
    · rw [hy_eq]
      rfl

-- Fintype instance for the min-distribution set
noncomputable instance min_distribution_set_fintype
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(_hM : IsUnit M.det)
:
Fintype {y | ∃ x ∈ low_weight_vectors, y = min (wH x + wH (M.mulVec x)) (wH x + wH (M⁻¹.mulVec x))} := by
  have h_eq : {y | ∃ x ∈ low_weight_vectors, y = min (wH x + wH (M.mulVec x)) (wH x + wH (M⁻¹.mulVec x))} =
              ↑(low_weight_vectors.image (fun x => min (wH x + wH (M.mulVec x)) (wH x + wH (M⁻¹.mulVec x)))) := by
    ext y
    simp only [Finset.mem_coe, Finset.mem_image]
    constructor
    · intro ⟨x, hx_mem, hx_eq⟩
      exact ⟨x, hx_mem, hx_eq.symm⟩
    · intro ⟨x, hx_mem, hx_eq⟩
      exact ⟨x, hx_mem, hx_eq.symm⟩
  rw [h_eq]
  infer_instance

-- The main min-distribution identity theorem
lemma min_distribution_identity
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit M.det) :
min
  ({x | ∃ x_1 ∈ low_weight_vectors, wH x_1 + wH (M.mulVec x_1) = x}.toFinset.min'
    (by rw [Set.toFinset_nonempty]
        obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
        use wH x + wH (M.mulVec x)
        use x, hx))
  ({x | ∃ x_1 ∈ low_weight_vectors, wH x_1 + wH (M⁻¹.mulVec x_1) = x}.toFinset.min'
    (by rw [Set.toFinset_nonempty]
        obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
        use wH x + wH (M⁻¹.mulVec x)
        use x, hx)) =
Branchnumber_efficient M hM := by
  rw [← min_distribution_set_eq_branchnumber_efficient M hM]
  apply le_antisymm
  · let A := {x | ∃ x_1 ∈ low_weight_vectors, wH x_1 + wH (M.mulVec x_1) = x}
    let B := {x | ∃ x_1 ∈ low_weight_vectors, wH x_1 + wH (M⁻¹.mulVec x_1) = x}
    let C := low_weight_vectors.image (fun x => min (wH x + wH (M.mulVec x)) (wH x + wH (M⁻¹.mulVec x)))
    have hA_nonempty : A.toFinset.Nonempty := by
      rw [Set.toFinset_nonempty]
      obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
      use wH x + wH (M.mulVec x), x, hx
    have hB_nonempty : B.toFinset.Nonempty := by
      rw [Set.toFinset_nonempty]
      obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
      use wH x + wH (M⁻¹.mulVec x), x, hx
    have hC_nonempty : C.Nonempty := by
      simp [C, Finset.image_nonempty]
      exact low_weight_vectors_nonempty
    by_cases h : A.toFinset.min' hA_nonempty ≤ B.toFinset.min' hB_nonempty
    · rw [min_eq_left h]
      have h_min_A : ∃ x₀, x₀ ∈ low_weight_vectors ∧ wH x₀ + wH (M.mulVec x₀) = A.toFinset.min' hA_nonempty := by
        have h_mem := Finset.min'_mem A.toFinset hA_nonempty
        rw [Set.mem_toFinset] at h_mem
        obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := h_mem
        use x₀, hx₀_mem, hx₀_eq
      obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := h_min_A
      have h_case : wH x₀ + wH (M.mulVec x₀) ≤ wH x₀ + wH (M⁻¹.mulVec x₀) := by
        have h_B_min_le : B.toFinset.min' hB_nonempty ≤ wH x₀ + wH (M⁻¹.mulVec x₀) := by
          apply Finset.min'_le
          simp [Set.mem_toFinset, B]
          use x₀, hx₀_mem
        rw [← hx₀_eq] at h
        exact le_trans h h_B_min_le
      have h_min_eq : min (wH x₀ + wH (M.mulVec x₀)) (wH x₀ + wH (M⁻¹.mulVec x₀)) = A.toFinset.min' hA_nonempty := by
        rw [min_eq_left h_case, hx₀_eq]
      have h_A_min_in_C : A.toFinset.min' hA_nonempty ∈ C := by
        rw [← h_min_eq]
        rw [Finset.mem_image]
        use x₀, hx₀_mem
      have h_C_min_le : C.min' hC_nonempty ≤ A.toFinset.min' hA_nonempty := by
        apply Finset.min'_le
        exact h_A_min_in_C
      apply Finset.le_min'
      intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨x, hx_mem, hy_eq⟩ := hy
      rw [← hy_eq]
      apply le_min
      · apply Finset.min'_le
        simp only [Set.mem_toFinset, A, Set.mem_setOf_eq]
        exact ⟨x, hx_mem, rfl⟩
      · apply le_trans h
        apply Finset.min'_le
        simp only [Set.mem_toFinset, B, Set.mem_setOf_eq]
        exact ⟨x, hx_mem, rfl⟩
    · rw [min_eq_right (le_of_not_ge h)]
      have h_min_B : ∃ x₀, x₀ ∈ low_weight_vectors ∧ wH x₀ + wH (M⁻¹.mulVec x₀) = B.toFinset.min' hB_nonempty := by
        have h_min_mem : B.toFinset.min' hB_nonempty ∈ B.toFinset := Finset.min'_mem _ hB_nonempty
        rw [Set.mem_toFinset] at h_min_mem
        simp [B] at h_min_mem
        exact h_min_mem
      obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := h_min_B
      have h_case : wH x₀ + wH (M⁻¹.mulVec x₀) ≤ wH x₀ + wH (M.mulVec x₀) := by
        have h_A_min_le : A.toFinset.min' hA_nonempty ≤ wH x₀ + wH (M.mulVec x₀) := by
          apply Finset.min'_le
          simp [Set.mem_toFinset, A]
          use x₀, hx₀_mem
        rw [← hx₀_eq] at h
        exact le_trans (le_of_not_ge h) h_A_min_le
      have h_min_eq : min (wH x₀ + wH (M.mulVec x₀)) (wH x₀ + wH (M⁻¹.mulVec x₀)) = B.toFinset.min' hB_nonempty := by
        rw [min_eq_right h_case, hx₀_eq]
      have h_B_min_in_C : B.toFinset.min' hB_nonempty ∈ C := by
        rw [← h_min_eq]
        rw [Finset.mem_image]
        use x₀, hx₀_mem
      apply Finset.le_min'
      intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨x, hx_mem, hy_eq⟩ := hy
      rw [← hy_eq]
      apply le_min
      · apply le_trans (le_of_not_ge h)
        apply Finset.min'_le
        simp only [Set.mem_toFinset, A, Set.mem_setOf_eq]
        exact ⟨x, hx_mem, rfl⟩
      · apply Finset.min'_le
        simp only [Set.mem_toFinset, B, Set.mem_setOf_eq]
        exact ⟨x, hx_mem, rfl⟩
  · let A := {x | ∃ x_1 ∈ low_weight_vectors, wH x_1 + wH (M.mulVec x_1) = x}
    let B := {x | ∃ x_1 ∈ low_weight_vectors, wH x_1 + wH (M⁻¹.mulVec x_1) = x}
    let C := low_weight_vectors.image (fun x => min (wH x + wH (M.mulVec x)) (wH x + wH (M⁻¹.mulVec x)))
    have hA_nonempty : A.toFinset.Nonempty := by
      rw [Set.toFinset_nonempty]
      obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
      use wH x + wH (M.mulVec x), x, hx
    have hB_nonempty : B.toFinset.Nonempty := by
      rw [Set.toFinset_nonempty]
      obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
      use wH x + wH (M⁻¹.mulVec x), x, hx
    apply Finset.min'_le
    by_cases h_case : A.toFinset.min' hA_nonempty ≤ B.toFinset.min' hB_nonempty
    · rw [min_eq_left h_case]
      have h_min_A : ∃ x₀, x₀ ∈ low_weight_vectors ∧ wH x₀ + wH (M.mulVec x₀) = A.toFinset.min' hA_nonempty := by
        have h_min_mem : A.toFinset.min' hA_nonempty ∈ A.toFinset := Finset.min'_mem _ hA_nonempty
        rw [Set.mem_toFinset] at h_min_mem
        simp [A] at h_min_mem
        exact h_min_mem
      obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := h_min_A
      have h_case_ineq : wH x₀ + wH (M.mulVec x₀) ≤ wH x₀ + wH (M⁻¹.mulVec x₀) := by
        have h_B_min_le : B.toFinset.min' hB_nonempty ≤ wH x₀ + wH (M⁻¹.mulVec x₀) := by
          apply Finset.min'_le
          simp [Set.mem_toFinset, B]
          use x₀, hx₀_mem
        rw [← hx₀_eq] at h_case
        exact le_trans h_case h_B_min_le
      simp only [Finset.mem_image]
      use x₀, hx₀_mem
      rw [min_eq_left h_case_ineq, hx₀_eq]
    · rw [min_eq_right (le_of_not_ge h_case)]
      have h_min_B : ∃ x₀, x₀ ∈ low_weight_vectors ∧ wH x₀ + wH (M⁻¹.mulVec x₀) = B.toFinset.min' hB_nonempty := by
        have h_min_mem : B.toFinset.min' hB_nonempty ∈ B.toFinset := Finset.min'_mem _ hB_nonempty
        rw [Set.mem_toFinset] at h_min_mem
        simp [B] at h_min_mem
        exact h_min_mem
      obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := h_min_B
      have h_case_ineq : wH x₀ + wH (M⁻¹.mulVec x₀) ≤ wH x₀ + wH (M.mulVec x₀) := by
        have h_A_min_le : A.toFinset.min' hA_nonempty ≤ wH x₀ + wH (M.mulVec x₀) := by
          apply Finset.min'_le
          simp [Set.mem_toFinset, A]
          use x₀, hx₀_mem
        rw [← hx₀_eq] at h_case
        exact le_trans (le_of_not_ge h_case) h_A_min_le
      rw [Finset.mem_image]
      use x₀, hx₀_mem
      rw [min_eq_right h_case_ineq, hx₀_eq]

-- Corollary: The main theorem expressed using Branchnumber_efficient
theorem min_distribution_identity_branchnumber
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit M.det) :
min
  ({x | ∃ x_1 ∈ low_weight_vectors, wH x_1 + wH (M.mulVec x_1) = x}.toFinset.min'
    (low_weight_branch_values_nonempty M))
  ({x | ∃ x_1 ∈ low_weight_vectors, wH x_1 + wH (M⁻¹.mulVec x_1) = x}.toFinset.min'
    (by rw [Set.toFinset_nonempty]
        obtain ⟨x, hx⟩ := @low_weight_vectors_nonempty p q n _ _ _
        use wH x + wH (M⁻¹.mulVec x)
        use x, hx)) =
Branchnumber_efficient M hM :=
min_distribution_identity M hM





-- ========================================
-- SECTION 5: MAIN THEOREM
-- ========================================
theorem branchnumber_equiv
{p q n : ℕ}
[Fact p.Prime]
[Fact (0 < q)]
[Fact (1 < n)]
(M : Matrix (Fin n) (Fin n) (GaloisField p q))
(hM : IsUnit (M.det))
:
Branchnumber M hM = Branchnumber_efficient M hM := by

-- KEY SORRIES: THE ORIGINAL PROOF USES MINIMUMS OF EMPTY FINSETS, WHICH ARE NOT DEFINED
have h_constrained_low_nonempty : ({ x ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec x) ≤ (n + 1) / 2 }).Nonempty := by sorry
have h_first_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 }.Nonempty := by sorry
have h_second_set_nonempty : { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 }.Nonempty := by sorry

-- Step 1: Apply partition by vector weight
-- We partition vectors by Hamming weight: {1,...,⌊(n+1)/2⌋} and {⌊(n+1)/2⌋+1,...,n}
-- This gives us: B(M) = min{min{h(M,x) | 1 ≤ wH(x) ≤ ⌊(n+1)/2⌋},
--                           min{h(M,x) | ⌊(n+1)/2⌋ < wH(x) ≤ n}}
have h_step1 : Branchnumber M hM = min
  ({ wH x + wH (M.mulVec x) | x ∈ low_weight_vectors }.toFinset.min' (low_weight_branch_values_nonempty M))
  ({ wH x + wH (M.mulVec x) | x ∈ high_weight_vectors }.toFinset.min' (high_weight_branch_values_nonempty M)) :=
  step1 M hM

-- Step 2: Apply partition of high weight by image weight
-- We partition vectors with ⌊(n+1)/2⌋ < wH(x) ≤ n by: wH(Mx) ≤ ⌊(n+1)/2⌋ and wH(Mx) > ⌊(n+1)/2⌋
-- This gives us: B(M) = min{min{h(M,x) | ⌊(n+1)/2⌋ < wH(x) ≤ n, wH(Mx) ≤ ⌊(n+1)/2⌋},
--                           min{h(M,x) | ⌊(n+1)/2⌋ < wH(x) ≤ n, wH(Mx) > ⌊(n+1)/2⌋}}
have h_step2 : Branchnumber M hM = min
  ({ wH x + wH (M.mulVec x) | x ∈ low_weight_vectors }.toFinset.min' (low_weight_branch_values_nonempty M))
  (min
    ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (high_weight_low_image_branch_values_nonempty M h_first_set_nonempty))
    ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) > (n + 1) / 2 } }.toFinset.min' (high_weight_high_image_branch_values_nonempty M h_second_set_nonempty))) := by
  rw [h_step1, step2 M hM h_first_set_nonempty h_second_set_nonempty]

-- Step 3: Eliminate the irrelevant term
-- We show that vectors with ⌊(n+1)/2⌋ < wH(x) ≤ n and wH(Mx) > ⌊(n+1)/2⌋ don't contribute to the minimum
-- This gives us: B(M) = min{min{h(M,x) | 1≤wH(x)≤⌊(n+1)/2⌋}, min{h(M,x) | ⌊(n+1)/2⌋ < wH(x) ≤ n, wH(Mx)≤⌊(n+1)/2⌋}}
have h_step3 : Branchnumber M hM = min
  ({ wH x + wH (M.mulVec x) | x ∈ low_weight_vectors }.toFinset.min' (low_weight_branch_values_nonempty M))
  ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (high_weight_low_image_branch_values_nonempty M h_first_set_nonempty)) := by
  exact second_term_irrelevant_for_branch_number M hM h_first_set_nonempty h_second_set_nonempty


-- Define clean variable names for the four terms
-- D represents the LaTeX definition: min{h(M,x) | x ∈ F_q^n, 1 ≤ wH(x) ≤ n, wH(Mx) ≤ ⌊(n+1)/2⌋}
let A := ({ wH x + wH (M.mulVec x) | x ∈ (@low_weight_vectors p q n _ _ _) }.toFinset.min' (low_weight_branch_values_nonempty M))
let B := ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@low_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := h_constrained_low_nonempty
    exact ⟨wH x + wH (M.mulVec x), x, hx, rfl⟩))
let C := ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@high_weight_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (high_weight_low_image_branch_values_nonempty M h_first_set_nonempty))
let D := ({ wH x + wH (M.mulVec x) | x ∈ { y ∈ (@nonzero_vectors p q n _ _ _) | wH (M.mulVec y) ≤ (n + 1) / 2 } }.toFinset.min' (by
    rw [Set.toFinset_nonempty]
    obtain ⟨x, hx⟩ := h_constrained_low_nonempty
    simp at hx
    use wH x + wH (M.mulVec x)
    simp only [Set.mem_setOf_eq]
    use x
    constructor
    · have hx_nonzero : x ∈ nonzero_vectors := by
        simp [nonzero_vectors]
        exact low_weight_vectors_mem_nonzero hx.1
      simp
      exact ⟨hx_nonzero, hx.2⟩
    · rfl))

-- Step 4: Apply the extra term transformation
-- We use branchnumber_with_extra_term to show that the binary minimum equals the ternary minimum
-- This transforms: min(A,C) = min(A,B,C) where B is the constrained low-weight term
have h_step4 : Branchnumber M hM = ({A, B, C} : Finset ℕ).min' (by simp) := by
  rw [h_step3, branchnumber_with_extra_term M hM h_first_set_nonempty h_constrained_low_nonempty]

-- Step 5: Apply finset minimum simplification using our helper lemma
have h_step5 : ({A, B, C} : Finset ℕ).min' (by simp) = min A (min B C) :=
  finset_min_three_elements A B C
rw [h_step4, h_step5]


-- Step 6: Establish D = min B C using constrained vector partition
have h_BC_subset_D : D = min B C := by
    simp only [D]
    simp_rw [constrained_nonzero_partition M, Set.toFinset_union]
    exact Finset.min'_union _ _

rw [←h_BC_subset_D]


-- Step 8: express D in a different manner
have h_branch_reformulation : D =
      ({ wH y + wH (M⁻¹.mulVec y) | y ∈ { y | ∃ x, M.mulVec x = y ∧
                    1 ≤ wH x ∧ wH x ≤ n ∧
                    1 ≤ wH y ∧ wH y ≤ (n + 1) / 2 } }.toFinset.min'
      (matrix_inverse_constrained_nonempty M hM)) :=
  branch_number_matrix_inverse_reformulation M hM h_constrained_low_nonempty

rw [h_branch_reformulation]


-- Step 8: express D in a different manner
have h_drop_trivial_condition :
  ({ x | ∃ y ∈ {y | ∃ x, M.mulVec x = y ∧ 1 ≤ wH x ∧ wH x ≤ n ∧ 1 ≤ wH y ∧ wH y ≤ (n + 1) / 2},
              wH y + wH (M⁻¹.mulVec y) = x }.toFinset.min'
      (matrix_inverse_constrained_nonempty M hM)) =
  ({ x | ∃ y ∈ {y | 1 ≤ wH y ∧ wH y ≤ (n + 1) / 2},
              wH y + wH (M⁻¹.mulVec y) = x }.toFinset.min'
      (weight_constrained_nonempty M)) := by
  congr 1; rw [Set.toFinset_inj]; ext x; simp only [Set.mem_setOf_eq]
  constructor
  · intro ⟨y, hy_mem, hy_eq⟩
    obtain ⟨x_orig, hx_orig_eq, hx_orig_pos, hx_orig_bound, hy_pos, hy_constraint⟩ := hy_mem
    use y, ⟨hy_pos, hy_constraint⟩, hy_eq
  · intro ⟨y, hy_constraints, hy_eq⟩
    obtain ⟨hy_pos, hy_constraint⟩ := hy_constraints
    use y
    constructor
    · let x := M⁻¹.mulVec y
      use x
      constructor
      · calc M.mulVec x = M.mulVec (M⁻¹.mulVec y) := rfl
          _ = (M * M⁻¹).mulVec y := by rw [Matrix.mulVec_mulVec]
          _ = (1 : Matrix (Fin n) (Fin n) (GaloisField p q)).mulVec y := by rw [Matrix.mul_nonsing_inv M hM]
          _ = y := by rw [Matrix.one_mulVec]
      constructor
      · have hy_nonzero : y ≠ 0 := by
          by_contra h_zero; simp only [wH] at hy_pos; rw [h_zero] at hy_pos; simp at hy_pos
        have hx_nonzero : x ≠ 0 := (nonzero_equivalence M hM x y (by
          calc M.mulVec x = M.mulVec (M⁻¹.mulVec y) := rfl
            _ = y := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec])).mpr hy_nonzero
        exact nonzero_hamming_weight_pos x hx_nonzero
      constructor
      · exact wH_le_n x
      constructor
      · exact hy_pos
      · exact hy_constraint
    · exact hy_eq

rw [h_drop_trivial_condition]

convert min_distribution_identity_branchnumber M hM using 1
congr 1
congr 1
ext z
simp only [Set.mem_toFinset, Set.mem_setOf_eq]
constructor
· intro ⟨y, hy_cond, hz_eq⟩
  use y
  exact ⟨(mem_low_weight_vectors_iff y).mpr hy_cond, hz_eq⟩
· intro ⟨y, hy_mem, hz_eq⟩
  use y
  exact ⟨(mem_low_weight_vectors_iff y).mp hy_mem, hz_eq⟩
