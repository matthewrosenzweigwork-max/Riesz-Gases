import HRS.MC.CepH2Defs

/-!
# CEPH2, helper 1: geometry of the cylinder and the fundamental domain `cep_cell`

`h2_perp` is a continuous linear projection, orthogonal to the diagonal; `cep_cell` is a fundamental domain of
the translation action of `ℤ (1,…,1)`; integrals over the cell of periodic functions are translation invariant
and `∫_E F = ∫_cell ∑_m F(· + m d)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- The mean of the coordinates. -/
def h2_mean (z : Ch N) : ℝ := (∑ k, z k) / (N : ℝ)

theorem h2_perp_eq (z : Ch N) : h2_perp z = z - h2_mean z • cep_diag N := rfl

theorem cep_diag_apply (k : Fin N) : (cep_diag N) k = 1 := rfl

theorem h2_mean_add_diag [NeZero N] (z : Ch N) (m : ℝ) : h2_mean (z + m • cep_diag N) = h2_mean z + m := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  unfold h2_mean
  simp only [PiLp.add_apply, PiLp.smul_apply, cep_diag_apply, smul_eq_mul, mul_one, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem h2_perp_add_diag [NeZero N] (z : Ch N) (m : ℝ) : h2_perp (z + m • cep_diag N) = h2_perp z := by
  rw [h2_perp_eq, h2_perp_eq, h2_mean_add_diag]
  ext k
  simp [add_smul]

theorem h2_mean_add (z w : Ch N) : h2_mean (z + w) = h2_mean z + h2_mean w := by
  unfold h2_mean
  simp only [PiLp.add_apply, Finset.sum_add_distrib, add_div]

theorem h2_mean_smul (c : ℝ) (z : Ch N) : h2_mean (c • z) = c * h2_mean z := by
  unfold h2_mean
  simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem h2_mean_diag [NeZero N] : h2_mean (cep_diag N) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  unfold h2_mean
  simp [cep_diag_apply]

/-- `‖z‖² = ‖P⊥ z‖² + N · mean(z)²`. -/
theorem h2_norm_sq [NeZero N] (z : Ch N) : ‖z‖ ^ 2 = ‖h2_perp z‖ ^ 2 + N * h2_mean z ^ 2 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [h2_perp_eq, PiLp.sub_apply, PiLp.smul_apply, cep_diag_apply, smul_eq_mul, mul_one, Real.norm_eq_abs,
    sq_abs]
  have hsum : ∑ k, z k = N * h2_mean z := by
    unfold h2_mean; field_simp
  have : ∑ k, (z k - h2_mean z) ^ 2 = ∑ k, z k ^ 2 - N * h2_mean z ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum, hsum]
    ring
  rw [this]; ring

theorem h2_norm_perp_le [NeZero N] (z : Ch N) : ‖h2_perp z‖ ≤ ‖z‖ := by
  have := h2_norm_sq z
  have h2 : ‖h2_perp z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [this]; nlinarith [sq_nonneg (h2_mean z), (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  exact abs_le_of_sq_le_sq' h2 (norm_nonneg _) |>.2

/-- The projection as a continuous linear map. -/
def h2_permL (N : ℕ) [NeZero N] : Ch N →L[ℝ] Ch N :=
  LinearMap.toContinuousLinearMap
    { toFun := h2_perp
      map_add' := fun z w => by
        rw [h2_perp_eq, h2_perp_eq, h2_perp_eq, h2_mean_add, add_smul]; abel
      map_smul' := fun c z => by
        rw [h2_perp_eq, h2_perp_eq, h2_mean_smul]
        simp only [RingHom.id_apply, smul_sub, smul_smul] }

theorem h2_permL_apply [NeZero N] (z : Ch N) : h2_permL N z = h2_perp z := rfl

theorem h2_continuous_perp [NeZero N] : Continuous (h2_perp : Ch N → Ch N) := (h2_permL N).continuous

theorem h2_perp_add [NeZero N] (z w : Ch N) : h2_perp (z + w) = h2_perp z + h2_perp w :=
  (h2_permL N).map_add z w

theorem h2_perp_sub [NeZero N] (z w : Ch N) : h2_perp (z - w) = h2_perp z - h2_perp w :=
  (h2_permL N).map_sub z w

/-- Points of the cell are controlled by their transverse part. -/
theorem h2_cell_norm_le [NeZero N] {z : Ch N} (hz : z ∈ cep_cell N) :
    ‖z‖ ≤ ‖h2_perp z‖ + Real.sqrt N * (1 + ‖h2_perp z‖) := by
  have h0 : |z 0| ≤ 1 := by
    obtain ⟨h1, h2⟩ := hz
    rw [abs_le]; constructor <;> linarith
  have hp0 : |(h2_perp z) 0| ≤ ‖h2_perp z‖ := by
    have := PiLp.norm_apply_le (h2_perp z) 0
    simpa using this
  have hmean : |h2_mean z| ≤ 1 + ‖h2_perp z‖ := by
    have : h2_mean z = z 0 - (h2_perp z) 0 := by
      rw [h2_perp_eq]; simp [cep_diag_apply]
    rw [this]
    calc |z 0 - (h2_perp z) 0| ≤ |z 0| + |(h2_perp z) 0| := abs_sub _ _
      _ ≤ 1 + ‖h2_perp z‖ := add_le_add h0 hp0
  have hsq := h2_norm_sq z
  have hn : ‖z‖ ^ 2 ≤ (‖h2_perp z‖ + Real.sqrt N * (1 + ‖h2_perp z‖)) ^ 2 := by
    rw [hsq]
    have hs : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
    have h3 : h2_mean z ^ 2 ≤ (1 + ‖h2_perp z‖) ^ 2 := by
      rw [← sq_abs (h2_mean z)]
      exact pow_le_pow_left₀ (abs_nonneg _) hmean 2
    have h4 : (N : ℝ) * h2_mean z ^ 2 ≤ (Real.sqrt N * (1 + ‖h2_perp z‖)) ^ 2 := by
      rw [mul_pow, hs]; exact mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg N)
    nlinarith [norm_nonneg (h2_perp z), Real.sqrt_nonneg (N : ℝ), mul_nonneg (norm_nonneg (h2_perp z))
      (mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (add_nonneg zero_le_one (norm_nonneg (h2_perp z))))]
  exact abs_le_of_sq_le_sq' hn (by positivity) |>.2

theorem h2_cell_measurable [NeZero N] : MeasurableSet (cep_cell N) := by
  have hc : Continuous fun z : Ch N => z 0 := (EuclideanSpace.proj (0 : Fin N)).continuous
  exact (measurableSet_le measurable_const hc.measurable).inter (measurableSet_lt hc.measurable measurable_const)

/-! ### The cell is a fundamental domain for `ℤ d` -/

/-- The translation subgroup `ℤ d`. -/
abbrev h2_lat (N : ℕ) : AddSubgroup (Ch N) := AddSubgroup.zmultiples (cep_diag N)

theorem cep_diag_zero [NeZero N] : (cep_diag N) 0 = 1 := rfl

theorem h2_isFD [NeZero N] : IsAddFundamentalDomain (h2_lat N) (cep_cell N) volume where
  nullMeasurableSet := h2_cell_measurable.nullMeasurableSet
  ae_covers := by
    refine Eventually.of_forall fun x => ?_
    refine ⟨⟨(-⌊x 0⌋ : ℤ) • cep_diag N, AddSubgroup.zsmul_mem_zmultiples _ _⟩, ?_⟩
    show (-⌊x 0⌋ : ℤ) • cep_diag N + x ∈ cep_cell N
    simp only [cep_cell, Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, cep_diag_apply, zsmul_eq_mul,
      Int.cast_neg, smul_eq_mul, mul_one]
    constructor
    · linarith [Int.floor_le (x 0)]
    · linarith [Int.lt_floor_add_one (x 0)]
  aedisjoint := by
    intro g₁ g₂ hne
    apply Disjoint.aedisjoint
    obtain ⟨k₁, hk₁⟩ := AddSubgroup.mem_zmultiples_iff.1 g₁.2
    obtain ⟨k₂, hk₂⟩ := AddSubgroup.mem_zmultiples_iff.1 g₂.2
    show Disjoint _ _
    rw [Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨y1, hy1, rfl⟩ := hx1
    obtain ⟨y2, hy2, hy⟩ := hx2
    have e1 : (g₁ : Ch N) = k₁ • cep_diag N := hk₁.symm
    have e2 : (g₂ : Ch N) = k₂ • cep_diag N := hk₂.symm
    change (g₂ : Ch N) + y2 = (g₁ : Ch N) + y1 at hy
    have hy0 := congrArg (fun v : Ch N => v 0) hy
    simp only [e1, e2, PiLp.add_apply, PiLp.smul_apply, cep_diag_apply, zsmul_eq_mul, smul_eq_mul,
      mul_one] at hy0
    have a1 := hy1.1; have a2 := hy1.2; have b1 := hy2.1; have b2 := hy2.2
    have : k₁ = k₂ := by
      have h1 : (k₁ : ℝ) - k₂ < 1 := by linarith
      have h2 : (k₂ : ℝ) - k₁ < 1 := by linarith
      have h1' : k₁ - k₂ < 1 := by exact_mod_cast h1
      have h2' : k₂ - k₁ < 1 := by exact_mod_cast h2
      omega
    apply hne
    apply Subtype.ext
    rw [e1, e2, this]

end HRS.MC.CepH2
