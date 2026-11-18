import HRS.MS.SA12V3N

/-!
# S.A.12 C2 (SA12V3 worker), part O: the master cell bound for the periodic initial datum

For `L ≥ 1`, `ε > 0` and every real centre `c`, the cell norm `‖χ(·-c) periodicDatum ζ η L ε φ‖_{H^m}` is bounded by
`C ∑_{z∈K} ∑_{j∈J} ‖χ(·-cellPt(k₀(z)+j)) φ‖_{H^m}`, where `K` is the finite set of lattice points within `2 + L/3`
of `c` (`|K| ≤ 7^d`), `‖(c - Lz) - cellPt(k₀ z)‖ ≤ 1/2`, and `C, J` do not depend on `L, ε, c, φ`.
Consequence: the uloc bound of C2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_pd_master {η χ ζ : Euc d → ℝ} (hη : IsMollifier η) (hχ : IsUlocCutoff χ)
    (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) (m : ℕ) :
    ∃ (J : Finset (Fin d → ℤ)) (C : ℝ), 0 < C ∧ ∀ L ε : ℝ, 1 ≤ L → 0 < ε → ∀ c : Euc d,
      ∃ (K : Finset (Fin d → ℤ)) (k₀ : (Fin d → ℤ) → (Fin d → ℤ)),
        (∀ z : Fin d → ℤ, ‖L • latticePt z - c‖ < 2 + L / 3 → z ∈ K) ∧
        (∀ z ∈ K, ‖L • latticePt z - c‖ < 2 + L / 3) ∧ (K.card : ℝ) ≤ 7 ^ d ∧
        (∀ z, ‖(c - L • latticePt z) - cellPt d (k₀ z)‖ ≤ 1 / 2) ∧
        ∀ φ : Euc d → ℝ, sa12v3_cell m χ c (periodicDatum ζ η L ε φ) ≤
          ∑ z ∈ K, ∑ j ∈ J, ENNReal.ofReal C * sa12v3_cell m χ (cellPt d (k₀ z + j)) φ := by
  obtain ⟨J, Cmoll, hCmoll, hmc⟩ := sa12v3_moll_cell hη hχ m
  obtain ⟨Cz, hCz0, hz⟩ := sa12v3_zeta_mul m hζ.1 hζ.2.1
  refine ⟨J, (Cz + 1) * Cmoll, by positivity, fun L ε hL1 hε c => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hε'0 : 0 < min ε 1 := lt_min hε one_pos
  have hε'1 : min ε 1 ≤ 1 := min_le_right _ _
  obtain ⟨B, hBmem, hBcard⟩ := sa12v3_box_card L hL0 c (2 + L / 3) (by positivity)
  have hK : ∀ z : Fin d → ℤ, ‖L • latticePt z - c‖ < 2 + L / 3 → z ∈ B := by
    intro z hz'
    refine hBmem z fun i => ?_
    have h1 := PiLp.norm_apply_le (L • latticePt z - c) i
    have e : (L • latticePt z - c) i = L * (z i : ℝ) - c i := by simp [latticePt]
    rw [e, Real.norm_eq_abs] at h1
    exact h1.trans hz'.le
  classical
  have hcard : (B.card : ℝ) ≤ 7 ^ d := by
    refine hBcard.trans ?_
    have : 2 * (2 + L / 3) / L + 2 ≤ 7 := by
      rw [div_add' _ _ _ hL0.ne', div_le_iff₀ hL0]
      nlinarith
    exact pow_le_pow_left₀ (by positivity) this d
  choose k₀ hk₀ hφ using fun z : Fin d → ℤ => hmc (min ε 1) hε'0 hε'1 (c - L • latticePt z)
  have hKf : ∀ z : Fin d → ℤ, ‖L • latticePt z - c‖ < 2 + L / 3 →
      z ∈ B.filter (fun z => ‖L • latticePt z - c‖ < 2 + L / 3) :=
    fun z hz' => Finset.mem_filter.2 ⟨hK z hz', hz'⟩
  have hcardf : ((B.filter (fun z => ‖L • latticePt z - c‖ < 2 + L / 3)).card : ℝ) ≤ 7 ^ d :=
    (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans hcard
  refine ⟨B.filter (fun z => ‖L • latticePt z - c‖ < 2 + L / 3), k₀, hKf,
    fun z hz' => (Finset.mem_filter.1 hz').2, hcardf, hk₀, fun φ => ?_⟩
  set g : Euc d → ℝ := fun x => ζ (L⁻¹ • x) * mollify η (min ε 1) φ x with hg
  have hgsupp : ∀ y : Euc d, L / 3 ≤ ‖y‖ → g y = 0 := by
    intro y hy
    by_contra hne
    have hz1 : ζ (L⁻¹ • y) ≠ 0 := fun h => hne (by simp [hg, h])
    have h1 : L⁻¹ • y ∈ Metric.ball (0 : Euc d) (1 / 3) :=
      hζ.2.2.1 (subset_tsupport _ (Function.mem_support.2 hz1))
    rw [Metric.mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL0] at h1
    have : ‖y‖ < L / 3 := by
      have := mul_lt_mul_of_pos_left h1 hL0
      rw [← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul] at this
      linarith
    linarith
  have h1 := sa12v3_perL_cell_le hχ m hL0 hgsupp c _ hKf
  have hpd : periodicDatum ζ η L ε φ = perL L g := rfl
  rw [hpd]
  refine h1.trans ?_
  refine Finset.sum_le_sum fun z _ => ?_
  have h2 : sa12v3_cell m χ (c - L • latticePt z) g ≤
      ENNReal.ofReal Cz * sa12v3_cell m χ (c - L • latticePt z) (mollify η (min ε 1) φ) := by
    unfold sa12v3_cell
    have e : (fun x => χ (x - (c - L • latticePt z)) * g x) =
        fun x => ζ (L⁻¹ • x) * (χ (x - (c - L • latticePt z)) * mollify η (min ε 1) φ x) := by
      funext x; simp only [hg]; ring
    rw [e]
    exact hz L hL1 _
  have h3 := (hφ z) φ
  calc sa12v3_cell m χ (c - L • latticePt z) g
      ≤ ENNReal.ofReal Cz * sa12v3_cell m χ (c - L • latticePt z) (mollify η (min ε 1) φ) := h2
    _ ≤ ENNReal.ofReal (Cz + 1) * (ENNReal.ofReal Cmoll * ∑ j ∈ J,
          sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d (k₀ z + j)) * φ x)) := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) ?_
        exact h3
    _ = ∑ j ∈ J, ENNReal.ofReal ((Cz + 1) * Cmoll) * sa12v3_cell m χ (cellPt d (k₀ z + j)) φ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith), Finset.mul_sum]
        rfl

theorem sa12v3_pd_uloc {η χ ζ : Euc d → ℝ} (hη : IsMollifier η) (hχ : IsUlocCutoff χ)
    (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Euc d → ℝ) (L ε : ℝ), 1 ≤ L → 0 < ε →
      ulocNormE m χ (periodicDatum ζ η L ε φ) ≤ ENNReal.ofReal C * ulocNormE m χ φ := by
  obtain ⟨J, C, hC, hmaster⟩ := sa12v3_pd_master hη hχ hζ m
  refine ⟨7 ^ d * J.card * C + 1, by positivity, fun φ L ε hL hε => ?_⟩
  unfold ulocNormE
  refine iSup_le fun c => ?_
  obtain ⟨K, k₀, hK, hKsub, hcard, hk, hle⟩ := hmaster L ε hL hε c
  have h := hle φ
  show sa12v3_cell m χ c (periodicDatum ζ η L ε φ) ≤ _
  refine h.trans ?_
  have hcell : ∀ z j, ENNReal.ofReal C * sa12v3_cell m χ (cellPt d (k₀ z + j)) φ ≤
      ENNReal.ofReal C * ⨆ z : Euc d, sobolevNormE (m : ℝ) fun x => χ (x - z) * φ x := fun z j =>
    mul_le_mul' le_rfl (le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * φ x)
      (cellPt d (k₀ z + j)))
  calc ∑ z ∈ K, ∑ j ∈ J, ENNReal.ofReal C * sa12v3_cell m χ (cellPt d (k₀ z + j)) φ
      ≤ ∑ z ∈ K, ∑ j ∈ J, ENNReal.ofReal C * ⨆ z : Euc d, sobolevNormE (m : ℝ) fun x => χ (x - z) * φ x :=
        Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun j _ => hcell z j
    _ = (K.card : ℝ≥0∞) * ((J.card : ℝ≥0∞) * (ENNReal.ofReal C *
          ⨆ z : Euc d, sobolevNormE (m : ℝ) fun x => χ (x - z) * φ x)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (7 ^ d) * ((J.card : ℝ≥0∞) * (ENNReal.ofReal C *
          ⨆ z : Euc d, sobolevNormE (m : ℝ) fun x => χ (x - z) * φ x)) := by
        refine mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard
    _ = ENNReal.ofReal (7 ^ d * J.card * C) * ⨆ z : Euc d, sobolevNormE (m : ℝ) fun x => χ (x - z) * φ x := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        ring
    _ ≤ ENNReal.ofReal (7 ^ d * J.card * C + 1) * ⨆ z : Euc d, sobolevNormE (m : ℝ) fun x => χ (x - z) * φ x :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end HRS.MH.AdjointRd.Phase2SA12V3
