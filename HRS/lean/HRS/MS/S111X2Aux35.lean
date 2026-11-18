import HRS.MS.S111X2Aux34
import HRS.MS.QsfOsc4

/-!
# S11.1 X2, packet H01 (part 3): bounds of the initial data of the Hermite observations

For the dual Hermite tests `φ_α = λ_α^{-m/2} h_α` (`m = 24d+240`) and the thermal reference:
`∑_{α∈S} (‖P_μ φ_α‖² + ‖P_μ Gφ_α‖²) ≤ Λ` uniformly in the finite set `S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34
open HRS.MS.S111X1 (EnData KData Nnl)

variable {d : ℕ}

theorem s111x2_cbNorm_bounds {φ : Euc d → ℝ} (H : MemCb 2 φ) :
    (∀ x, ‖φ x‖ ≤ HRS.cbNorm 2 φ) ∧ CbD φ (HRS.cbNorm 2 φ) (HRS.cbNorm 2 φ) := by
  have hbdd : ∀ j ≤ 2, BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ j φ x‖) := H.2
  have hle : ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j φ x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j φ z‖ := fun j hj x =>
    le_ciSup (hbdd j hj) x
  have hnn : ∀ j, 0 ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j φ z‖ := fun j => Real.iSup_nonneg fun z => norm_nonneg _
  have hc : HRS.cbNorm 2 φ = (⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 φ z‖) + (⨆ z : Euc d, ‖iteratedFDeriv ℝ 1 φ z‖) +
      ⨆ z : Euc d, ‖iteratedFDeriv ℝ 2 φ z‖ := by
    unfold HRS.cbNorm
    simp [Finset.sum_range_succ]
  have h0 := hnn 0
  have h1 := hnn 1
  have h2 := hnn 2
  refine ⟨fun x => ?_, H.1, fun x => ?_, fun x => ?_⟩
  · have := hle 0 (by norm_num) x
    rw [norm_iteratedFDeriv_zero] at this
    rw [hc]; linarith
  · have := hle 1 (by norm_num) x
    rw [norm_iteratedFDeriv_one] at this
    rw [hc]; linarith
  · have := hle 2 le_rfl x
    have e1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := φ) (x := x) (n := 1)
    rw [norm_iteratedFDeriv_one] at e1
    rw [e1, hc]; linarith

section Core

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

/-- The generator is bounded linearly in the `C²` data. -/
theorem s111x2_gen_lin_bound (T : TD d s β ρ M C) :
    ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ {h : Euc d → ℝ} {B1 B2 : ℝ}, CbD h B1 B2 → ∀ x,
      |generatorW C 0 h x| ≤ Kg * (B1 + B2) * (1 + ‖x‖) := by
  obtain ⟨c0, hc0⟩ := T.en.dgrow
  have hβ := T.en.hβ
  set kA' := max (HRS.MS.S111X1.kA d s M ρ) 0 with hkA'
  set c0' := max c0 0 with hc0'
  refine ⟨β⁻¹ * d + c0' + kA', by positivity, fun {h B1 B2} H x => ?_⟩
  have hB1 := H.B1_nonneg
  have hB2 := H.B2_nonneg
  have hg1 : ∀ y, ‖gradient h y‖ ≤ B1 := fun y => by rw [s111x2_norm_gradient]; exact H.d1 y
  have hN := HRS.MS.S111X1.Nnl_bdd T.en.K hg1 x
  have hL1 := s111x2_laplacian_bound H x
  have hdr : ‖C.drift 0 x‖ ≤ c0' * (1 + ‖x‖) := (hc0 0 x).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have h2 : |inner ℝ (C.drift 0 x) (gradient h x)| ≤ c0' * (1 + ‖x‖) * B1 :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hdr (hg1 x) (norm_nonneg _) (by positivity))
  have hLb : |s111x2_L ρ h x| ≤ d * B2 + β * (c0' * (1 + ‖x‖) * B1) := by
    rw [s111x2_L_eq T h x]
    calc |-Laplacian.laplacian h x - β * inner ℝ (C.drift 0 x) (gradient h x)|
        ≤ |Laplacian.laplacian h x| + β * |inner ℝ (C.drift 0 x) (gradient h x)| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_neg, abs_mul, abs_of_pos hβ]
      _ ≤ _ := add_le_add hL1 (mul_le_mul_of_nonneg_left h2 hβ.le)
  rw [s111x2_gen_eq T H]
  simp only
  refine (abs_add_le _ _).trans ?_
  have hN' : |Nnl d s ρ (gradient h) x| ≤ B1 * kA' :=
    hN.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hB1)
  have hL' : |-β⁻¹ * s111x2_L ρ h x| ≤ β⁻¹ * (d * B2 + β * (c0' * (1 + ‖x‖) * B1)) := by
    rw [abs_mul, abs_neg, abs_of_pos (inv_pos.2 hβ)]
    exact mul_le_mul_of_nonneg_left hLb (inv_pos.2 hβ).le
  have hx := norm_nonneg x
  have e : β⁻¹ * (d * B2 + β * (c0' * (1 + ‖x‖) * B1)) = β⁻¹ * d * B2 + c0' * (1 + ‖x‖) * B1 := by
    field_simp
  rw [e] at hL'
  have hc00 : 0 ≤ c0' := le_max_right _ _
  have hkA0 : 0 ≤ kA' := le_max_right _ _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcoef : 0 ≤ β⁻¹ * d := mul_nonneg (inv_pos.2 hβ).le hd0
  have s1 : B2 ≤ (B1 + B2) * (1 + ‖x‖) := by nlinarith [mul_nonneg hB1 hx, mul_nonneg hB2 hx]
  have s2 : B1 ≤ (B1 + B2) * (1 + ‖x‖) := by nlinarith [mul_nonneg hB1 hx, mul_nonneg hB2 hx]
  have s3 : B1 * (1 + ‖x‖) ≤ (B1 + B2) * (1 + ‖x‖) := by nlinarith [mul_nonneg hB2 hx]
  have t1 := mul_le_mul_of_nonneg_left s1 hcoef
  have t2 := mul_le_mul_of_nonneg_left s3 hc00
  have t3 := mul_le_mul_of_nonneg_left s2 hkA0
  have e2 : c0' * (1 + ‖x‖) * B1 = c0' * (B1 * (1 + ‖x‖)) := by ring
  rw [e2] at hL'
  have e3 : B1 * kA' = kA' * B1 := mul_comm _ _
  rw [e3] at hN'
  have : (β⁻¹ * d + c0' + kA') * (B1 + B2) * (1 + ‖x‖) =
      β⁻¹ * d * ((B1 + B2) * (1 + ‖x‖)) + c0' * ((B1 + B2) * (1 + ‖x‖)) + kA' * ((B1 + B2) * (1 + ‖x‖)) := by
    ring
  rw [this]
  nlinarith [t1, t2, t3, hL', hN']

theorem s111x2_cs_le_sq {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ} (hf : MemLp f 2 μ) :
    s111x2_centeredSquare μ f ≤ ∫ x, f x ^ 2 ∂μ := by
  have hv : ProbabilityTheory.variance f μ = s111x2_centeredSquare μ f := by
    rw [ProbabilityTheory.variance_eq_integral hf.aemeasurable]
    rfl
  rw [← hv]
  exact ProbabilityTheory.variance_le_expectation_sq hf.aestronglyMeasurable

theorem s111x2_init_sum (hd : 1 ≤ d) (T : TD d s β ρ M C) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ S : Finset (MultiIndex d),
      ∑ α ∈ S, (s111x2_centeredSquare (HRS.Whole.withDensityReal ρ) (oscTestFun (wholeSpaceIndex d : ℝ) α) +
        s111x2_centeredSquare (HRS.Whole.withDensityReal ρ)
          (generatorW C 0 (oscTestFun (wholeSpaceIndex d : ℝ) α))) ≤ Λ := by
  haveI := isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set m : ℝ := (wholeSpaceIndex d : ℝ) with hm
  obtain ⟨K, hK0, hK⟩ := S45.s45_cb_oscTest hd 2 m
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmv : m = 24 * (d : ℝ) + 240 := by simp [hm, wholeSpaceIndex]
  have hlt : (d : ℝ) < (m - ((2 : ℕ) : ℝ)) / 2 := by rw [hmv]; push_cast; linarith
  have hsum : Summable fun α : MultiIndex d => K * oscEigenvalue d α ^ (-((m - ((2 : ℕ) : ℝ)) / 2)) :=
    ((summable_oscEigenvalue_rpow_iff hd _).2 hlt).mul_left K
  set q : MultiIndex d → ℝ := fun α => K * oscEigenvalue d α ^ (-((m - ((2 : ℕ) : ℝ)) / 2)) with hq
  have hq0 : ∀ α, 0 ≤ q α := fun α => mul_nonneg hK0 (Real.rpow_nonneg (by
    have := one_le_oscEigenvalue (d := d) α; linarith) _)
  obtain ⟨Kg, hKg0, hKg⟩ := s111x2_gen_lin_bound T
  have hMomI : Integrable (fun x : Euc d => (1 + ‖x‖) ^ 2) μ := by
    have := (s111x2_lin_memLp T 1).integrable_sq
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  set Mom : ℝ := ∫ x, (1 + ‖x‖) ^ 2 ∂μ with hMom
  have hMom0 : 0 ≤ Mom := integral_nonneg fun x => sq_nonneg _
  refine ⟨(1 + 4 * Kg ^ 2 * Mom) * (∑' α, q α) ^ 2, by positivity, fun S => ?_⟩
  have hc : ∀ α, cbNorm 2 (oscTestFun m α) ≤ q α := fun α => (hK α).2
  have hper : ∀ α, s111x2_centeredSquare μ (oscTestFun m α) +
      s111x2_centeredSquare μ (generatorW C 0 (oscTestFun m α)) ≤
      (1 + 4 * Kg ^ 2 * Mom) * (cbNorm 2 (oscTestFun m α)) ^ 2 := by
    intro α
    set c := cbNorm 2 (oscTestFun m α) with hcdef
    obtain ⟨h0, hC⟩ := s111x2_cbNorm_bounds (hK α).1
    have hc0 : 0 ≤ c := (norm_nonneg _).trans (h0 0)
    have hmem : MemLp (oscTestFun m α) 2 μ :=
      (MemLp.of_bound (hC.smooth.continuous.aestronglyMeasurable) c
        (Filter.Eventually.of_forall fun x => h0 x)).mono_exponent le_top
    have e1 : s111x2_centeredSquare μ (oscTestFun m α) ≤ c ^ 2 := by
      refine (s111x2_cs_le_sq hmem).trans ?_
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => oscTestFun m α x ^ 2) (C := c ^ 2)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using h0 x) 2)
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at this
      exact (le_abs_self _).trans (by simpa using this)
    have e2 : s111x2_centeredSquare μ (generatorW C 0 (oscTestFun m α)) ≤ 4 * Kg ^ 2 * Mom * c ^ 2 := by
      refine (s111x2_cs_le_sq (s111x2_gen_memLp T hC)).trans ?_
      have hI1 : Integrable (fun x => (generatorW C 0 (oscTestFun m α) x) ^ 2) μ :=
        (s111x2_gen_memLp T hC).integrable_sq
      have hI2 : Integrable (fun x : Euc d => (2 * Kg * c) ^ 2 * (1 + ‖x‖) ^ 2) μ := hMomI.const_mul _
      calc ∫ x, (generatorW C 0 (oscTestFun m α) x) ^ 2 ∂μ
          ≤ ∫ x, (2 * Kg * c) ^ 2 * (1 + ‖x‖) ^ 2 ∂μ := by
            refine integral_mono hI1 hI2 fun x => ?_
            have := hKg hC x
            have hb : |generatorW C 0 (oscTestFun m α) x| ≤ 2 * Kg * c * (1 + ‖x‖) := by
              refine this.trans (le_of_eq ?_); ring
            calc (generatorW C 0 (oscTestFun m α) x) ^ 2 = |generatorW C 0 (oscTestFun m α) x| ^ 2 :=
                  (sq_abs _).symm
              _ ≤ (2 * Kg * c * (1 + ‖x‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
              _ = (2 * Kg * c) ^ 2 * (1 + ‖x‖) ^ 2 := by ring
        _ = (2 * Kg * c) ^ 2 * Mom := by rw [integral_const_mul]
        _ = 4 * Kg ^ 2 * Mom * c ^ 2 := by ring
    linarith
  calc ∑ α ∈ S, (s111x2_centeredSquare μ (oscTestFun m α) +
        s111x2_centeredSquare μ (generatorW C 0 (oscTestFun m α)))
      ≤ ∑ α ∈ S, (1 + 4 * Kg ^ 2 * Mom) * (cbNorm 2 (oscTestFun m α)) ^ 2 :=
        Finset.sum_le_sum fun α _ => hper α
    _ = (1 + 4 * Kg ^ 2 * Mom) * ∑ α ∈ S, (cbNorm 2 (oscTestFun m α)) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 + 4 * Kg ^ 2 * Mom) * (∑ α ∈ S, cbNorm 2 (oscTestFun m α)) ^ 2 := by
        gcongr
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun α _ => by
          obtain ⟨h0, _⟩ := s111x2_cbNorm_bounds (hK α).1
          exact (norm_nonneg _).trans (h0 0)
    _ ≤ (1 + 4 * Kg ^ 2 * Mom) * (∑' α, q α) ^ 2 := by
        gcongr
        · exact Finset.sum_nonneg fun α _ => by
            obtain ⟨h0, _⟩ := s111x2_cbNorm_bounds (hK α).1
            exact (norm_nonneg _).trans (h0 0)
        · exact (Finset.sum_le_sum fun α _ => hc α).trans (hsum.sum_le_tsum S fun α _ => hq0 α)

end Core

end HRS.MS.S111X2
