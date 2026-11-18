import HRS.MS.SA12Z3NearN4E
import HRS.MS.SA12Z3NearN5B

/-!
# S.A.12 N4 (SA12Z3): `odd_gradient_finite`

`I_{lj} = ∫ ∂_lZ a T ∂_jZ`.  `I_{lj} + I_{jl}` is the commutator form (part C); `I_{lj} - I_{jl}` is
`∫ Z ((∂_j a) T ∂_l Z - (∂_l a) T ∂_j Z)` (part D, E), bounded through the skew-adjointness of `T` and
the `H¹ → L²` bound of `T` (`n0_kcd_global`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12z3_pd_one {Z : Euc d → ℝ} (hZ : ContDiff ℝ 1 Z) (l : Fin d) :
    partialDeriv (fun _ : Fin 1 => l) Z = D1 l Z := by
  funext x
  have h : (fun _ : Fin 1 => l) = (Fin.cons l (fun i : Fin 0 => (i.elim0 : Fin d)) : Fin (0 + 1) → Fin d) := by
    funext i; fin_cases i; rfl
  rw [h, sa12z3_pd_cons (fun i : Fin 0 => (i.elim0 : Fin d)) l (by simpa using hZ) x]
  simp only [sa12z3_pd_zero_fun]

theorem sa12z3_D1_le (l : Fin d) (f : Euc d → ℝ) (x : Euc d) : |D1 l f x| ≤ ‖fderiv ℝ f x‖ := by
  have h := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single l (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  simpa [D1, Real.norm_eq_abs] using h

theorem sa12z3_fderiv_D1_le {a : Euc d → ℝ} (ha : ContDiff ℝ 2 a) (j : Fin d) (x : Euc d) :
    ‖fderiv ℝ (D1 j a) x‖ ≤ ‖fderiv ℝ (fderiv ℝ a) x‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ a) x :=
    ((ha.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have : fderiv ℝ (D1 j a) x = (fderiv ℝ (fderiv ℝ a) x).flip (EuclideanSpace.single j (1 : ℝ)) := by
    unfold D1
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    ext z; simp
  rw [this]
  refine (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun z => ?_)
  simp only [ContinuousLinearMap.flip_apply]
  calc ‖(fderiv ℝ (fderiv ℝ a) x z) (EuclideanSpace.single j (1 : ℝ))‖
      ≤ ‖fderiv ℝ (fderiv ℝ a) x z‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ a) x‖ * ‖z‖ * 1 := by
        simp only [PiLp.norm_single, norm_one]
        exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) zero_le_one
    _ = _ := by ring

/-- Integrability of `‖∇ψ‖²` for `ψ ∈ C¹_c`. -/
theorem sa12z3_gradsq_integrable {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2) volume :=
  Continuous.integrable_of_hasCompactSupport (f := fun x => ‖fderiv ℝ ψ x‖ ^ 2)
    ((hψ.continuous_fderiv one_ne_zero).norm.pow 2)
    (((hψc.fderiv (𝕜 := ℝ)).norm).comp_left (g := fun t : ℝ => t ^ 2) (by simp))

theorem sa12z3_sq_integrable {ψ : Euc d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => ψ x ^ 2) volume :=
  Continuous.integrable_of_hasCompactSupport (f := fun x => ψ x ^ 2) (hψ.pow 2)
    (hψc.comp_left (g := fun t : ℝ => t ^ 2) (by simp))

/-- The antisymmetric term. -/
theorem sa12z3_delta_term (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {CT : ℝ} (hCT0 : 0 ≤ CT)
    (hCT : ∀ (i : Fin d) (w g : Euc d → ℝ), ContDiff ℝ 1 w → HasCompactSupport w →
      Continuous g → HasCompactSupport g →
      |∫ x, g x * firstRiesz d s i w x| ≤ CT * Real.sqrt (∫ x, g x ^ 2) *
        (Real.sqrt (∫ x, w x ^ 2) + Real.sqrt (∫ x, ‖fderiv ℝ w x‖ ^ 2)))
    (i j l : Fin d) {Z a : Euc d → ℝ} (hZ : ContDiff ℝ 2 Z) (hZc : HasCompactSupport Z)
    (ha : MemCb 2 a) :
    |∫ x, (Z x * D1 j a x) * firstRiesz d s i (D1 l Z) x| ≤
      3 * CT * cbNorm 2 a * ((∫ x, Z x ^ 2) + ∫ x, ‖fderiv ℝ Z x‖ ^ 2) := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have hcb0 := sa12z3_cb_nonneg ha
  set cb : ℝ := cbNorm 2 a with hcb
  set E : ℝ := (∫ x, Z x ^ 2) + ∫ x, ‖fderiv ℝ Z x‖ ^ 2 with hE
  have hZ1 : ContDiff ℝ 1 Z := hZ.of_le (by norm_num)
  have hIZ := sa12z3_sq_integrable hZ.continuous hZc
  have hIG := sa12z3_gradsq_integrable hZ1 hZc
  have hZ0 : 0 ≤ ∫ x, Z x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hG0 : 0 ≤ ∫ x, ‖fderiv ℝ Z x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hE0 : 0 ≤ E := add_nonneg hZ0 hG0
  set u : Euc d → ℝ := fun x => Z x * D1 j a x with hu
  have hDja : ContDiff ℝ 1 (D1 j a) := D1_contDiff ha2 j
  have hu1 : ContDiff ℝ 1 u := hZ1.mul hDja
  have huc : HasCompactSupport u := hZc.mul_right
  have hfl : ContDiff ℝ 1 (D1 l Z) := D1_contDiff hZ l
  have hflc : HasCompactSupport (D1 l Z) := D1_supp hZc l
  have hsk := sa12z3_T_skew hd hs0 hsd i hu1 huc hfl hflc
  have hpair := hCT i u (D1 l Z) hu1 huc hfl.continuous hflc
  -- bounds
  have hDa : ∀ x, |D1 j a x| ≤ cb := fun x =>
    (sa12z3_D1_le j a x).trans (sa12z3_cb2_bounds ha x).2.1
  have hfl2 : ∫ x, D1 l Z x ^ 2 ≤ E := by
    have : ∫ x, D1 l Z x ^ 2 ≤ ∫ x, ‖fderiv ℝ Z x‖ ^ 2 :=
      integral_mono (sa12z3_sq_integrable hfl.continuous hflc) hIG fun x => by
        have := sa12z3_D1_le l Z x
        rw [← sq_abs (D1 l Z x)]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
    linarith
  have hu2 : ∫ x, u x ^ 2 ≤ cb ^ 2 * E := by
    have : ∫ x, u x ^ 2 ≤ ∫ x, cb ^ 2 * Z x ^ 2 :=
      integral_mono (sa12z3_sq_integrable hu1.continuous huc) (hIZ.const_mul _) fun x => by
        show (Z x * D1 j a x) ^ 2 ≤ cb ^ 2 * Z x ^ 2
        have h1 : D1 j a x ^ 2 ≤ cb ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hDa x) 2
        nlinarith [sq_nonneg (Z x)]
    rw [integral_const_mul] at this
    nlinarith [mul_nonneg (sq_nonneg cb) hG0]
  have hgu : ∫ x, ‖fderiv ℝ u x‖ ^ 2 ≤ 2 * cb ^ 2 * E := by
    have hpt : ∀ x, ‖fderiv ℝ u x‖ ^ 2 ≤ 2 * cb ^ 2 * (Z x ^ 2 + ‖fderiv ℝ Z x‖ ^ 2) := by
      intro x
      have hprod : fderiv ℝ u x = Z x • fderiv ℝ (D1 j a) x + D1 j a x • fderiv ℝ Z x := by
        have := fderiv_fun_mul (hZ1.differentiable one_ne_zero x) (hDja.differentiable one_ne_zero x)
        simpa [hu] using this
      have hn : ‖fderiv ℝ u x‖ ≤ cb * |Z x| + cb * ‖fderiv ℝ Z x‖ := by
        rw [hprod]
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ?_ ?_
        · refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
          rw [Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right ((sa12z3_fderiv_D1_le ha2 j x).trans
            (sa12z3_cb2_bounds ha x).2.2) (abs_nonneg _)
        · refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hDa x) (norm_nonneg _)
      have h0 : 0 ≤ ‖fderiv ℝ u x‖ := norm_nonneg _
      calc ‖fderiv ℝ u x‖ ^ 2 ≤ (cb * |Z x| + cb * ‖fderiv ℝ Z x‖) ^ 2 := pow_le_pow_left₀ h0 hn 2
        _ ≤ 2 * cb ^ 2 * (Z x ^ 2 + ‖fderiv ℝ Z x‖ ^ 2) := by
          nlinarith [sq_nonneg (|Z x| - ‖fderiv ℝ Z x‖), sq_abs (Z x), sq_nonneg cb]
    have : ∫ x, ‖fderiv ℝ u x‖ ^ 2 ≤ ∫ x, 2 * cb ^ 2 * (Z x ^ 2 + ‖fderiv ℝ Z x‖ ^ 2) :=
      integral_mono (sa12z3_gradsq_integrable hu1 huc) ((hIZ.add hIG).const_mul _) hpt
    rw [integral_const_mul, integral_add hIZ hIG] at this
    exact this
  have hsE : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE0
  have hA : Real.sqrt (∫ x, u x ^ 2) ≤ cb * Real.sqrt E := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∫ x, u x ^ 2 ≤ cb ^ 2 * E := hu2
      _ = (cb * Real.sqrt E) ^ 2 := by rw [mul_pow, Real.sq_sqrt hE0]
  have hΓ : Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2) ≤ 2 * (cb * Real.sqrt E) := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ∫ x, ‖fderiv ℝ u x‖ ^ 2 ≤ 2 * cb ^ 2 * E := hgu
      _ ≤ (2 * (cb * Real.sqrt E)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hE0]; nlinarith [mul_nonneg (sq_nonneg cb) hE0]
  have hg : Real.sqrt (∫ x, D1 l Z x ^ 2) ≤ Real.sqrt E := Real.sqrt_le_sqrt hfl2
  have hmain : |∫ x, D1 l Z x * firstRiesz d s i u x| ≤ 3 * CT * cb * E := by
    refine hpair.trans ?_
    calc CT * Real.sqrt (∫ x, D1 l Z x ^ 2) * (Real.sqrt (∫ x, u x ^ 2) +
          Real.sqrt (∫ x, ‖fderiv ℝ u x‖ ^ 2))
        ≤ CT * Real.sqrt E * (cb * Real.sqrt E + 2 * (cb * Real.sqrt E)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hg hCT0) (add_le_add hA hΓ) (by positivity)
            (by positivity)
      _ = 3 * CT * cb * (Real.sqrt E * Real.sqrt E) := by ring
      _ = 3 * CT * cb * E := by rw [hsE]
  have : ∫ x, (Z x * D1 j a x) * firstRiesz d s i (D1 l Z) x = -∫ x, D1 l Z x * firstRiesz d s i u x := hsk
  rw [this, abs_neg]
  exact hmain

end HRS.MH.AdjointRd.Phase2SA12Near
