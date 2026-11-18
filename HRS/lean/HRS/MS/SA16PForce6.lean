import HRS.MS.SA16PForce5

/-!
# SA16P P4, part 6: the mean-field drift `b = M ∇g*ρ - ∇V` of `AdjointRdData` at a fixed time

`sa16p_drift_bounds`: for `D.s = s ∈ [0,d)`, `|M_ij| ≤ MB`, `VHypRd (m+3) ΛV G₀ V`, and `ρ` with
`IsRegularDensityW (m+3) Λ ρ`, the drift `meanFieldDriftW D ρ` is `C^{m+2}`, `‖b(0)‖ ≤ Bf + G₀` and
`‖D^j b(x)‖ ≤ Bf + ΛV` for `1 ≤ j ≤ m+2` and all `x`, with `Bf = d²MB · d C₀ A`, `A = d^{m+3} Λ⁺ 2^{(d+3)/2}`
independent of `D`, `ρ`.  (This is the fixed-time content of the skeleton `drift_data_high`, E13; the time clamp and the
joint continuity in `(t,x)` are the separate step using `coefficient_time_regular`.)
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

section Drift
variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma sa16p_matVec_norm_le (hd : 1 ≤ d) {MB : ℝ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, |M i j| ≤ MB) (v : 𝔼) :
    ‖Torus.matVec M v‖ ≤ ((d : ℝ) * d * MB) * ‖v‖ := by
  have hMB : 0 ≤ MB := (abs_nonneg _).trans (hM ⟨0, by omega⟩ ⟨0, by omega⟩)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcomp : ∀ i, |(Torus.matVec M v) i| ≤ (d : ℝ) * MB * ‖v‖ := by
    intro i
    have h1 : (Torus.matVec M v) i = ∑ j, M i j * v j := by
      have hmv : Torus.matVec M v = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M v :=
        (LinearMap.congr_fun (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M) v).symm
      rw [hmv]
      show (M.mulVec (v : Fin d → ℝ)) i = _
      simp [Matrix.mulVec, dotProduct]
    rw [h1]
    calc |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin d, MB * ‖v‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hM i j) (by simpa using PiLp.norm_apply_le v j) (abs_nonneg _) hMB
      _ = (d : ℝ) * MB * ‖v‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  set a : ℝ := (d : ℝ) * MB * ‖v‖ with ha
  have ha0 : 0 ≤ a := by positivity
  rw [EuclideanSpace.norm_eq]
  have h2 : ∑ i, ‖(Torus.matVec M v) i‖ ^ 2 ≤ (d : ℝ) * a ^ 2 := by
    calc ∑ i, ‖(Torus.matVec M v) i‖ ^ 2 ≤ ∑ i : Fin d, a ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcomp i) 2
      _ = (d : ℝ) * a ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i, ‖(Torus.matVec M v) i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * a ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt d * a := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq ha0]
    _ ≤ d * a := mul_le_mul_of_nonneg_right (by
          calc Real.sqrt d ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
            _ = d := Real.sqrt_sq (by positivity)) ha0
    _ = ((d : ℝ) * d * MB) * ‖v‖ := by rw [ha]; ring

set_option synthInstance.maxHeartbeats 400000 in
theorem sa16p_drift_bounds (hd : 1 ≤ d) {s MB Λ ΛV G₀ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    {D : WholeDyn d} (hDs : D.s = s) (hM : ∀ i j, |D.M i j| ≤ MB)
    (hV : VHypRd (m + 3) ΛV G₀ D.V) {ρ : 𝔼 → ℝ} (hρ : IsRegularDensityW (m + 3) Λ ρ) :
    ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (meanFieldDriftW D ρ) ∧
      ‖meanFieldDriftW D ρ 0‖ ≤ ((d : ℝ) * d * MB) * ((d : ℝ) * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s *
        ((d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)))) + G₀ ∧
      ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (meanFieldDriftW D ρ) x‖ ≤
        ((d : ℝ) * d * MB) * ((d : ℝ) * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s *
          ((d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)))) + ΛV := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMB : 0 ≤ MB := (abs_nonneg _).trans (hM ⟨0, by omega⟩ ⟨0, by omega⟩)
  set A : ℝ := (d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2) with hA
  have hb : ∀ j ≤ m + 2 + 1, ∀ y, ‖iteratedFDeriv ℝ j ρ y‖ ≤ A * sa16p_w d y := by
    intro j hj y
    refine (sa16p_regular_bounds hρ j (by omega) y).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sa16p_w_pos y).le
    have : (d : ℝ) ^ j ≤ (d : ℝ) ^ (m + 3) := pow_le_pow_right₀ hd1 (by omega)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (le_max_right _ _)) (by positivity)
  obtain ⟨hfc, hfb⟩ := sa16p_force_contDiff hd hs0 hsd (m + 2) (ρ := ρ) (A := A) hρ.1 hb
  subst hDs
  -- the linear map
  let Lm : 𝔼 →L[ℝ] 𝔼 := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) D.M
  have hLm : ∀ v, Torus.matVec D.M v = Lm v := fun v =>
    (LinearMap.congr_fun (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin D.M) v).symm
  have hLn : ‖Lm‖ ≤ (d : ℝ) * d * MB := ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (fun v => by rw [← hLm]; exact sa16p_matVec_norm_le hd D.M hM v)
  set f := convGradConvW (rieszKernelGrad d D.s) ρ with hf
  have hbf : meanFieldDriftW D ρ = fun x => Lm (f x) - gradient D.V x := by
    funext x; simp only [meanFieldDriftW, hLm]; rfl
  -- the gradient of V
  have hVsm : ContDiff ℝ ∞ D.V := hV.1
  have hV3 : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) D.V := contDiff_infty.1 hVsm (m + 3)
  have hdV : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (fderiv ℝ D.V) :=
    hV3.fderiv_right (m := ((m + 2 : ℕ) : WithTop ℕ∞)) (by norm_cast)
  have hgV : gradient D.V = (InnerProductSpace.toDual ℝ 𝔼).symm ∘ fderiv ℝ D.V := rfl
  have hgc : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (gradient D.V) := by
    rw [hgV]; exact (InnerProductSpace.toDual ℝ 𝔼).symm.contDiff.comp hdV
  have hLf : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (fun x => Lm (f x)) := Lm.contDiff.comp hfc
  refine ⟨?_, ?_, fun j hj1 hj2 x => ?_⟩
  · rw [hbf]; exact hLf.sub hgc
  · rw [hbf]
    have h0 := hV.2.2
    have h1 : ‖Lm (f 0)‖ ≤ ((d : ℝ) * d * MB) * ((d : ℝ) * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c D.s) D.s * A)) := by
      have := hfb 0 (by omega) 0
      rw [norm_iteratedFDeriv_zero] at this
      exact (Lm.le_opNorm (f 0)).trans (mul_le_mul hLn this (norm_nonneg _) (by positivity))
    calc ‖Lm (f 0) - gradient D.V 0‖ ≤ ‖Lm (f 0)‖ + ‖gradient D.V 0‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add h1 h0
  · rw [hbf]
    have hj2' : (j : WithTop ℕ∞) ≤ ((m + 2 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hj2
    have hcA : ContDiffAt ℝ (j : WithTop ℕ∞) (fun x => Lm (f x)) x := (hLf.of_le hj2').contDiffAt
    have hcB : ContDiffAt ℝ (j : WithTop ℕ∞) (gradient D.V) x := (hgc.of_le hj2').contDiffAt
    change ‖iteratedFDeriv ℝ j ((fun x => Lm (f x)) - gradient D.V) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply hcA hcB]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · have h1 := Lm.norm_iteratedFDeriv_comp_left (f := f) (x := x)
        ((hfc.of_le hj2').contDiffAt) le_rfl
      refine h1.trans (mul_le_mul hLn (hfb j hj2 x) (norm_nonneg _) (by positivity))
    · have h1 := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left
        (InnerProductSpace.toDual ℝ 𝔼).symm (fderiv ℝ D.V) x j
      rw [hgV, h1, norm_iteratedFDeriv_fderiv]
      exact hV.2.1 (j + 1) (by omega) (by omega) x

end Drift

end HRS.Whole.AppendixA.Phase2SA16P
