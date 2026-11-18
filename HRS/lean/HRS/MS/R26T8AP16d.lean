import HRS.MS.R26T8AP16d2

/-!
# S8.2 T8A P16d: the local operator commutes with the centred row average
`r26t8a_local_row_comm`: `Q` conormal `(k+2) b M (σ-2)`, `σ < d`, `∫ ρ(y) Q(u,y) dy = 0` for all `u`, then
`∫ ρ(y) (nu Δ + b·∇)Q(.,y)(x) dy = 0` for all `x`.  Weak form (`r26t8a_comm_ibp`), Fubini twice (`r26t8a_comm_dom`) and
`r26t8a_a01_row_deriv`; the row of the local operator is continuous by the row lemma.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_local_row_comm (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma A : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) (hA : 0 ≤ A) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {Q : Euc d → Euc d → ℝ}
    (hQ : Conormal (k + 2) b M (sigma - 2) A Q) (hcan : ∀ u, ∫ y, rho y * Q u y = 0) (x : Euc d) :
    ∫ y, rho y * r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x = 0 := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0c : 0 < criticalS d := by unfold criticalS; linarith
  have hsc : criticalS d < d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨B_, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0c.le hsc ha hbeta hrho
  have hpos : ∀ x, 0 < rho x := fun x => hR.pos x
  have hρs : ContDiff ℝ ∞ rho := (HRS.MS.Mov0.mv0_hgauss hd hs0c.le hsc ha hbeta hrho).1
  have hρc : Continuous rho := hρs.continuous
  have hM1 : 0 ≤ M + 1 := by linarith
  -- the row of the local operator
  obtain ⟨Bα, hBα0, hBα⟩ := r26t8a_drift_coord hd a beta ha hbeta hrho 0
  obtain ⟨cK, hcK0, hKc⟩ := r26t8a_Kx_conormal hchi (critCoeff d a beta rho)
    (fun i x => -(forceMean rho x i) - a * x i) (fun i x => r26t8a_drift_coord_eq a beta rho i x) 0 b M (sigma - 2)
    Bα hBα0 (fun i => (hBα i).1) (fun i => (hBα i).2)
  set K : Euc d → Euc d → ℝ := fun x y => r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x with hK
  have hQ0 : Conormal (0 + 2) b M (sigma - 2) A Q := r26t8a_conormal_mono (by omega) hQ
  have hKc0 : Conormal 0 b (M + 1) sigma (cK * A) K :=
    r26t8a_conormal_mono_sA (by positivity) le_rfl (le_of_eq (by ring)) (hKc Q A hA hQ0)
  have hcKA : 0 ≤ cK * A := mul_nonneg hcK0 hA
  have hdx : ∀ j : Fin d, Conormal 0 b (M + 1) (sigma - 1) (2 * A) (r26t8a_dx j Q) := by
    intro j
    have h1 := r26t8a_f8_dx_conormal hchi hA (k := k + 1) hQ j
    have h2 := r26t8a_conormal_mono (k := 0) (k' := k + 1) (by omega) h1
    have e : sigma - 2 + 1 = sigma - 1 := by ring
    rw [e] at h2
    exact r26t8a_conormal_mono_M (by positivity) (by linarith : M ≤ M + 1) h2
  obtain ⟨Cr, hCr0, hr⟩ := r26t8a_p15_rowx hd 0 b a beta (M + 1) sigma ha hbeta hM1 hsd hrho
  have hucont : Continuous (fun x => ∫ y, rho y * K x y) := by
    have h := (hr K (cK * A) hcKA hKc0).2.1.continuous
    have e : (fun x => ∫ y, K x y ∂(HRS.Whole.withDensityReal rho)) = fun x => ∫ y, rho y * K x y :=
      funext fun x => r26t8a_f25_wd_integral hprob (K x)
    rwa [e] at h
  obtain ⟨Kρ, hKρ0, hρ0, hKρ⟩ := r26t8a_p15_rho_weight hd 0 (M + 1) ha hbeta hrho
  have hdxint : ∀ (j : Fin d) (x : Euc d), Integrable (fun y => rho y * r26t8a_dx j Q x y) := fun j x =>
    r26t8a_row_integrable hd 0 b hM1 (sigma - 1) (by linarith) Kρ hKρ0 hρ0 hKρ (by positivity) (hdx j) x
  -- weak form
  have hweak : ∀ φ : Euc d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x * (rho x * ∫ y, rho y * K x y) = 0 := by
    intro φ hφ hφc
    set ψ : Fin d → Euc d → ℝ := fun j x => fderiv ℝ φ x (EuclideanSpace.single j 1) * rho x with hψ
    have hψc : ∀ j, Continuous (ψ j) := fun j =>
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).mul hρc
    have hψs : ∀ j, HasCompactSupport (ψ j) := fun j => by
      have := (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) (by simp)
      exact this.mul_right
    have hW0 : Continuous (fun x => φ x * rho x) := hφ.continuous.mul hρc
    have hW0s : HasCompactSupport (fun x => φ x * rho x) := hφc.mul_right
    have hF1 : Integrable (fun p : Euc d × Euc d => φ p.1 * (rho p.1 * (rho p.2 * K p.1 p.2)))
        (volume.prod volume) := by
      have := r26t8a_comm_dom hd b a beta (M + 1) sigma (cK * A) ha hbeta hM1 hsd hrho hcKA hKc0
        (W := fun x => φ x * rho x) hW0 hW0s
      exact this.congr (Filter.Eventually.of_forall fun p => by simp only []; ring)
    have hF3 : Integrable (fun p : Euc d × Euc d => ∑ j : Fin d, rho p.2 * (ψ j p.1 * r26t8a_dx j Q p.1 p.2))
        (volume.prod volume) := by
      refine integrable_finset_sum _ fun j _ => ?_
      have := r26t8a_comm_dom hd b a beta (M + 1) (sigma - 1) (2 * A) ha hbeta hM1 (by linarith) hrho
        (by positivity) (hdx j) (W := ψ j) (hψc j) (hψs j)
      exact this.congr (Filter.Eventually.of_forall fun p => by simp only []; ring)
    have hzero : ∀ x', ∫ y, ∑ j : Fin d, rho y * (ψ j x' * r26t8a_dx j Q x' y) = 0 := by
      intro x'
      rw [integral_finset_sum _ fun j _ => ((hdxint j x').const_mul (ψ j x')).congr
        (Filter.Eventually.of_forall fun y => by simp only []; ring)]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ∀ y, rho y * (ψ j x' * r26t8a_dx j Q x' y) = ψ j x' * (rho y * r26t8a_dx j Q x' y) :=
        fun y => by ring
      simp only [this, integral_const_mul]
      rw [r26t8a_a01_row_deriv d hd k b a beta M sigma ha hbeta hM hsd hrho hA hQ hcan j x', mul_zero]
    calc ∫ x, φ x * (rho x * ∫ y, rho y * K x y)
        = ∫ x, ∫ y, φ x * (rho x * (rho y * K x y)) := by
          congr 1; funext x
          rw [← integral_const_mul, ← integral_const_mul]
      _ = ∫ y, ∫ x, φ x * (rho x * (rho y * K x y)) :=
          integral_integral_swap (f := fun x y => φ x * (rho x * (rho y * K x y))) hF1
      _ = ∫ y, rho y * (-(beta⁻¹ * ∫ x, ∑ j : Fin d, fderiv ℝ φ x (EuclideanSpace.single j 1) *
            (rho x * r26t8a_dx j Q x y))) := by
          congr 1; funext y
          rw [← r26t8a_comm_ibp d hd k b a beta M sigma A ha hbeta hM hsd hA rho hrho Q hQ φ hφ hφc y,
            ← integral_const_mul]
          congr 1; funext x; ring
      _ = -(beta⁻¹ * ∫ y, ∫ x, ∑ j : Fin d, rho y * (ψ j x * r26t8a_dx j Q x y)) := by
          rw [← integral_const_mul, ← integral_neg]
          congr 1; funext y
          have : ∀ x, ∑ j : Fin d, rho y * (ψ j x * r26t8a_dx j Q x y) =
              rho y * ∑ j : Fin d, fderiv ℝ φ x (EuclideanSpace.single j 1) * (rho x * r26t8a_dx j Q x y) := by
            intro x; rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [hψ]; ring
          simp only [this, integral_const_mul]
          ring
      _ = -(beta⁻¹ * ∫ x, ∫ y, ∑ j : Fin d, rho y * (ψ j x * r26t8a_dx j Q x y)) := by
          rw [integral_integral_swap (f := fun y x => ∑ j : Fin d, rho y * (ψ j x * r26t8a_dx j Q x y))
            hF3.swap]
      _ = 0 := by simp only [hzero, integral_zero, mul_zero, neg_zero]
  have hcont : Continuous (fun x => rho x * ∫ y, rho y * K x y) := hρc.mul hucont
  have hae0 : ∀ᵐ x : Euc d ∂volume, rho x * ∫ y, rho y * K x y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable ?_
    intro g hg hgc
    simpa only [smul_eq_mul] using hweak g hg hgc
  have := (hcont.ae_eq_iff_eq volume continuous_const).1 hae0
  have hx : rho x * ∫ y, rho y * K x y = 0 := congrFun this x
  rcases mul_eq_zero.1 hx with h | h
  · exact absurd h (hpos x).ne'
  · exact h

end HRS.MS.R26T8A
