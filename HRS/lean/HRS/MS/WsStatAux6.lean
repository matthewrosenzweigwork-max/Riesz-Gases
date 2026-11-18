import HRS.MS.WsStatAux5
import HRS.MS.GoFeatAux3

/-!
# S21 packet D2: the thermal density is a stationary mean-field solution

`s21_regSlice`: `RegSliceRd` for the thermal density (Schwartz).
`s21_mf_stationary`: `IsWholeMeanFieldSolution (<s, -1, quadV (a.1) 0, beta^{-1}>) T (fun _ => rho_beta)` for every `T`:
the weak identity of `H:eq:meanfield` for `psi in C_b^2` is
`int rho (nu Delta psi - <grad V, grad psi>) + (self pairing) = 0`, the self pairing being
`- int rho <grad psi, grad g*rho>` (`self_pairing_rd_proof`), `grad g*rho = grad U` (`s21_gradU_eq`) and
`int rho (L psi) = 0` for `L = thermalGen` (`s45_ibp_mu` with `phi = 1`), `nu beta = 1`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s21_regSlice (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) : HRS.MH.DualityRd.RegSliceRd (thermalDensity d s a β) := by
  obtain ⟨hprob, ψ, hψ⟩ := s21_schwartz_thermal hd hs0 hsd ha hβ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨hcd, Λ, hw⟩ := HRS.MS.UlW.ulw_schwartz_wsup ψ 3 (L := (d : ℝ) + 3) (by linarith)
  have hreg := HRS.MS.Go.s55f_regular_slice (n := 3) 3 le_rfl (le_refl _) hcd hw
  rw [hψ] at hreg
  exact ⟨hprob, hreg.1, hreg.2.1⟩

theorem s21_mf_stationary (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (T : ℝ) :
    IsWholeMeanFieldSolution
      (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d) T (fun _ => ρ) := by
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hgU := s21_gradU_eq hd hs0 hsd ha hβ hρ
  subst hρeq
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hprob := hT.prob
  have hd1 : 1 ≤ d := by omega
  refine ⟨fun t ht => hprob, fun t ht => ?_, fun ψ hψ t ht => ?_⟩
  · have := s21_thermal_second_integrable hd hs0 hsd ha hβ
    have h2 := (HRS.MS.TcR.tc2_integrable_nu hprob (fun x => ‖x‖ ^ 2)).1 this
    exact h2.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)
  · set D : WholeDyn d := ⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ with hD
    have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
      unfold Matrix.IsSymm; simp
    have hVgrad : ∀ x, gradient D.V x = a • x := fun x => by
      show gradient (quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0) x = a • x
      rw [HRS.MS.Adj.ad_gradient_quadV hQ 0 x, s21_matVec_smul_one, add_zero]
    have hreg := s21_regSlice hd hs0 hsd ha hβ
    obtain ⟨hself, -⟩ := HRS.MH.DualityRd.self_pairing_rd_proof D hd1 hs0 hsd hreg hψ
    have hψ1 := hψ.1
    set B := HRS.cbNorm 2 ψ with hB
    have hψ0 : ContDiff ℝ 2 ψ := hψ1
    have hgrad_cont : Continuous (gradient ψ) :=
      (S45.s45_contDiff_gradient hψ0).continuous
    have hlapc := s21_lap_continuous hψ0
    -- integrability of the three pieces
    have hI1 : Integrable (fun x => thermalDensity d s a β x * (β⁻¹ * Laplacian.laplacian ψ x)) := by
      refine s21_gauss_dom hT (hlapc.const_mul β⁻¹).aestronglyMeasurable
        (K := β⁻¹ * (d * B)) fun x => ?_
      rw [abs_mul, abs_of_pos (inv_pos.2 hβ)]
      have := s21_lap_bound hψ x
      have h0 : 0 ≤ β⁻¹ := (inv_pos.2 hβ).le
      have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      have h2 : 0 ≤ β⁻¹ * (d * B) := (mul_nonneg h0 ((abs_nonneg _).trans this))
      nlinarith [mul_le_mul_of_nonneg_left this h0]
    have hI2 : Integrable (fun x => thermalDensity d s a β x * inner ℝ (a • x) (gradient ψ x)) := by
      have hax : Continuous (fun x : Euc d => a • x) := continuous_id.const_smul a
      refine s21_gauss_dom hT (hax.inner hgrad_cont).aestronglyMeasurable
        (K := a * B) fun x => ?_
      calc |inner ℝ (a • x) (gradient ψ x)| ≤ ‖a • x‖ * ‖gradient ψ x‖ := abs_real_inner_le_norm _ _
        _ ≤ (a * ‖x‖) * B := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
            exact mul_le_mul le_rfl (s21_grad_bound hψ x) (norm_nonneg _) (by positivity)
        _ ≤ a * B * (1 + ‖x‖) := by
            have hB0 : 0 ≤ B := (norm_nonneg _).trans (s21_grad_bound hψ 0)
            nlinarith [norm_nonneg x, mul_nonneg ha.le hB0]
    have hI3 : Integrable (fun x => thermalDensity d s a β x * inner ℝ (gradient ψ x)
        (gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x)) := by
      have hU2 : ContDiff ℝ 2 (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) := by
        exact_mod_cast contDiff_infty.1 hT.Usmooth 2
      have hUc : Continuous (gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β))) :=
        (S45.s45_contDiff_gradient hU2).continuous
      refine s21_gauss_dom hT (hgrad_cont.inner hUc).aestronglyMeasurable (K := B * BU) fun x => ?_
      calc |inner ℝ (gradient ψ x)
            (gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x)|
          ≤ ‖gradient ψ x‖ * ‖gradient (HRS.Whole.convMeasure (rieszKernel d s)
            (thermalMeasure d s a β)) x‖ := abs_real_inner_le_norm _ _
        _ ≤ B * BU := mul_le_mul (s21_grad_bound hψ x) (hT.gradU_le x) (norm_nonneg _)
            ((norm_nonneg _).trans (s21_grad_bound hψ 0))
        _ ≤ B * BU * (1 + ‖x‖) := by
            have h0 : 0 ≤ B * BU := mul_nonneg ((norm_nonneg _).trans (s21_grad_bound hψ 0)) hT.BU0
            nlinarith [norm_nonneg x]
    -- the identity `int rho (L psi) = 0`
    have hibp : ∫ y, thermalGen d s a β ψ y ∂(thermalMeasure d s a β) = 0 := by
      have := S45.s45_ibp_mu hT hψ0 (B1 := B) (B2 := B) (s21_grad_bound hψ) (s21_hess_bound hψ)
        (φ := fun _ => (1 : ℝ)) contDiff_const (Bφ := 1) (Dφ := 0) (fun x => by simp) (fun x => by simp)
      have h1 : ∀ y, (fun _ : Euc d => (1 : ℝ)) y * thermalGen d s a β ψ y = thermalGen d s a β ψ y :=
        fun y => one_mul _
      have h2 : ∀ y, inner ℝ (gradient (fun _ : Euc d => (1 : ℝ)) y) (gradient ψ y) = 0 := fun y => by
        have : gradient (fun _ : Euc d => (1 : ℝ)) y = 0 := by
          unfold gradient
          simp
        rw [this, inner_zero_left]
      simp_rw [h1, h2] at this
      simpa using this
    have hibp' : ∫ x, thermalDensity d s a β x * thermalGen d s a β ψ x = 0 := by
      have e := HRS.Whole.Q09A.pair_withDensityReal hprob (thermalGen d s a β ψ)
      rw [← e]
      exact hibp
    have hgen : ∀ x, thermalGen d s a β ψ x = -Laplacian.laplacian ψ x +
        β * (inner ℝ (a • x) (gradient ψ x) +
          inner ℝ (gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x)
            (gradient ψ x)) := fun x => by
      rw [S45.s45_gen_eq (hT.Usmooth.differentiable (by simp)) x, inner_add_left]
    -- the total
    have hpair := HRS.Whole.Q09A.pair_withDensityReal hprob
      (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x))
    have hK0 : HRS.Whole.pair (HRS.Whole.withDensityReal (thermalDensity d s a β))
        (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)) +
        interactionPairingW D ψ (HRS.Whole.withDensityReal (thermalDensity d s a β))
          (HRS.Whole.withDensityReal (thermalDensity d s a β)) = 0 := by
      rw [hpair, hself]
      have hDM : D.M = -1 := rfl
      have hDinv : D.invβ = β⁻¹ := rfl
      have hDs : D.s = s := rfl
      simp only [hDM, hDinv, hDs, s21_matVec_neg_one, hVgrad, inner_neg_right]
      simp only [hgU]
      set ρ := thermalDensity d s a β with hρdef
      set U := HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) with hUdef
      have e1 : ∀ x, ρ x * (β⁻¹ * Laplacian.laplacian ψ x - inner ℝ (a • x) (gradient ψ x)) =
          ρ x * (β⁻¹ * Laplacian.laplacian ψ x) - ρ x * inner ℝ (a • x) (gradient ψ x) := fun x => by ring
      have e2 : ∀ x, ρ x * -inner ℝ (gradient ψ x) (gradient U x) =
          -(ρ x * inner ℝ (gradient ψ x) (gradient U x)) := fun x => by ring
      simp_rw [e1, e2]
      rw [integral_sub hI1 hI2, integral_neg]
      have hpt : ∀ x, ρ x * thermalGen d s a β ψ x =
          -β * (ρ x * (β⁻¹ * Laplacian.laplacian ψ x)) + β * (ρ x * inner ℝ (a • x) (gradient ψ x)) +
            β * (ρ x * inner ℝ (gradient ψ x) (gradient U x)) := fun x => by
        rw [hgen x, real_inner_comm (gradient ψ x) (gradient U x)]
        field_simp
        ring
      have hA := hI1.const_mul (-β)
      have hB := hI2.const_mul β
      have hC := hI3.const_mul β
      have hAB : Integrable (fun x => -β * (ρ x * (β⁻¹ * Laplacian.laplacian ψ x)) +
          β * (ρ x * inner ℝ (a • x) (gradient ψ x))) := hA.add hB
      set J1 : ℝ := ∫ x, ρ x * (β⁻¹ * Laplacian.laplacian ψ x) with hJ1
      set J2 : ℝ := ∫ x, ρ x * inner ℝ (a • x) (gradient ψ x) with hJ2
      set J3 : ℝ := ∫ x, ρ x * inner ℝ (gradient ψ x) (gradient U x) with hJ3
      have hsum : ∫ x, ρ x * thermalGen d s a β ψ x = -β * J1 + β * J2 + β * J3 := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hAB hC,
          integral_add hA hB, integral_const_mul, integral_const_mul, integral_const_mul]
      rw [hibp'] at hsum
      have hβ0 : β ≠ 0 := hβ.ne'
      have : β * ((J1 - J2) + -J3) = 0 := by linear_combination hsum
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hβ0
      · exact h
    have hint0 : ∀ r : ℝ, HRS.Whole.pair (HRS.Whole.withDensityReal ((fun _ : ℝ => thermalDensity d s a β) r))
        (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)) +
        interactionPairingW D ψ (HRS.Whole.withDensityReal ((fun _ : ℝ => thermalDensity d s a β) r))
          (HRS.Whole.withDensityReal ((fun _ : ℝ => thermalDensity d s a β) r)) = 0 := fun r => hK0
    simp only [sub_self]
    rw [setIntegral_congr_fun measurableSet_Icc (fun r _ => hint0 r)]
    simp

end HRS.MS.S21
