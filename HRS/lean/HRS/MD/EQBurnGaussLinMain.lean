import HRS.MD.EQBurnGaussLinLaw

/-!
# EQ-BURN P2 (`eq_gauss_lin`), part 4: independence of `G` and `Z 0`, and the main theorem

`(G_a)_a` and `(Z^0(e_k))_k` are jointly Gaussian (linear images of the Gaussian process `eglB`) and uncorrelated, hence
independent (`IsGaussianProcess.indepFun_of_covariance_eq_zero`); the real modes `e_k` generate the Borel σ-algebra of `E_m`
(`eqgw_measurable_of_coord`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.MD.EQGaussLyapDet HRS.MD.EQGaussLyapDet2

namespace HRS.MD.EQBurnGaussLin

variable {d : ℕ}

section Indep

variable (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
  (hV : Torus.IsSmooth V) (hβ : 0 < β) (ρβ : Torus d → ℝ)
  (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {m : ℝ}
  {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m}

include hd hV hρβ in
/-- The increment vector `G` is independent of `Z 0`. -/
theorem egl_indep (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z) {p : ℕ}
    (τ : Fin p → ℝ) (hτ : ∀ a, 0 ≤ τ a) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    IndepFun (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (Z (τ a) ω) (φ a) - NegSobolev.eval (Z 0 ω)
          (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (τ a) (φ a)) :
        EuclideanSpace ℝ (Fin p))) (Z 0) P := by
  classical
  set D := mfData d s hs0 hsd V β hβ with hD
  let U : Fin p → Torus d → ℝ := fun a => propagator D (fun _ => ρβ) 0 (τ a) (φ a)
  have hU : ∀ a, Torus.IsSmooth (U a) := fun a =>
    egl_prop_smooth hd hs0 hsd V hV hβ ρβ hρβ (hφ a) (hτ a)
  have hgp := egl_gp hZ
  let xa : Fin p → EglIdx d := fun a => ⟨(τ a, φ a), hτ a, hφ a⟩
  let ya : Fin p → EglIdx d := fun a => ⟨(0, U a), le_rfl, hU a⟩
  let zk : NonzeroLattice d → EglIdx d := fun k =>
    ⟨(0, Torus.realMode k), le_rfl, HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k⟩
  let Xf : Fin p → Ω → ℝ := fun a ω => eglB Z (xa a) ω - eglB Z (ya a) ω
  let Yf : NonzeroLattice d → Ω → ℝ := fun k ω => eglB Z (zk k) ω
  have hGP : IsGaussianProcess (Sum.elim Xf Yf) P := by
    refine hgp.of_isGaussianProcess fun t => ?_
    rcases t with a | k
    · refine ⟨{xa a, ya a}, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({xa a, ya a} : Finset (EglIdx d)) => ℝ)
        ⟨xa a, by simp⟩ - ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : ({xa a, ya a} : Finset (EglIdx d)) => ℝ) ⟨ya a, by simp⟩, fun ω => ?_⟩
      rfl
    · refine ⟨{zk k}, ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : ({zk k} : Finset (EglIdx d)) => ℝ) ⟨zk k, by simp⟩, fun ω => ?_⟩
      rfl
  have hmX : ∀ a, AEMeasurable (Xf a) P := fun a =>
    ((egl_B_measurable hZ (xa a)).sub (egl_B_measurable hZ (ya a))).aemeasurable
  have hmY : ∀ k, AEMeasurable (Yf k) P := fun k => (egl_B_measurable hZ (zk k)).aemeasurable
  have hcov : ∀ a k, cov[Xf a, Yf k; P] = 0 := by
    intro a k
    have m1 := (hgp.hasGaussianLaw_eval (xa a)).memLp_two
    have m2 := (hgp.hasGaussianLaw_eval (ya a)).memLp_two
    have m3 := (hgp.hasGaussianLaw_eval (zk k)).memLp_two
    have h0 : cov[Xf a, Yf k; P] = cov[eglB Z (xa a) - eglB Z (ya a), eglB Z (zk k); P] := rfl
    rw [h0, covariance_sub_left m1 m2 m3, egl_cov2 hd hs0 hsd V hV hβ ρβ hρβ P hZ,
      egl_cov2 hd hs0 hsd V hV hβ ρβ hρβ P hZ]
    have e1 : eglK d s β D ρβ (xa a).1 (zk k).1 =
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (U a) (Torus.realMode k) :=
      eglK_zero_right hd hs0 hsd V hV hβ ρβ hρβ (hτ a) (hφ a)
        (HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k)
    have e2 : eglK d s β D ρβ (ya a).1 (zk k).1 =
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (U a) (Torus.realMode k) :=
      eglK_zero_zero hd hs0 hsd V hV hβ ρβ hρβ (hU a) (HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k)
    rw [e1, e2, sub_self]
  have hind := hGP.indepFun_of_covariance_eq_zero hmX hmY hcov
  -- from the coordinate process to the random element `Z 0`
  let Yvec : Ω → (NonzeroLattice d → ℝ) := fun ω k => Yf k ω
  have h1 : IndepFun (fun ω => (WithLp.toLp 2 fun a => Xf a ω : EuclideanSpace ℝ (Fin p))) Yvec P :=
    hind.comp (f := fun ω a => Xf a ω) (g := fun ω k => Yf k ω)
      (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable measurable_id
  rw [IndepFun_iff_Indep] at h1 ⊢
  refine indep_of_indep_of_le_right h1 ?_
  have hmc : Measurable[MeasurableSpace.comap Yvec inferInstance] Yvec := comap_measurable Yvec
  have hcoord : ∀ k, Measurable[MeasurableSpace.comap Yvec inferInstance]
      (fun ω => NegSobolev.coord (Z 0 ω) k) := by
    intro k
    have hj := Torus.jp_pos k.1
    have hne : Lattice.jp k.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos hj m).ne'
    have e : (fun ω => NegSobolev.coord (Z 0 ω) k) = fun ω => (Lattice.jp k.1 ^ m)⁻¹ * Yvec ω k := by
      funext ω
      have h2 : Yvec ω k = Lattice.jp k.1 ^ m * NegSobolev.coord (Z 0 ω) k := by
        show NegSobolev.eval (Z 0 ω) (Torus.realMode k) = _
        rw [HRS.MD.EQGaussWindow.eqgw_eval_realMode]
        rfl
      rw [h2, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [e]
    exact ((measurable_pi_apply k).comp hmc).const_mul _
  have hZ0 : Measurable[MeasurableSpace.comap Yvec inferInstance] (Z 0) :=
    @HRS.MD.EQGaussWindow.eqgw_measurable_of_coord d Ω (MeasurableSpace.comap Yvec inferInstance) m
      (Z 0) hcoord
  exact hZ0.comap_le

end Indep

section Main

open HRS.MD.EQBurnGaussLin

/-- (P2 `EQ-GAUSS-LIN`.)  An `IsStationaryGaussianField` on `[0,∞)` is, on every horizon `S ≥ 0`, a linear fluctuation solution. -/
theorem eq_gauss_lin_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (S : ℝ) (hS : 0 ≤ S)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z) :
    IsLinearFluctuationSolution P' (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m β⁻¹ S (Z 0) Z := by
  refine ⟨ae_of_all _ fun ω => rfl, ?_, hZ.meas, ?_⟩
  · filter_upwards [hZ.cont] with ω hω
    exact hω.mono fun t ht => ht.1
  · intro p ts φ hts hφ
    have hts' : ∀ a, 0 ≤ ts a := fun a => (hts a).1
    exact ⟨egl_indep hd hs0 hsd V hV hβ ρβ hρβ P' hZ ts hts' φ hφ,
      egl_law hd hs0 hsd V hV hβ ρβ hρβ P' hZ ts hts' φ hφ⟩

end Main

end HRS.MD.EQBurnGaussLin

end
