import HRS.MS.R26T8AA03
import HRS.MS.R26T8AP16b

/-!
# S8.2 T8A P16c: the local generator rows of a conormal pair function (general order)
`r26t8a_local_ibp_gen`: A03 for `Conormal (k+2) b M (sigma-2) A Q` with `sigma < d` instead of `PairCorrector`
(the proof of A03 only uses this conormal bound): `∫ (nu Δ + b·∇) Q(.,y) dmu = 0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 6400000 in
theorem r26t8a_local_ibp_gen (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma A : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsigma : sigma < d) (hA : 0 ≤ A) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Q : Euc d → Euc d → ℝ) (hQ : Conormal (k + 2) b M (sigma - 2) A Q) :
    ∀ y, Integrable (fun x => beta⁻¹ * Laplacian.laplacian (fun z => Q z y) x +
      inner ℝ ((critCoeff d a beta rho).drift 0 x) (pairGradX Q x y)) (HRS.Whole.withDensityReal rho) ∧
      ∫ x, beta⁻¹ * Laplacian.laplacian (fun z => Q z y) x +
        inner ℝ ((critCoeff d a beta rho).drift 0 x) (pairGradX Q x y) ∂HRS.Whole.withDensityReal rho = 0 := by
  intro y
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsc : criticalS d < d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsc ha hbeta hrho).1
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0.le hsc ha hbeta hrho
  have hpos : ∀ x, 0 < rho x := fun x => hR.pos x
  obtain ⟨τ, H⟩ := r26t8a_p10a_hyp hd hM hsigma hA hQ hρs hC hc (fun x => (hb x).1)
    (fun x => (hb x).2) y
  set h : Euc d → Euc d := fun w => rho w • gradient (fun v => Q v y) w with hh
  obtain ⟨hI1, -, hI3⟩ := r26t8a_g2_ibp H (Γ := fun _ => (1 : ℝ)) contDiff_const (B0 := 1) (B1 := 0)
    (fun u => by simp) (fun u => by simp)
  have hdivI : Integrable (r26t8a_divh h) := by simpa using hI1
  have hdiv0 : ∫ u, r26t8a_divh h u = 0 := by simpa using hI3
  -- divSource = divh off `y`
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.1.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hf2 : ContDiffOn ℝ 2 (fun v => Q v y) {y}ᶜ := by
    have hg : ContDiff ℝ 2 (fun v : Euc d => (v, y)) := contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    exact hQ2.comp hg.contDiffOn hmaps
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
  have hdivae : ∀ᵐ u : Euc d ∂volume, r26t8a_divSource rho Q u y = r26t8a_divh h u := by
    filter_upwards [hae] with u hu
    exact (r26t8a_p10a_divh_eq hdiff (hf2.contDiffAt (hopen.mem_nhds (by simpa using hu)))).symm
  -- the drift and the density gradient
  have hdr : ∀ x, (critCoeff d a beta rho).drift 0 x = beta⁻¹ • gradient (fun t => Real.log (rho t)) x := by
    intro x
    have E := HRS.MS.Mov0.mv0_thermal_force hd hs0.le hsc ha hbeta hrho x
    have hV := movtr_gradient_confinement (d := d) a x
    show meanFieldDriftW (quadraticGradientDyn d ((d : ℝ) / 2) a beta) rho x = _
    unfold meanFieldDriftW
    simp only [quadraticGradientDyn, hV]
    have hM : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) rho x) =
        -convGradConvW (rieszKernelGrad d (criticalS d)) rho x := by
      simp [Torus.matVec, criticalS]
    rw [hM]
    exact (eq_sub_of_add_eq (eq_neg_of_add_eq_zero_left E)).symm
  have hgr : ∀ x, gradient rho x = rho x • gradient (fun t => Real.log (rho t)) x := by
    intro x
    have hρx : rho x ≠ 0 := (hpos x).ne'
    have hf : HasFDerivAt (fun t => Real.log (rho t)) ((rho x)⁻¹ • fderiv ℝ rho x) x :=
      (hdiff x).hasFDerivAt.log hρx
    have : gradient (fun t => Real.log (rho t)) x = (rho x)⁻¹ • gradient rho x := by
      refine ext_inner_left ℝ fun v => ?_
      rw [HRS.MS.PoisKolm.kl_inner_gradient, hf.fderiv, ContinuousLinearMap.smul_apply,
        ← HRS.MS.PoisKolm.kl_inner_gradient rho x v, inner_smul_right]
      simp
    rw [this, smul_smul, mul_inv_cancel₀ hρx, one_smul]
  have hpt : ∀ x, rho x * (beta⁻¹ * Laplacian.laplacian (fun z => Q z y) x +
      inner ℝ ((critCoeff d a beta rho).drift 0 x) (pairGradX Q x y)) =
      beta⁻¹ * r26t8a_divSource rho Q x y := by
    intro x
    unfold r26t8a_divSource
    rw [hdr x, hgr x]
    simp only [inner_smul_left, conj_trivial, pairGradX]
    ring
  have hint : Integrable (fun x => rho x * (beta⁻¹ * Laplacian.laplacian (fun z => Q z y) x +
      inner ℝ ((critCoeff d a beta rho).drift 0 x) (pairGradX Q x y))) := by
    have h1 : Integrable (fun x => beta⁻¹ * r26t8a_divh h x) := hdivI.const_mul _
    refine h1.congr ?_
    filter_upwards [hdivae] with x hx
    rw [hpt x, hx]
  refine ⟨(r26t8a_f25_wd_integrable hprob _).2 hint, ?_⟩
  rw [r26t8a_f25_wd_integral hprob]
  have e : (fun x => rho x * (beta⁻¹ * Laplacian.laplacian (fun z => Q z y) x +
      inner ℝ ((critCoeff d a beta rho).drift 0 x) (pairGradX Q x y))) =
      fun x => beta⁻¹ * r26t8a_divSource rho Q x y := funext hpt
  rw [e, integral_const_mul, integral_congr_ae hdivae, hdiv0, mul_zero]

end HRS.MS.R26T8A
