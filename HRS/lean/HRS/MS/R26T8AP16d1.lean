import HRS.MS.R26T8AP16c
import HRS.MS.R26T8AP11g10

/-!
# S8.2 T8A P16d1: weak form of the local operator row
`ρ Lop Q(.,y) = ν div(ρ ∇ Q(.,y))` off `y`; for a compactly supported smooth `φ`:
`∫ φ ρ Lop Q(.,y) dx = -ν ∫ Σ_j ∂_jφ ρ dx_j Q(.,y) dx`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 6400000 in
theorem r26t8a_comm_ibp (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma A : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsigma : sigma < d) (hA : 0 ≤ A) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Q : Euc d → Euc d → ℝ) (hQ : Conormal (k + 2) b M (sigma - 2) A Q)
    (φ : Euc d → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (y : Euc d) :
    ∫ x, φ x * (rho x * r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x) =
      -(beta⁻¹ * ∫ x, ∑ j : Fin d, fderiv ℝ φ x (EuclideanSpace.single j 1) *
        (rho x * r26t8a_dx j Q x y)) := by
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
  obtain ⟨B0, hB0⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  obtain ⟨B1, hB1⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
  obtain ⟨-, -, hI3⟩ := r26t8a_g2_ibp H (Γ := φ) hφ1 (B0 := B0) (B1 := B1)
    (fun u => by simpa using hB0 u) (fun u => hB1 u)
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
  -- the pointwise identity
  have hLop : ∀ x, r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x =
      beta⁻¹ * Laplacian.laplacian (fun z => Q z y) x +
        inner ℝ ((critCoeff d a beta rho).drift 0 x) (pairGradX Q x y) := by
    intro x
    unfold r26t8a_Lop
    rw [r26t8a_critCoeff_nu]
    rfl
  have e1 : ∫ x, φ x * (rho x * r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x) =
      beta⁻¹ * ∫ x, φ x * r26t8a_divh h x := by
    have : ∀ x, φ x * (rho x * r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x) =
        beta⁻¹ * (φ x * r26t8a_divSource rho Q x y) := by
      intro x
      rw [hLop x]
      linear_combination (φ x) * hpt x
    simp only [this]
    rw [integral_const_mul]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hdivae] with u hu
    rw [hu]
  rw [e1, hI3, mul_neg]
  refine congrArg Neg.neg (congrArg (HMul.hMul beta⁻¹) ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : ∀ L : Euc d →L[ℝ] ℝ, ((InnerProductSpace.toDual ℝ (Euc d)).symm L).ofLp j =
      L (EuclideanSpace.single j 1) := by
    intro L
    have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single j 1) (y := L)
    rw [EuclideanSpace.inner_single_right] at h1
    simpa using h1
  simp only [hh, PiLp.smul_apply, smul_eq_mul, r26t8a_dx, gradient]
  rw [hc]

end HRS.MS.R26T8A
