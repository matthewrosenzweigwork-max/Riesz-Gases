import HRS.MS.R26T8AP10a17
import HRS.MS.WadAux22
import HRS.Whole.Critical

/-!
# S8.2 T8A P10a: potential identity for an arbitrary conormal pair section
`r26t8a_conormal_potential_ibp` (Pro contract, verbatim).  Proof: with `f = Q(·,y)`, `h = ρ ∇f` (`R26P10Hyp`, from the slice jets of
`Conormal`), `oneJ = ∑_j (∇g ⋆ (ρ ∂_j f))_j` is the cancellation form `∫ Ecan0`, which equals `∫ g(x-u) div h(u) du` (`r26t8a_p10a_core`:
regularise `g_ε = (|w|²+ε²)^(-s/2)`, cut off the `y`-pole by `1 - chi((u-y)/δ)`, integrate by parts on the whole space, let `δ → 0`, then `ε → 0`),
and `div h = divSource`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_conv_neg (G : Euc d → Euc d) (φ : Euc d → ℝ) (x : Euc d) :
    convGradConvW G (fun y => - φ y) x = - convGradConvW G φ x := by
  unfold convGradConvW
  rw [← integral_neg]
  congr 1; funext y
  by_cases h : ‖x - y‖ ≤ 1 / 4
  · simp only [if_pos h]; rw [← neg_smul]; congr 1; ring
  · simp only [if_neg h]; rw [← neg_smul]

theorem r26t8a_oneJ_crit (d : ℕ) (a β : ℝ) (ρ : Euc d → ℝ) (f : Euc d → ℝ) (x : Euc d) :
    oneJ (critCoeff d a β ρ) f x =
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d (criticalS d))
        (fun w => ρ w * (gradient f w) j) x) j := by
  have hM : ∀ v : Euc d, (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose v) = -v := by
    intro v
    simp [Torus.matVec]
  unfold oneJ generatorW critCoeff quadraticGradientDyn WholeDyn.coeff
  simp only [hM, PiLp.neg_apply, mul_neg]
  have : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d (d / 2 : ℝ)) (fun y => -(ρ y * (gradient f y) j)) x) j =
      - (convGradConvW (rieszKernelGrad d (d / 2 : ℝ)) (fun y => ρ y * (gradient f y) j) x) j := by
    intro j
    rw [r26t8a_conv_neg]; rfl
  simp only [this, Finset.sum_neg_distrib]
  unfold criticalS
  ring

theorem r26t8a_p10a_divh_eq {Q : Euc d → Euc d → ℝ} {y u : Euc d} {ρ : Euc d → ℝ}
    (hρ : Differentiable ℝ ρ) (hf : ContDiffAt ℝ 2 (fun v => Q v y) u) :
    r26t8a_divh (fun w => ρ w • gradient (fun v => Q v y) w) u = r26t8a_divSource ρ Q u y := by
  set f : Euc d → ℝ := fun v => Q v y with hfdef
  have hDD : DifferentiableAt ℝ (fderiv ℝ f) u :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (gradient f) u := by
    rw [r26t8a_gradient_eq_Rz]
    exact (r26t8a_Rz d).differentiableAt.comp u hDD
  have hD : fderiv ℝ (gradient f) u = (r26t8a_Rz d).comp (fderiv ℝ (fderiv ℝ f) u) := by
    have : gradient f = (r26t8a_Rz d) ∘ fderiv ℝ f := r26t8a_gradient_eq_Rz f
    rw [this, ((r26t8a_Rz d).hasFDerivAt.comp u hDD.hasFDerivAt).fderiv]
  unfold r26t8a_divh r26t8a_divSource pairGradX
  rw [fderiv_fun_smul (hρ u) hdf, hD]
  have hpt : ∀ j : Fin d, ((ρ u • (r26t8a_Rz d).comp (fderiv ℝ (fderiv ℝ f) u) +
      (fderiv ℝ ρ u).smulRight (gradient f u)) (EuclideanSpace.single j 1)) j =
      ρ u * fderiv ℝ (fderiv ℝ f) u (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) +
        fderiv ℝ ρ u (EuclideanSpace.single j 1) * (gradient f u) j := by
    intro j
    simp [r26t8a_Rz]
  simp only [hpt, Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.mul_sum]
    congr 1
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedFDeriv_two_apply]
    simp
  · rw [real_inner_comm]
    simp only [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [r26t8a_gradient_coord]
    exact Or.inl rfl

theorem r26t8a_conormal_potential_ibp (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Q : Euc d → Euc d → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hQ : Conormal (k + 2) b M (sigma - 2) A Q) :
    ∀ x y, x ≠ y → Integrable (fun u => rieszKernel d (criticalS d) (x - u) * r26t8a_divSource rho Q u y) ∧
      oneJ (critCoeff d a beta rho) (fun u => Q u y) x =
        ∫ u, rieszKernel d (criticalS d) (x - u) * r26t8a_divSource rho Q u y := by
  intro x y hxy
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd' : criticalS d < d := by unfold criticalS; linarith
  have hgs := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := hgs
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith) ha hbeta
      hrho).1
  obtain ⟨τ, H⟩ := r26t8a_p10a_hyp hd hM hsd hA hQ hρs hC hc (fun x => (hb x).1) (fun x => (hb x).2) y
  have core := r26t8a_p10a_core H hs0 hsd' hxy
  have hker : ∀ w : Euc d, rieszKernel d (criticalS d) w = ‖w‖ ^ (-criticalS d) := fun w => by
    rw [rieszKernel, if_neg hs0.ne']
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hf2 : ContDiffOn ℝ 2 (fun v => Q v y) {y}ᶜ := by
    have hg : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (fun v : Euc d => (v, y)) :=
      contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    have := hQ.1.comp hg.contDiffOn hmaps
    exact this.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
  have hdiv : ∀ᵐ u : Euc d ∂volume, r26t8a_divSource rho Q u y =
      r26t8a_divh (fun w => rho w • gradient (fun v => Q v y) w) u := by
    filter_upwards [hae] with u hu
    exact (r26t8a_p10a_divh_eq hdiff
      (hf2.contDiffAt (hopen.mem_nhds (by simpa using hu)))).symm
  have hcongr : (fun u => rieszKernel d (criticalS d) (x - u) * r26t8a_divSource rho Q u y) =ᵐ[volume]
      fun u => ‖x - u‖ ^ (-criticalS d) *
        r26t8a_divh (fun w => rho w • gradient (fun v => Q v y) w) u := by
    filter_upwards [hdiv] with u hu
    rw [hker, hu]
  refine ⟨(core.1).congr hcongr.symm, ?_⟩
  rw [integral_congr_ae hcongr, core.2, ← r26t8a_p10a_conv_sum H hs0 hsd' hxy, r26t8a_oneJ_crit]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]

end HRS.MS.R26T8A
