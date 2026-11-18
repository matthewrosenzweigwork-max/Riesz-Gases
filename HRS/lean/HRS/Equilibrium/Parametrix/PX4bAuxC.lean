import HRS.Equilibrium.Parametrix.PX4bAuxB
import HRS.Equilibrium.Parametrix.PX3aAuxAA
import HRS.Equilibrium.Parametrix.PX2AuxE
import HRS.Equilibrium.Parametrix.PX1AuxExtApply

/-!
# Packet PX4b auxiliaries C: slices of conormal kernels are `Nice`, `Bop` is integrable
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma px4b_conormal_zero_const {σ : ℝ} {b : ℕ → ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b 0 B F) : Conormal σ (b 0) 0 B F where
  smooth := hF.smooth
  near a c hac X z hz hzr := by
    have ha : a = 0 := by omega
    have hc : c = 0 := by omega
    subst ha; subst hc
    exact hF.near 0 0 hac X z hz hzr
  far := hF.far

/-- Slices (in the first variable) of a conormal kernel of order `< d` are `μ`-integrable. -/
theorem px4b_slice_int (hd : 2 ≤ d) (hρ : SmoothPosDensity ρ) {σ : ℝ} (hσ : σ < d) {b : ℕ → ℕ}
    {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hF : ConormalL σ b m B F) (y : Torus d) :
    Integrable (fun x => F x y) (withDensityReal ρ) := by
  have hB := conormalL_B_nonneg hd hF
  have hc := px4b_conormal_zero_const (conormalL_mono_m (Nat.zero_le m) hF)
  have hH : Conormal σ (b 0) 0 B (offZero F) :=
    conormalL_congr_offDiag (fun x y hxy => by simp [offZero, hxy]) hc
  have hdiag : ∀ x, swapK (offZero F) x x = 0 := fun x => by simp [swapK, offZero]
  obtain ⟨K, hK0, hK⟩ := conormal_row_int hd hρ hσ (b 0)
  have := (hK B (swapK (offZero F)) hB (conormalL_swap hH) hdiag y).1
  refine this.congr ?_
  filter_upwards [px4b_ae_ne_mu (by omega) ρ y] with x hx
  simp [swapK, offZero, hx]

lemma px4b_slice_c2 {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hm : 2 ≤ m) (hF : ConormalL σ b m B F) (y : Torus d) :
    ∀ v : Euc d, Torus.mk v ≠ y → ContDiffAt ℝ 2 (Torus.lift (fun x => F x y)) v := by
  intro v hv
  have hp : (v, Torus.rep y) ∈ offDiag d := by
    show Torus.mk v ≠ Torus.mk (Torus.rep y)
    rwa [Torus.mk_rep]
  have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) (lift2 F) (v, Torus.rep y) :=
    hF.smooth.contDiffAt (isOpen_offDiag.mem_nhds hp)
  have h2 : ContDiffAt ℝ 2 (lift2 F) (v, Torus.rep y) := h1.of_le (by exact_mod_cast hm)
  have h3 : ContDiffAt ℝ 2 (fun w : Euc d => lift2 F (w, Torus.rep y)) v :=
    h2.comp v (contDiffAt_id.prodMk contDiffAt_const)
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [Torus.lift, Function.comp, lift2]
  rw [Torus.mk_rep]

lemma px4b_withDensity_int (hρ : SmoothPosDensity ρ) {k : Torus d → ℝ}
    (hk : Integrable k (withDensityReal ρ)) : Integrable (fun u => ρ u * k u) := by
  have hmeas : Measurable fun x => ENNReal.ofReal (ρ x) := by
    have : Continuous ρ := continuous_of_isSmooth hρ.smooth
    exact ENNReal.measurable_ofReal.comp this.measurable
  have h := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Torus d)))
    hmeas (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (g := k)).1 hk
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ.pos x).le]

theorem px4b_slice_nice (hd : 2 ≤ d) (hρ : SmoothPosDensity ρ) {σ : ℝ} (hσ : σ + 2 < d)
    {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hm : 2 ≤ m)
    (hF : ConormalL σ b m B F) (y : Torus d) : Nice ρ y (fun x => F x y) := by
  refine ⟨px4b_slice_c2 hm hF y, fun j => ?_⟩
  have hK1 := conormal_partial_fst_aux hF (by omega : 1 ≤ m) j
  have := px4b_slice_int hd hρ (σ := σ + 1) (by linarith) hK1 y
  exact px4b_withDensity_int hρ this


/-- Gibbs relation: `∇V + F_μ = -β⁻¹ ∇ρ / ρ`. -/
theorem px4b_drift (H : ParxHyp d s V β ρ) (x : Torus d) (j : Fin d) :
    Torus.partialDeriv j V x + (forceField d s ρ x) j =
      -β⁻¹ * (Torus.partialDeriv j ρ x / ρ x) := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hV1 : Torus.IsCk 1 V := PDE.MFPair.isCk_of_smooth_ps H.V_smooth 1
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  obtain ⟨-, hdiff⟩ := MFAux.gibbs_partialDeriv V ρ (convFun (periodicRiesz d s) ρ) β H.beta_pos.ne'
    (∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y))) hρ1 hV1 hρ.pos H.thermal.2
  have hconv : convMeasure (periodicRiesz d s) (withDensityReal ρ) = convFun (periodicRiesz d s) ρ := by
    funext z
    unfold convMeasure convFun
    rw [integral_withDensityReal_eq ρ hρc.measurable (fun y => (hρ.pos y).le)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  unfold forceField
  rw [hconv, MFAux.grad_apply, hdiff j x]
  ring

lemma px4b_laplacian_eq {f : Torus d → ℝ} {x : Torus d} (hf : ContDiffAt ℝ 2 (Torus.lift f) (Torus.rep x)) :
    Torus.laplacian f x = ∑ i, Torus.partialDeriv i (fun u => Torus.partialDeriv i f u) x := by
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift f)
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  have hD : HasFDerivAt (fderiv ℝ (Torus.lift f)) (fderiv ℝ (fderiv ℝ (Torus.lift f)) (Torus.rep x))
      (Torus.rep x) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have h2 := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)).hasFDerivAt.comp
    (Torus.rep x) hD
  have h3 : fderiv ℝ (fun y => fderiv ℝ (Torus.lift f) y (EuclideanSpace.basisFun (Fin d) ℝ i))
      (Torus.rep x) = (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) ∘L
        fderiv ℝ (fderiv ℝ (Torus.lift f)) (Torus.rep x) := h2.fderiv
  have e : Torus.lift (fun u => Torus.partialDeriv i f u) =
      fun y => fderiv ℝ (Torus.lift f) y (EuclideanSpace.basisFun (Fin d) ℝ i) := by
    funext w
    rw [px4b_lift_partialDeriv]
    simp [EuclideanSpace.basisFun_apply]
  rw [px4b_partialDeriv_eq (fun u => Torus.partialDeriv i f u) i x, e, h3]
  simp [EuclideanSpace.basisFun_apply]

/-- `Bop` through partial derivatives (Gibbs relation). -/
lemma px4b_Bop_eq (H : ParxHyp d s V β ρ) {f : Torus d → ℝ} {x : Torus d}
    (hf : ContDiffAt ℝ 2 (Torus.lift f) (Torus.rep x)) :
    Bop d s V β ρ f x = β⁻¹ * ∑ i, Torus.partialDeriv i (fun u => Torus.partialDeriv i f u) x +
      β⁻¹ * ∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x := by
  unfold Bop
  rw [px4b_laplacian_eq hf, PiLp.inner_apply]
  have e : ∀ i, inner ℝ ((Torus.grad V x + forceField d s ρ x).ofLp i) ((Torus.grad f x).ofLp i) =
      -β⁻¹ * (Torus.partialDeriv i ρ x / ρ x) * Torus.partialDeriv i f x := by
    intro i
    rw [real_inner_eq_re_inner, ← px4b_drift H x i]
    simp [MFAux.grad_apply]
    ring
  simp_rw [e]
  rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring


theorem px4b_Bop_int (H : ParxHyp d s V β ρ) {σ : ℝ} (hσ : σ + 2 < d) {b : ℕ → ℕ} {m : ℕ} {B : ℝ}
    {F : Torus d → Torus d → ℝ} (hm : 2 ≤ m) (hF : ConormalL σ b m B F) (y : Torus d) :
    Integrable (fun u => Bop d s V β ρ (fun x => F x y) u) (withDensityReal ρ) := by
  have hρ := H.rho_smooth
  have hd := H.two_le
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := continuous_of_isSmooth hρ.smooth
  have hK1 := fun j => conormal_partial_fst_aux hF (by omega : 1 ≤ m) j
  have hK2 := fun i j => conormal_partial_fst_aux (hK1 j) (by omega : 1 ≤ m - 1) i
  have I1 : ∀ j, Integrable (fun u => Torus.partialDeriv j (fun x => F x y) u) (withDensityReal ρ) :=
    fun j => px4b_slice_int hd hρ (σ := σ + 1) (by linarith) (hK1 j) y
  have I2 : ∀ i, Integrable (fun u => Torus.partialDeriv i (fun z => Torus.partialDeriv i
      (fun x => F x y) z) u) (withDensityReal ρ) :=
    fun i => px4b_slice_int hd hρ (σ := σ + 1 + 1) (by linarith) (hK2 i i) y
  have hq : ∀ j, Continuous (fun u => Torus.partialDeriv j ρ u / ρ u) := fun j =>
    (PDE.continuous_partialDeriv j ρ hρ1).div hρc (fun u => (hρ.pos u).ne')
  have I3 : ∀ j, Integrable (fun u => (Torus.partialDeriv j ρ u / ρ u) *
      Torus.partialDeriv j (fun x => F x y) u) (withDensityReal ρ) := by
    intro j
    obtain ⟨C, hC⟩ := PDE.MFSchauder.exists_bound_of_cont (hq j)
    refine (I1 j).bdd_mul (c := C) (hq j).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]; exact hC u
  have hsum := ((integrable_finsetSum Finset.univ fun i _ => (I2 i).const_mul β⁻¹)).add
    ((integrable_finsetSum Finset.univ fun j _ => (I3 j).const_mul β⁻¹))
  refine hsum.congr ?_
  filter_upwards [px4b_ae_ne_mu (by omega) ρ y] with u hu
  have hc2 : ContDiffAt ℝ 2 (Torus.lift (fun x => F x y)) (Torus.rep u) :=
    px4b_slice_c2 hm hF y _ (by rwa [Torus.mk_rep])
  rw [px4b_Bop_eq H hc2]
  simp only [Pi.add_apply, Finset.mul_sum]


/-- Smooth (`C²`) slices: `Nice`, and `Bop + Jop` is continuous, hence `μ`-integrable. -/
theorem px4b_smooth_slice (H : ParxHyp d s V β ρ) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f)
    (y : Torus d) : Nice ρ y f ∧ Integrable (fun u => Bop d s V β ρ f u) (withDensityReal ρ) ∧
      Integrable (fun u => Jop d s ρ f u) (withDensityReal ρ) := by
  have hρ := H.rho_smooth
  have hd := H.two_le
  have hd1 : 1 ≤ d := by omega
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := continuous_of_isSmooth hρ.smooth
  have hf1 : Torus.IsCk 1 f := hf.of_le (by norm_num)
  have hpd : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j f) := fun j =>
    PDE.ProdAux.isCk_partialDeriv (n := 1) (by exact_mod_cast hf) j
  have hpdc : ∀ j, Continuous (Torus.partialDeriv j f) := fun j =>
    PDE.continuous_partialDeriv j f hf1
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  refine ⟨⟨fun v _ => (show ContDiff ℝ 2 (Torus.lift f) from hf).contDiffAt, fun j => ?_⟩, ?_⟩
  · exact (hρc.mul (hpdc j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hB : Continuous (fun u => Bop d s V β ρ f u) := by
      have hfd : ∀ u, ContDiffAt ℝ 2 (Torus.lift f) (Torus.rep u) := fun u =>
        (show ContDiff ℝ 2 (Torus.lift f) from hf).contDiffAt
      have e : (fun u => Bop d s V β ρ f u) = fun u =>
          β⁻¹ * ∑ i, Torus.partialDeriv i (fun u => Torus.partialDeriv i f u) u +
          β⁻¹ * ∑ j, (Torus.partialDeriv j ρ u / ρ u) * Torus.partialDeriv j f u :=
        funext fun u => px4b_Bop_eq H (hfd u)
      rw [e]
      refine (continuous_const.mul (continuous_finset_sum _ fun i _ =>
        PDE.continuous_partialDeriv i _ (hpd i))).add (continuous_const.mul
          (continuous_finset_sum _ fun j _ => ?_))
      exact ((PDE.continuous_partialDeriv j ρ hρ1).div hρc (fun u => (hρ.pos u).ne')).mul (hpdc j)
    have hJ : Continuous (fun u => Jop d s ρ f u) := by
      have hg := PDE.MFOneLe.integrable_periodicRiesz hd1 s H.s_nonneg H.s_lt
      have hH : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j f y) :=
        fun j => MFAux.isCk_mul_partialDeriv ρ f hρ1 hf j
      have e : (fun u => Jop d s ρ f u) = convFun (periodicRiesz d s) (fun y => ∑ j,
          Torus.partialDeriv j (fun y' => ρ y' * Torus.partialDeriv j f y') y) :=
        funext fun u => pxS_Jop_eq hd1 H.s_nonneg H.s_lt hρ1 hf u
      rw [e]
      refine MFAux.continuous_convFun hg (continuous_finset_sum _ fun j _ => ?_)
      exact PDE.continuous_partialDeriv j _ (hH j)
    exact ⟨hB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
      hJ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)⟩

end HRS.Parx
end
