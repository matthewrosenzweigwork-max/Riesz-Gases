import HRS.Whole.Basic
import HRS.Prob.MartingaleLindeberg

/-!
# Packet STEIN, auxiliary file 1: mollification in `ℝⁿ`

`HRS.Whole.Stein.mol ψ g = ψ ⋆ g` for a compactly supported smooth bump `ψ = φ.normed volume`:
smoothness and bounded derivatives (for bounded continuous `g`), exact derivative bounds for `g ∈ C^N`
with bounded derivatives, and pointwise convergence as the radius tends to `0`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.Whole.Stein

variable {n : ℕ}

/-- The mollification `ψ ⋆ g`, `x ↦ ∫ ψ(p) g(x - p) dp`. -/
def mol (ψ g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ p, ψ p * g (x - p)

lemma mol_eq (ψ g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    mol ψ g x = ∫ y, ψ (x - y) * g y := by
  unfold mol
  have := integral_sub_left_eq_self (fun y => ψ (x - y) * g y)
    (volume : Measure (EuclideanSpace ℝ (Fin n))) x
  simp only [sub_sub_cancel] at this
  exact this

lemma bump_deriv_bdd (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    ∃ K, ∀ z, ‖iteratedFDeriv ℝ j (φ.normed volume) z‖ ≤ K :=
  Continuous.bounded_above_of_compact_support
    ((φ.contDiff_normed (n := (j : ℕ∞))).continuous_iteratedFDeriv (m := j) le_rfl)
    (φ.hasCompactSupport_normed.iteratedFDeriv j)

lemma mol_smooth_core (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) (hr : 0 < r)
    (hψcd : ∀ m : ℕ, ContDiff ℝ (m : WithTop ℕ∞) ψ) (hsupp : ∀ z, r ≤ ‖z‖ → ψ z = 0)
    (K : ℕ → ℝ) (hK : ∀ j z, ‖iteratedFDeriv ℝ j ψ z‖ ≤ K j)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) (N : ℕ) :
    ContDiff ℝ N (mol ψ g) ∧
      ∀ j ≤ N, ∃ K', ∀ x, ‖iteratedFDeriv ℝ j (mol ψ g) x‖ ≤ K' := by
  have hψc : Continuous ψ := by simpa using (hψcd 0).continuous
  have key : ∀ x0 : EuclideanSpace ℝ (Fin n), ContDiffAt ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (mol ψ g) x0 ∧
      ∀ j ≤ N + 1, ‖iteratedFDeriv ℝ j (mol ψ g) x0‖ ≤
        |M| * |K j| * (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * r))).toReal := by
    intro x0
    obtain ⟨s, hs⟩ : ∃ s : Set (EuclideanSpace ℝ (Fin n)), s = closedBall x0 (2 * r) := ⟨_, rfl⟩
    obtain ⟨ν, hν⟩ : ∃ ν : Measure (EuclideanSpace ℝ (Fin n)), ν = volume.restrict s := ⟨_, rfl⟩
    have hsc : IsCompact s := hs ▸ isCompact_closedBall _ _
    have hfin : IsFiniteMeasure ν :=
      ⟨by rw [hν, Measure.restrict_apply_univ]; rw [hs]; exact measure_closedBall_lt_top⟩
    obtain ⟨Gp, hGp⟩ : ∃ Gp : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ,
        ∀ p x, Gp p x = ψ (x - p) * g p := ⟨fun p x => ψ (x - p) * g p, fun _ _ => rfl⟩
    have hcd : ∀ p, ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (Gp p) := by
      intro p
      have : Gp p = fun x => ψ (x - p) * g p := funext (hGp p)
      rw [this]
      exact ((hψcd (N + 1)).comp (contDiff_id.sub contDiff_const)).mul contDiff_const
    have hit : ∀ j x p, iteratedFDeriv ℝ j (Gp p) x = g p • iteratedFDeriv ℝ j ψ (x - p) := by
      intro j x p
      have h1 : Gp p = fun x => g p • ψ (x - p) := by
        funext x; rw [hGp, smul_eq_mul]; ring
      have hcdat : ContDiffAt ℝ (j : WithTop ℕ∞) (fun x => ψ (x - p)) x :=
        ((hψcd j).comp (contDiff_id.sub contDiff_const)).contDiffAt
      rw [h1, iteratedFDeriv_const_smul_apply' (f := fun x => ψ (x - p)) hcdat,
        iteratedFDeriv_comp_sub]
    have hGpc : Continuous (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Gp q.1 q.2) := by
      have : (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => Gp q.1 q.2) =
          fun q => ψ (q.2 - q.1) * g q.1 := funext fun q => hGp _ _
      rw [this]
      exact (hψc.comp (continuous_snd.sub continuous_fst)).mul (hg.comp continuous_fst)
    have hint : ∀ x, Integrable (fun p => Gp p x) ν := by
      intro x
      have hc : Continuous (fun p => Gp p x) := hGpc.comp (continuous_id.prodMk continuous_const)
      rw [hν]
      exact hc.continuousOn.integrableOn_compact hsc
    have hmeas : ∀ j ≤ N + 1, ∀ x,
        AEStronglyMeasurable (fun p => iteratedFDeriv ℝ j (Gp p) x) ν := by
      intro j hj x
      have : (fun p => iteratedFDeriv ℝ j (Gp p) x) =
          fun p => g p • iteratedFDeriv ℝ j ψ (x - p) := by
        funext p; exact hit j x p
      rw [this]
      refine Continuous.aestronglyMeasurable ?_
      refine hg.smul ?_
      exact ((hψcd j).continuous_iteratedFDeriv le_rfl).comp (continuous_const.sub continuous_id)
    have hbd : ∀ j, ∀ p x,
        ‖iteratedFDeriv ℝ j (Gp p) x‖ ≤ |M| * |K j| := by
      intro j p x
      rw [hit, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul ((hM p).trans (le_abs_self M)) ((hK j _).trans (le_abs_self _))
        (norm_nonneg _) (abs_nonneg _)
    obtain ⟨hC, hE⟩ := HRS.contDiff_integral_dominated ν Gp (N + 1) (by omega) hcd hint hmeas
      (fun j => fun _ => (|M| * |K j|)) (fun j _ _ => integrable_const _) (fun j _ _ => hbd j)
    have hloc : mol ψ g =ᶠ[𝓝 x0] fun x => ∫ p, Gp p x ∂ν := by
      have hmem : ball x0 r ∈ 𝓝 x0 := ball_mem_nhds _ hr
      filter_upwards [hmem] with x hx
      rw [mol_eq, hν]
      simp only [hGp]
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro y hy
      have hy' : 2 * r < dist y x0 := by simpa [hs, mem_closedBall, not_le] using hy
      have hx' : dist x x0 < r := hx
      have : ψ (x - y) = 0 := by
        apply hsupp
        have h2 : dist y x0 ≤ dist y x + dist x x0 := dist_triangle _ _ _
        have h3 : dist y x = ‖x - y‖ := by rw [dist_comm, dist_eq_norm]
        linarith
      rw [this, zero_mul]
    have hCat : ContDiffAt ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (mol ψ g) x0 :=
      (hC.contDiffAt).congr_of_eventuallyEq hloc
    refine ⟨hCat, fun j hj => ?_⟩
    have hEq : iteratedFDeriv ℝ j (mol ψ g) x0 =
        iteratedFDeriv ℝ j (fun x => ∫ p, Gp p x ∂ν) x0 :=
      (hloc.iteratedFDeriv ℝ j).self_of_nhds
    rw [hEq, hE j hj x0]
    calc ‖∫ p, iteratedFDeriv ℝ j (Gp p) x0 ∂ν‖ ≤ ∫ _p, |M| * |K j| ∂ν := by
          refine norm_integral_le_of_norm_le (integrable_const _) (Eventually.of_forall fun p => ?_)
          exact hbd j p x0
      _ = _ := by
          rw [integral_const, hν, smul_eq_mul]
          simp only [Measure.real, Measure.restrict_apply_univ, hs]
          rw [Measure.addHaar_closedBall_center]
          ring
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ((key x).1.of_le ?_), fun j hj => ?_⟩
  · exact_mod_cast Nat.le_succ N
  · exact ⟨_, fun x => (key x).2 j (by omega)⟩

lemma mol_smooth (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) (N : ℕ) :
    ContDiff ℝ N (mol (φ.normed volume) g) ∧
      ∀ j ≤ N, ∃ K, ∀ x, ‖iteratedFDeriv ℝ j (mol (φ.normed volume) g) x‖ ≤ K := by
  choose K hK using fun j => bump_deriv_bdd φ j
  refine mol_smooth_core (φ.normed volume) φ.rOut φ.rOut_pos
    (fun m => φ.contDiff_normed (n := (m : ℕ∞))) ?_ K hK g hg M hM N
  intro z hz
  by_contra hne
  have hsup : z ∈ Function.support (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n)))) := hne
  rw [φ.support_normed_eq] at hsup
  have h1 : dist z 0 < φ.rOut := hsup
  rw [dist_zero_right] at h1
  linarith

/-- Exact derivative formulas and bounds for the mollification of a `C^N` function with bounded
derivatives. -/
lemma mol_deriv (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (N : ℕ) (hN : 1 ≤ N) (hg : ContDiff ℝ N g)
    (M : ℝ) (hM : ∀ y, |g y| ≤ M) (D : ℕ → ℝ)
    (hD : ∀ j, 1 ≤ j → j ≤ N → ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ D j) :
    ContDiff ℝ N (mol (φ.normed volume) g) ∧
      (∀ j ≤ N, ∀ x, iteratedFDeriv ℝ j (mol (φ.normed volume) g) x =
        ∫ p, (φ.normed volume p) • iteratedFDeriv ℝ j g (x - p)) ∧
      (∀ j, 1 ≤ j → j ≤ N → ∀ x, ‖iteratedFDeriv ℝ j (mol (φ.normed volume) g) x‖ ≤ D j) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ψ = φ.normed volume := ⟨_, rfl⟩
  rw [← hψ]
  have hψc : Continuous ψ := hψ ▸ φ.continuous_normed
  have hψi : Integrable ψ volume := hψ ▸ φ.integrable_normed
  have hψ0 : ∀ z, 0 ≤ ψ z := fun z => hψ ▸ φ.nonneg_normed z
  have hψ1 : ∫ z, ψ z = 1 := hψ ▸ φ.integral_normed
  have hgc : Continuous g := hg.continuous
  obtain ⟨Gp, hGp⟩ : ∃ Gp : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ,
      ∀ p x, Gp p x = ψ p * g (x - p) := ⟨fun p x => ψ p * g (x - p), fun _ _ => rfl⟩
  have hcd : ∀ p, ContDiff ℝ (N : WithTop ℕ∞) (Gp p) := by
    intro p
    have : Gp p = fun x => ψ p * g (x - p) := funext (hGp p)
    rw [this]
    exact contDiff_const.mul (hg.comp (contDiff_id.sub contDiff_const))
  have hit : ∀ j, j ≤ N → ∀ x p, iteratedFDeriv ℝ j (Gp p) x =
      ψ p • iteratedFDeriv ℝ j g (x - p) := by
    intro j hj x p
    have h1 : Gp p = fun x => ψ p • g (x - p) := by
      funext x; rw [hGp, smul_eq_mul]
    have hcdat : ContDiffAt ℝ (j : WithTop ℕ∞) (fun x => g (x - p)) x :=
      ((hg.of_le (by exact_mod_cast hj)).comp (contDiff_id.sub contDiff_const)).contDiffAt
    rw [h1, iteratedFDeriv_const_smul_apply' (f := fun x => g (x - p)) hcdat,
      iteratedFDeriv_comp_sub]
  have hGpc : Continuous (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      Gp q.1 q.2) := by
    have : (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => Gp q.1 q.2) =
        fun q => ψ q.1 * g (q.2 - q.1) := funext fun q => hGp _ _
    rw [this]
    exact (hψc.comp continuous_fst).mul (hgc.comp (continuous_snd.sub continuous_fst))
  have hint : ∀ x, Integrable (fun p => Gp p x) volume := by
    intro x
    have : (fun p => Gp p x) = fun p => ψ p * g (x - p) := funext fun p => hGp p x
    rw [this]
    refine hψi.mul_bdd (hgc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa using hM (x - p))
  have hmeas : ∀ j ≤ N, ∀ x,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ j (Gp p) x) volume := by
    intro j hj x
    have : (fun p => iteratedFDeriv ℝ j (Gp p) x) =
        fun p => ψ p • iteratedFDeriv ℝ j g (x - p) := by
      funext p; exact hit j hj x p
    rw [this]
    refine Continuous.aestronglyMeasurable ?_
    refine hψc.smul ?_
    exact ((hg.continuous_iteratedFDeriv (by exact_mod_cast hj))).comp
      (continuous_const.sub continuous_id)
  have hbd : ∀ j, 1 ≤ j → j ≤ N → ∀ p x,
      ‖iteratedFDeriv ℝ j (Gp p) x‖ ≤ ψ p * D j := by
    intro j h1 hj p x
    rw [hit j hj, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψ0 p)]
    exact mul_le_mul_of_nonneg_left (hD j h1 hj _) (hψ0 p)
  obtain ⟨hC, hE⟩ := HRS.contDiff_integral_dominated volume Gp N hN hcd hint hmeas
    (fun j p => ψ p * D j) (fun j _ _ => hψi.mul_const _) hbd
  have hmol : mol ψ g = fun x => ∫ p, Gp p x := by
    funext x; simp only [mol, hGp]
  rw [hmol]
  refine ⟨hC, fun j hj x => ?_, fun j h1 hj x => ?_⟩
  · rw [hE j hj x]
    congr 1; funext p; exact hit j hj x p
  · rw [hE j hj x]
    calc ‖∫ p, iteratedFDeriv ℝ j (Gp p) x‖ ≤ ∫ p, ψ p * D j := by
          refine norm_integral_le_of_norm_le (hψi.mul_const _) (Eventually.of_forall fun p => ?_)
          exact hbd j h1 hj p x
      _ = D j := by rw [integral_mul_const, hψ1, one_mul]

/-- The derivative of a mollification, evaluated on a vector. -/
lemma mol_fderiv_apply (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 1 g)
    (M : ℝ) (hM : ∀ y, |g y| ≤ M) (D : ℝ) (hD : ∀ x, ‖fderiv ℝ g x‖ ≤ D)
    (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (mol (φ.normed volume) g) x v =
      ∫ p, φ.normed volume p * fderiv ℝ g (x - p) v := by
  have hDi : ∀ j, 1 ≤ j → j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ D := by
    intro j h1 hj x
    have : j = 1 := le_antisymm hj h1
    subst this
    rw [norm_iteratedFDeriv_one]  -- ‖iteratedFDeriv 1 g x‖ = ‖fderiv g x‖
    exact hD x
  obtain ⟨_, hform, _⟩ := mol_deriv φ g 1 le_rfl hg M hM (fun _ => D) hDi
  have h1 := hform 1 le_rfl x
  have h2 := congrArg (fun L => L ![v]) h1
  simp only [iteratedFDeriv_one_apply] at h2
  have hψi : Integrable (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n)))) volume :=
    φ.integrable_normed
  have hψ0 : ∀ z, 0 ≤ φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n))) z :=
    φ.nonneg_normed
  have hint : Integrable (fun p => (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n))) p) •
      iteratedFDeriv ℝ 1 g (x - p)) volume := by
    refine (hψi.mul_const D).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (φ.continuous_normed.smul ((hg.continuous_iteratedFDeriv (by norm_num)).comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hψ0 p)]
      exact mul_le_mul_of_nonneg_left (hDi 1 le_rfl le_rfl _) (hψ0 p)
  rw [ContinuousMultilinearMap.integral_apply hint] at h2
  simp only [Matrix.cons_val_zero] at h2
  rw [h2]
  congr 1; funext p
  simp [iteratedFDeriv_one_apply]

/-- Pointwise convergence of mollifications of a continuous function. -/
lemma mol_tendsto (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hc : Continuous h) (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => mol ((φ k).normed volume) h x) atTop (𝓝 (h x)) := by
  have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (φ := φ) (l := atTop) (g := h) hφ hc x
  refine this.congr fun k => ?_
  simp [mol, convolution_def]

/-- A sequence of bumps with radii tending to `0`. -/
def bumpSeq (n : ℕ) (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) where
  rIn := 1 / ((k : ℝ) + 2)
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt <;> [positivity; linarith]

lemma bumpSeq_rOut_tendsto (n : ℕ) :
    Tendsto (fun k => (bumpSeq n k).rOut) atTop (𝓝 0) := by
  simp only [bumpSeq]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma mol_abs_le (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) (hM : ∀ y, |g y| ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) : |mol (φ.normed volume) g x| ≤ M := by
  have hψi : Integrable (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n)))) volume :=
    φ.integrable_normed
  have hψ0 : ∀ z, 0 ≤ φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n))) z :=
    φ.nonneg_normed
  have hψ1 : ∫ z, φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n))) z = 1 := φ.integral_normed
  rw [← Real.norm_eq_abs]
  unfold mol
  calc ‖∫ p, φ.normed volume p * g (x - p)‖ ≤ ∫ p, φ.normed volume p * M := by
        refine norm_integral_le_of_norm_le (hψi.mul_const _) (Eventually.of_forall fun p => ?_)
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hψ0 p), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM _) (hψ0 p)
    _ = M := by rw [integral_mul_const, hψ1, one_mul]

end HRS.Whole.Stein
