import HRS.MS.PoisInvAux1

/-!
# GAP-1 (part 1): the abstract reference structure `GapRef`, integration by parts, invariance, Dirichlet identity

Supplement foundation packet GAP-1 (`docs/S4_PLAN.md`, brief GAP-1; rows S4.9 and S4.4).  Namespace `HRS.MS.Gap`,
helper prefix `gap1_`.

`GapRef d ρ q B` is the abstract setting of the packet: `ρ` is a positive `C^∞` probability density on `ℝ^d`
with finite second moment, `∇ρ = ρ (-q x + B)`, and `B ∈ C_b^m` for every `m` (with a bound `Mb m`).  The
generator is `kolmL q B h = Δh + ⟨-q x + B, ∇h⟩` (`HRS.MS.PoisKolm.kolmL`, definitionally the operator
`Δ + b·∇` of `IsInvariantMeasure`).

Main theorems of this file (all generic in `(ρ, q, B)`).
* `gap_moment`: the second moment `∫ ‖x‖² dμ` is finite (`μ = withDensityReal ρ`), and `μ` is a probability measure.
* `gap_invariant`: `IsInvariantMeasure (fun x => -q • x + B x) (HRS.Whole.withDensityReal ρ)`.
* `gap_dirichlet`: for `φ ∈ C²` with bounded `Dφ, D²φ` and `ψ ∈ C¹` bounded with bounded `Dψ`:
  `∫ (Δφ + b·∇φ) ψ dμ = -∫ ⟨∇φ, ∇ψ⟩ dμ`, both integrands integrable (cutoff `φ(x/R)`, second moment).
* `gap_of_logDensity`, `gap_of_tilt`: criteria producing `GapRef` from `ρ = exp(-(q/2)‖x‖² + G)` with `G ∈ C^∞`
  having bounded derivatives of every positive order (`B = ∇G`), respectively from the tilt `(1+εψ) ρ`.

Statement adjustments relative to the plan sketch: the integrals are against `withDensityReal ρ`; the generator is the
explicit `kolmL q B`; second-derivative bounds are on `fderiv ℝ (fderiv ℝ φ)` (as in `PoisInv`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisInv

noncomputable section

namespace HRS.MS.Gap

variable {d : ℕ}

/-- The abstract reference data of GAP-1: `ρ > 0` is a `C^∞` probability density with finite second moment,
`∇ρ = ρ (-q x + B)` and `B ∈ C_b^m` for all `m`. -/
structure GapRef (d : ℕ) (ρ : Euc d → ℝ) (q : ℝ) (B : Euc d → Euc d) : Prop where
  pos : ∀ x, 0 < ρ x
  smooth : ContDiff ℝ ∞ ρ
  integrable : Integrable ρ
  integral_one : ∫ x, ρ x = 1
  moment2 : Integrable (fun x => ‖x‖ ^ 2 * ρ x)
  grad : ∀ x, gradient ρ x = ρ x • (-q • x + B x)
  cb : ∀ m : ℕ, ∃ Mb : ℝ, HasCbBound m Mb B

/-! ### Elementary facts -/

lemma gap1_sum_inner (u w : Euc d) :
    ∑ i : Fin d, inner ℝ (EuclideanSpace.single i (1 : ℝ)) u *
      inner ℝ (EuclideanSpace.single i (1 : ℝ)) w = inner ℝ u w := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner u w
  simpa [EuclideanSpace.basisFun_apply, real_inner_comm] using this

lemma gap1_integral_wdr {ρ : Euc d → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : Euc d → ℝ) :
    ∫ y, f y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * f y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ).aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 y)]

lemma gap1_integrable_wdr {ρ f : Euc d → ℝ} (hρ : Measurable ρ) (hn : ∀ x, 0 ≤ ρ x)
    (h : Integrable (fun x => ρ x * f x)) : Integrable f (HRS.Whole.withDensityReal ρ) := by
  unfold HRS.Whole.withDensityReal
  have hm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ
  rw [integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hn x)]

lemma gap1_integrable_of_zero {F : Euc d → ℝ} (hF : Continuous F) {K : Set (Euc d)} (hK : IsCompact K)
    (h0 : ∀ x ∉ K, F x = 0) : Integrable F :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h0)

lemma gap1_fderiv_rho {ρ : Euc d → ℝ} {b : Euc d → Euc d} (h : ∀ x, gradient ρ x = ρ x • b x)
    (x v : Euc d) : fderiv ℝ ρ x v = ρ x * inner ℝ v (b x) := by
  rw [← kl_inner_gradient, h, inner_smul_right]

lemma gap1_cut_zero {φ : Euc d → ℝ} {x : Euc d} (hx : x ∉ tsupport φ) :
    fderiv ℝ φ x = 0 ∧ fderiv ℝ (fderiv ℝ φ) x = 0 := by
  refine ⟨fderiv_of_notMem_tsupport ℝ hx, ?_⟩
  exact fderiv_of_notMem_tsupport ℝ (fun h => hx (tsupport_fderiv_subset ℝ h))

lemma gap1_grad_zero {φ : Euc d → ℝ} {x : Euc d} (hx : x ∉ tsupport φ) : gradient φ x = 0 := by
  unfold gradient
  rw [(gap1_cut_zero hx).1, map_zero]

lemma gap1_kolmL_zero (q : ℝ) (B : Euc d → Euc d) {φ : Euc d → ℝ} {x : Euc d} (hx : x ∉ tsupport φ) :
    kolmL q B φ x = 0 := by
  rw [kl_L_eq, (gap1_cut_zero hx).2, (gap1_cut_zero hx).1]
  simp

/-! ### Integration by parts for compactly supported test functions -/

theorem gap1_ibp {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) {φ ψ : Euc d → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hψ : ContDiff ℝ 1 ψ) :
    ∫ x, kolmL q B φ x * ψ x * ρ x = -∫ x, inner ℝ (gradient φ x) (gradient ψ x) * ρ x := by
  have hB : Continuous B := by
    obtain ⟨Mb, hMb⟩ := hR.cb 0
    exact hMb.1.continuous
  have hρ1 : ContDiff ℝ 1 ρ := hR.smooth.of_le (by exact_mod_cast le_top)
  set g : Euc d → ℝ := fun x => ψ x * ρ x with hg
  have hg1 : ContDiff ℝ 1 g := hψ.mul hρ1
  have hgc : Continuous g := hg1.continuous
  have hg1' : Continuous (fderiv ℝ g) := hg1.continuous_fderiv one_ne_zero
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hφ1c : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hφ2c : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  set e : Fin d → Euc d := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have key : ∀ i : Fin d,
      Integrable (fun x => fderiv ℝ φ x (e i) * fderiv ℝ g x (e i)) ∧
      Integrable (fun x => fderiv ℝ (fderiv ℝ φ) x (e i) (e i) * g x) ∧
      ∫ x, fderiv ℝ φ x (e i) * fderiv ℝ g x (e i) =
        -∫ x, fderiv ℝ (fderiv ℝ φ) x (e i) (e i) * g x := by
    intro i
    obtain ⟨hfe, hfec⟩ := inv_fe hφ hc (e i)
    have hf' : Continuous (fun x => fderiv ℝ (fun a => fderiv ℝ φ a (e i)) x (e i)) :=
      (hfe.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hf'c : HasCompactSupport (fun x => fderiv ℝ (fun a => fderiv ℝ φ a (e i)) x (e i)) :=
      (hfec.fderiv ℝ).comp_left (g := fun T : Euc d →L[ℝ] ℝ => T (e i)) (by simp)
    have h1 : Integrable (fun x => fderiv ℝ (fun a => fderiv ℝ φ a (e i)) x (e i) * g x) :=
      (hf'.mul hgc).integrable_of_hasCompactSupport hf'c.mul_right
    have h2 : Integrable (fun x => fderiv ℝ φ x (e i) * fderiv ℝ g x (e i)) :=
      ((hφ1c.clm_apply continuous_const).mul (hg1'.clm_apply continuous_const)).integrable_of_hasCompactSupport
        hfec.mul_right
    have h3 : Integrable (fun x => fderiv ℝ φ x (e i) * g x) :=
      ((hφ1c.clm_apply continuous_const).mul hgc).integrable_of_hasCompactSupport hfec.mul_right
    have hI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun a => fderiv ℝ φ a (e i)) (g := g) (v := e i) h1 h2 h3
      (fun x _ => (hfe.differentiable one_ne_zero) x) (fun x _ => (hg1.differentiable one_ne_zero) x)
    have hrw : ∀ x, fderiv ℝ (fun a => fderiv ℝ φ a (e i)) x (e i) = fderiv ℝ (fderiv ℝ φ) x (e i) (e i) := by
      intro x
      rw [← inv_fderiv2 ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)]
    simp_rw [hrw] at hI h1
    exact ⟨h2, h1, hI⟩
  have hgrad : ∀ {f : Euc d → ℝ}, ContDiff ℝ 1 f → Continuous (gradient f) := fun {f} hf => by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hlap : Continuous (Laplacian.laplacian φ) := by
    have e : Laplacian.laplacian φ = fun y => ∑ i : Fin d, fderiv ℝ (fderiv ℝ φ) y (e i) (e i) :=
      funext (kl_laplacian_eq φ)
    rw [e]
    exact continuous_finsetSum _ fun i _ => (hφ2c.clm_apply continuous_const).clm_apply continuous_const
  have hρc : Continuous ρ := hR.smooth.continuous
  have hψc : Continuous ψ := hψ.continuous
  have hbc : Continuous (fun x => -q • x + B x) := (continuous_id.const_smul (-q)).add hB
  have hK : IsCompact (tsupport φ) := hc
  -- the three integrable pieces
  have I1 : Integrable (fun x => Laplacian.laplacian φ x * g x) :=
    gap1_integrable_of_zero (hlap.mul hgc) hK fun x hx => by
      have := (gap1_cut_zero hx).2
      rw [kl_laplacian_eq, this]; simp
  have I2 : Integrable (fun x => ψ x * ρ x * inner ℝ (-q • x + B x) (gradient φ x)) :=
    gap1_integrable_of_zero ((hψc.mul hρc).mul (hbc.inner (hgrad hφ1))) hK fun x hx => by
      rw [gap1_grad_zero hx]; simp
  have I3 : Integrable (fun x => ρ x * inner ℝ (gradient φ x) (gradient ψ x)) :=
    gap1_integrable_of_zero (hρc.mul ((hgrad hφ1).inner (hgrad hψ))) hK fun x hx => by
      rw [gap1_grad_zero hx]; simp
  have hb : ∀ x, ∑ i, fderiv ℝ φ x (e i) * fderiv ℝ g x (e i) =
      ρ x * inner ℝ (gradient φ x) (gradient ψ x) +
        ψ x * ρ x * inner ℝ (-q • x + B x) (gradient φ x) := by
    intro x
    have hfd : ∀ v, fderiv ℝ g x v = ρ x * fderiv ℝ ψ x v + ψ x * (ρ x * inner ℝ v (-q • x + B x)) := by
      intro v
      rw [hg, fderiv_fun_mul (hψ.differentiable one_ne_zero x) (hρ1.differentiable one_ne_zero x)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [gap1_fderiv_rho hR.grad x v]
      ring
    have h1 : ∀ i, fderiv ℝ φ x (e i) * fderiv ℝ g x (e i) =
        ρ x * (inner ℝ (e i) (gradient φ x) * inner ℝ (e i) (gradient ψ x)) +
          ψ x * ρ x * (inner ℝ (e i) (gradient φ x) * inner ℝ (e i) (-q • x + B x)) := by
      intro i
      rw [hfd, ← kl_inner_gradient φ x (e i), ← kl_inner_gradient ψ x (e i)]
      ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h2 := gap1_sum_inner (gradient φ x) (gradient ψ x)
    have h3 := gap1_sum_inner (gradient φ x) (-q • x + B x)
    simp only [he] at *
    rw [h2, h3, real_inner_comm (gradient φ x)]
  have hl : ∀ x, ∑ i, fderiv ℝ (fderiv ℝ φ) x (e i) (e i) * g x = Laplacian.laplacian φ x * g x := by
    intro x
    rw [← Finset.sum_mul, kl_laplacian_eq]
  have hmain : ∫ x, (ρ x * inner ℝ (gradient φ x) (gradient ψ x) +
        ψ x * ρ x * inner ℝ (-q • x + B x) (gradient φ x)) =
      -∫ x, Laplacian.laplacian φ x * g x := by
    have e1 : ∫ x, (ρ x * inner ℝ (gradient φ x) (gradient ψ x) +
        ψ x * ρ x * inner ℝ (-q • x + B x) (gradient φ x)) =
        ∫ x, ∑ i, fderiv ℝ φ x (e i) * fderiv ℝ g x (e i) := by
      refine integral_congr_ae (Eventually.of_forall fun x => (hb x).symm)
    have e2 : ∫ x, Laplacian.laplacian φ x * g x =
        ∫ x, ∑ i, fderiv ℝ (fderiv ℝ φ) x (e i) (e i) * g x :=
      integral_congr_ae (Eventually.of_forall fun x => (hl x).symm)
    rw [e1, e2, integral_finset_sum _ fun i _ => (key i).1, integral_finset_sum _ fun i _ => (key i).2.1,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => (key i).2.2
  have hsplit := integral_add (I3) (I2)
  have hkl : ∀ x, kolmL q B φ x * ψ x * ρ x =
      Laplacian.laplacian φ x * g x + ψ x * ρ x * inner ℝ (-q • x + B x) (gradient φ x) := by
    intro x; unfold kolmL; rw [hg]; ring
  have hkl' : ∀ x, inner ℝ (gradient φ x) (gradient ψ x) * ρ x =
      ρ x * inner ℝ (gradient φ x) (gradient ψ x) := fun x => mul_comm _ _
  simp_rw [hkl, hkl']
  rw [integral_add I1 I2]
  linarith

/-! ### Second moment, invariance, Dirichlet identity -/

lemma gap1_integrable_lin {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) :
    Integrable (fun x : Euc d => (1 + ‖x‖) * ρ x) := by
  have hb : Integrable (fun x : Euc d => 2 * ρ x + ‖x‖ ^ 2 * ρ x) :=
    (hR.integrable.const_mul 2).add hR.moment2
  refine hb.mono' ((continuous_const.add continuous_norm).mul hR.smooth.continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have h0 := (hR.pos x).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

lemma gap1_isProb {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := by
  refine ⟨?_⟩
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hR.integrable (Eventually.of_forall fun x => (hR.pos x).le),
    hR.integral_one]
  simp

/-- **Second moment** (`gap_moment`): for `GapRef d ρ q B`, `μ = ρ dx` is a probability measure with finite second
moment `m₂ = ∫ ‖x‖² dμ = ∫ ‖x‖² ρ dx`. -/
theorem gap_moment {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) ∧
      Integrable (fun x : Euc d => ‖x‖ ^ 2) (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, ‖x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) = ∫ x, ‖x‖ ^ 2 * ρ x := by
  have hm : Measurable ρ := hR.smooth.continuous.measurable
  refine ⟨gap1_isProb hR, ?_, ?_⟩
  · refine gap1_integrable_wdr hm (fun x => (hR.pos x).le) ?_
    simpa [mul_comm] using hR.moment2
  · rw [gap1_integral_wdr hm (fun x => (hR.pos x).le)]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- **Invariance** (`gap_invariant`): `ρ dx` is an invariant probability measure of `Δ + b·∇`,
`b = -q x + B`. -/
theorem gap_invariant {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) :
    IsInvariantMeasure (fun x => -q • x + B x) (HRS.Whole.withDensityReal ρ) := by
  refine ⟨gap1_isProb hR, fun φ hφ hc => ?_⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have h := gap1_ibp hR hφ2 hc (ψ := fun _ => (1 : ℝ)) contDiff_const
  have hg : ∀ x : Euc d, gradient (fun _ : Euc d => (1 : ℝ)) x = 0 := fun x => by simp [gradient]
  simp only [hg, inner_zero_right, zero_mul, integral_zero, neg_zero, mul_one] at h
  rw [gap1_integral_wdr hR.smooth.continuous.measurable (fun x => (hR.pos x).le)]
  have : ∀ x, ρ x * (Laplacian.laplacian φ x + inner ℝ (-q • x + B x) (gradient φ x)) =
      kolmL q B φ x * ρ x := fun x => by unfold kolmL; ring
  simp_rw [this]
  exact h

lemma gap1_norm_grad (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

lemma gap1_grad_continuous {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

/-- **Dirichlet identity** (`gap_dirichlet`): for `φ ∈ C²` with bounded `Dφ, D²φ` (`φ` itself may grow linearly) and
`ψ ∈ C¹` bounded with bounded `Dψ`, `∫ (Δφ + b·∇φ) ψ dμ = -∫ ⟨∇φ, ∇ψ⟩ dμ` with `μ = ρ dx` and both integrands
`μ`-integrable.  Here `kolmL q B φ = Δφ + ⟨-q x + B, ∇φ⟩`. -/
theorem gap_dirichlet {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) {φ ψ : Euc d → ℝ}
    (hφ : ContDiff ℝ 2 φ) {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ M1)
    (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ M2) (hψ : ContDiff ℝ 1 ψ) {Cψ C1 : ℝ}
    (hψb : ∀ x, |ψ x| ≤ Cψ) (hψ1 : ∀ x, ‖fderiv ℝ ψ x‖ ≤ C1) :
    Integrable (fun x => kolmL q B φ x * ψ x) (HRS.Whole.withDensityReal ρ) ∧
    Integrable (fun x => inner ℝ (gradient φ x) (gradient ψ x)) (HRS.Whole.withDensityReal ρ) ∧
    ∫ x, kolmL q B φ x * ψ x ∂(HRS.Whole.withDensityReal ρ) =
      -∫ x, inner ℝ (gradient φ x) (gradient ψ x) ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨Mb, hMb⟩ := hR.cb 0
  have hBc : Continuous B := hMb.1.continuous
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hMb.2 0 le_rfl y
  have hρc : Continuous ρ := hR.smooth.continuous
  have hψc : Continuous ψ := hψ.continuous
  have hCψ : 0 ≤ Cψ := (abs_nonneg _).trans (hψb 0)
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (hψ1 0)
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans (hBb 0)
  have hdom := gap1_integrable_lin hR
  obtain ⟨M1', M2', hbnd⟩ := inv_cut_bounds hφ hM1 hM2
  set A : ℝ := ((d * M2' + M1' * Mb) + M1' * |q|) with hA
  have hf2 : ∀ n : ℕ, ContDiff ℝ 2 (fun y => invCutR ((n : ℝ) + 1) y * φ y) := fun n =>
    ((inv_cutR_contDiff _).of_le (by norm_num)).mul hφ
  have hfc : ∀ n : ℕ, HasCompactSupport (fun y => invCutR ((n : ℝ) + 1) y * φ y) := fun n =>
    (inv_cutR_compact (by positivity)).mul_right
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hibp : ∀ n : ℕ, ∫ x, kolmL q B (fun y => invCutR ((n : ℝ) + 1) y * φ y) x * ψ x * ρ x =
      -∫ x, inner ℝ (gradient (fun y => invCutR ((n : ℝ) + 1) y * φ y) x) (gradient ψ x) * ρ x :=
    fun n => gap1_ibp hR (hf2 n) (hfc n) hψ
  have hA0 : 0 ≤ A := by
    have h1 := hbnd 1 le_rfl
    have : 0 ≤ M1' := (norm_nonneg _).trans (h1.1 0)
    have : 0 ≤ M2' := (norm_nonneg (fderiv ℝ (fderiv ℝ (fun y => invCutR (1:ℝ) y * φ y)) 0)).trans (h1.2 0)
    positivity
  have hM1'0 : 0 ≤ M1' := (norm_nonneg _).trans ((hbnd 1 le_rfl).1 0)
  -- local equality of the cut-off functions with `φ`
  have hloc : ∀ x : Euc d, ∀ᶠ n : ℕ in atTop,
      (fun y => invCutR ((n : ℝ) + 1) y * φ y) =ᶠ[𝓝 x] φ := fun x => by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hxn : ‖x‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hopen : IsOpen {y : Euc d | ‖y‖ < (n : ℝ) + 1} := isOpen_lt continuous_norm continuous_const
    filter_upwards [hopen.mem_nhds hxn] with y hy
    have hy' : ‖y‖ < (n : ℝ) + 1 := hy
    simp [inv_cutR_one (by positivity : (0 : ℝ) < (n : ℝ) + 1) hy'.le]
  -- left side
  have hL : Tendsto (fun n : ℕ => ∫ x, kolmL q B (fun y => invCutR ((n : ℝ) + 1) y * φ y) x * ψ x * ρ x)
      atTop (𝓝 (∫ x, kolmL q B φ x * ψ x * ρ x)) := by
    refine tendsto_integral_of_dominated_convergence (μ := volume)
      (fun x => A * Cψ * ((1 + ‖x‖) * ρ x)) ?_ (hdom.const_mul _) ?_ ?_
    · exact fun n => (((kl_L_continuous q hBc (hf2 n)).mul hψc).mul hρc).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      have h1 := inv_growth q hBb (hbnd _ (hR1 n)).1 (hbnd _ (hR1 n)).2 x
      have h2 := hψb x
      have h3 := (hR.pos x).le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h3]
      calc |kolmL q B (fun y => invCutR ((n : ℝ) + 1) y * φ y) x| * |ψ x| * ρ x
          ≤ (A * (1 + ‖x‖)) * Cψ * ρ x := by gcongr
        _ = A * Cψ * ((1 + ‖x‖) * ρ x) := by ring
    · refine Eventually.of_forall fun x => ?_
      refine (tendsto_const_nhds (x := kolmL q B φ x * ψ x * ρ x)).congr' ?_
      filter_upwards [hloc x] with n hn
      rw [inv_kolmL_congr q B hn]
  -- right side
  have hRt : Tendsto (fun n : ℕ => ∫ x, inner ℝ (gradient (fun y => invCutR ((n : ℝ) + 1) y * φ y) x)
      (gradient ψ x) * ρ x) atTop (𝓝 (∫ x, inner ℝ (gradient φ x) (gradient ψ x) * ρ x)) := by
    refine tendsto_integral_of_dominated_convergence (μ := volume)
      (fun x => M1' * C1 * ρ x) ?_ (hR.integrable.const_mul _) ?_ ?_
    · exact fun n => (((gap1_grad_continuous ((hf2 n).of_le (by norm_num))).inner
        (gap1_grad_continuous hψ)).mul hρc).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun x => ?_
      have h3 := (hR.pos x).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h3]
      have h4 : |inner ℝ (gradient (fun y => invCutR ((n : ℝ) + 1) y * φ y) x) (gradient ψ x)| ≤
          M1' * C1 := by
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [gap1_norm_grad, gap1_norm_grad]
        exact mul_le_mul ((hbnd _ (hR1 n)).1 x) (hψ1 x) (norm_nonneg _) hM1'0
      exact mul_le_mul_of_nonneg_right h4 h3
    · refine Eventually.of_forall fun x => ?_
      refine (tendsto_const_nhds (x := inner ℝ (gradient φ x) (gradient ψ x) * ρ x)).congr' ?_
      filter_upwards [hloc x] with n hn
      have : gradient (fun y => invCutR ((n : ℝ) + 1) y * φ y) x = gradient φ x := by
        unfold gradient; rw [hn.fderiv_eq]
      rw [this]
  simp_rw [hibp] at hL
  have hlim : ∫ x, kolmL q B φ x * ψ x * ρ x = -∫ x, inner ℝ (gradient φ x) (gradient ψ x) * ρ x :=
    tendsto_nhds_unique hL hRt.neg
  -- integrability of the limits
  have hint1 : Integrable (fun x => ρ x * (kolmL q B φ x * ψ x)) := by
    refine (hdom.const_mul (((d * M2 + M1 * Mb) + M1 * |q|) * Cψ)).mono'
      (hρc.mul ((kl_L_continuous q hBc hφ).mul hψc)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have h1 := inv_growth q hBb hM1 hM2 x
    have h2 := hψb x
    have h3 := (hR.pos x).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h3]
    have hA1 : 0 ≤ ((d * M2 + M1 * Mb) + M1 * |q|) := by
      have : 0 ≤ M2 := (norm_nonneg (fderiv ℝ (fderiv ℝ φ) 0)).trans (hM2 0)
      positivity
    calc ρ x * (|kolmL q B φ x| * |ψ x|)
        ≤ ρ x * ((((d * M2 + M1 * Mb) + M1 * |q|) * (1 + ‖x‖)) * Cψ) := by gcongr
      _ = ((d * M2 + M1 * Mb) + M1 * |q|) * Cψ * ((1 + ‖x‖) * ρ x) := by ring
  have hint2 : Integrable (fun x => ρ x * inner ℝ (gradient φ x) (gradient ψ x)) := by
    refine (hR.integrable.const_mul (M1 * C1)).mono'
      (hρc.mul ((gap1_grad_continuous (hφ.of_le (by norm_num))).inner
        (gap1_grad_continuous hψ))).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have h3 := (hR.pos x).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h3]
    have h4 : |inner ℝ (gradient φ x) (gradient ψ x)| ≤ M1 * C1 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [gap1_norm_grad, gap1_norm_grad]
      exact mul_le_mul (hM1 x) (hψ1 x) (norm_nonneg _) hM10
    calc ρ x * |inner ℝ (gradient φ x) (gradient ψ x)| ≤ ρ x * (M1 * C1) := by gcongr
      _ = M1 * C1 * ρ x := by ring
  have hm : Measurable ρ := hρc.measurable
  have hn : ∀ x, 0 ≤ ρ x := fun x => (hR.pos x).le
  refine ⟨gap1_integrable_wdr hm hn hint1, gap1_integrable_wdr hm hn hint2, ?_⟩
  rw [gap1_integral_wdr hm hn, gap1_integral_wdr hm hn]
  have e1 : ∫ x, ρ x * (kolmL q B φ x * ψ x) = ∫ x, kolmL q B φ x * ψ x * ρ x :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  have e2 : ∫ x, ρ x * inner ℝ (gradient φ x) (gradient ψ x) =
      ∫ x, inner ℝ (gradient φ x) (gradient ψ x) * ρ x :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [e1, e2]
  exact hlim

end HRS.MS.Gap

end
