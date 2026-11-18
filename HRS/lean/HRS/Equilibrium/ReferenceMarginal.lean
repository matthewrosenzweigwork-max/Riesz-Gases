/-
# HRS.Equilibrium.ReferenceMarginal -- first-marginal bounds for the calibrated reference `R_N` (EQ-02, reference half)

Source: main paper `Q:eq:reference-input` (TeX lines 4449-4488) and the reference part of
Proposition 4.2 `M:A:prop:marginal` (TeX 3664-3672 and its proof): for `π_N = R_N^{(1)}`,
`dπ_N/dμ ≤ C`, `‖dπ_N/dμ - 1‖_{L²(μ)} ≤ C δ_N`, `‖dπ_N/dμ - 1‖_∞ → 0`, uniformly over the
densities `ρ ≤ Λ`.

Main results (end of the file): `reference_marginal_density_le`, `reference_marginal_density_L2`,
`reference_marginal_density_uniform`.

Proof (the source's cavity argument).  `π_N = Θ/∫Θ · μ` with `Θ = e^{φ} u`, `u` the pole-insertion
factor of the `(N-1)`-particle cavity ensemble (`marginal_eq_normalized`); `log u = -m + D` with the
compensated correction `D ≤ C δ_N` (truncation + Wu's linear variance bound, `cavD_torus`);
`t_N·Ξ = -β g_L*(π - μ)` (`hh_eq`); cavity versus full marginal `C/N` (`event_pi_nu`, RvH); the
`L²` convolution estimate with the weak-`L^p` kernel (`cv_L2_rate`); absorption by the positive
definiteness of `g` (`absorption`) for `L²`; for the sup-norm, the exact cavity equation with
`‖t_N·Ξ‖_∞ → 0` (`small_field`) and `π⁰_N → μ` in total variation (`tv_R0_mu`).
-/
import HRS.Equilibrium.CalibratedReference
import HRS.Equilibrium.ReferenceSmallness
import HRS.Kernel.Riesz

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.External.RefMarg

open HRS HRS.External HRS.External.Calib HeatSplit

section Ensemble

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {B : Type*} [Fintype B]

/-- **One-coordinate marginal domination**: every one-coordinate marginal of the pinned weak ensemble
is at most `e^{M+M'+βγ} μ`. -/
theorem marginal_le_smul (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) (i : Fin n) :
    (pinnedLaw V (β / N) n a).map (fun y => y i) ≤
      ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) • μ := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam a
  set S := fieldSpec (V := V) hψ hlam n with hS
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.map_apply (measurable_pi_apply i) hA]
  have hmeas : Measurable fun x : Fin n → E => (fun z : Fin n → E => z i) ⁻¹' A |>.indicator
      (fun _ => (1 : ℝ≥0∞)) x := measurable_const.indicator (measurable_pi_apply i hA)
  have h1 := S.invariant i (fun x => ((fun z : Fin n → E => z i) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) x) hmeas
  have e1 : pinnedLaw V (β / N) n a ((fun z : Fin n → E => z i) ⁻¹' A) =
      ∫⁻ x, ((fun z : Fin n → E => z i) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) x ∂S.P := by
    have := lintegral_indicator_one (μ := S.P) (measurable_pi_apply i hA)
    have e : S.P = pinnedLaw V (β / N) n a := rfl
    rw [e] at this ⊢
    rw [← this]
    rfl
  rw [e1, ← h1]
  have hG : ∀ x, ∫⁻ z, ((fun z : Fin n → E => z i) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) (Function.update x i z)
      ∂(S.G i x) = S.G i x A := by
    intro x
    have : (fun z => ((fun z : Fin n → E => z i) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) (Function.update x i z))
        = A.indicator (fun _ => 1) := by
      funext z
      by_cases hz : z ∈ A <;> simp [Set.indicator, hz]
    rw [this]
    have := lintegral_indicator_one (μ := S.G i x) hA
    exact this
  simp_rw [hG]
  have hle : ∀ x, S.G i x A ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) * μ A := by
    intro x
    have := weak_siteKernel_le (B := B) V hβ hN0 hN a i x
    have h2 := this A
    simpa [hS, fieldSpec_G] using h2
  calc ∫⁻ x, S.G i x A ∂S.P ≤ ∫⁻ _x, ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) * μ A ∂S.P :=
        lintegral_mono hle
    _ = _ := by
        rw [lintegral_const, measure_univ, mul_one]
        simp [Measure.smul_apply]


/-- Adding the pin `x` multiplies the unnormalised weight by `exp(-lam ∑_k q(y_k, x))`. -/
lemma fieldWeight_pinsWith (V : WeakPotential μ) (lam : ℝ) (a : B → E) {n : ℕ} (x : E)
    (y : Fin n → E) :
    fieldWeight V (pinField V lam (pinsWith a x)) lam y =
      fieldWeight V (pinField V lam a) lam y *
        ENNReal.ofReal (Real.exp (-(lam * ∑ k, V.q (y k) x))) := by
  unfold fieldWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp_rw [pinField_pinsWith, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h3 : ∑ k, V.q (y k) x = ∑ k, V.q x (y k) := Finset.sum_congr rfl fun k _ => V.q_symm _ _
  ring


/-- The cavity function `u(x) = E_{P⁰_n}[exp(-lam ∑_k q(y_k, x))]` (the pole insertion factor). -/
def cavU (V : WeakPotential μ) (lam : ℝ) (n : ℕ) (a : B → E) (x : E) : ℝ :=
  ∫ y, Real.exp (-(lam * ∑ k, V.q (y k) x)) ∂(pinnedLaw V lam n a)

lemma measurable_pinPole (V : WeakPotential μ) (lam : ℝ) (n : ℕ) :
    Measurable fun p : (Fin n → E) × E => Real.exp (-(lam * ∑ k, V.q (p.1 k) p.2)) := by
  refine Real.measurable_exp.comp (Measurable.neg (Measurable.const_mul
    (Finset.measurable_sum _ fun k _ => ?_) _))
  have := V.measurable_q.comp (((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd :
    Measurable fun p : (Fin n → E) × E => (p.1 k, p.2))
  exact this

omit [IsProbabilityMeasure μ] in
lemma pinPole_le_one (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) {n : ℕ} (y : Fin n → E) (x : E) :
    Real.exp (-(lam * ∑ k, V.q (y k) x)) ≤ 1 := by
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg hlam (Finset.sum_nonneg fun k _ => V.q_nonneg _ _)

lemma lintegral_fieldWeight_pinsWith (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E)
    (n : ℕ) (x : E) :
    fieldNorm V (pinField V lam (pinsWith a x)) lam n =
      fieldNorm V (pinField V lam a) lam n * ENNReal.ofReal (cavU V lam n a x) := by
  have hψ := isField_pinField V hlam a
  haveI := isProb_pinnedLaw V hlam n a
  have hW := measurable_fieldWeight hψ.measurable V lam (n := n)
  have hP : Measurable fun y : Fin n → E => ENNReal.ofReal (Real.exp (-(lam * ∑ k, V.q (y k) x))) :=
    ENNReal.measurable_ofReal.comp ((measurable_pinPole V lam n).comp (measurable_id.prodMk measurable_const))
  have hint : Integrable (fun y : Fin n → E => Real.exp (-(lam * ∑ k, V.q (y k) x)))
      (pinnedLaw V lam n a) := by
    refine Integrable.of_bound (C := 1) ((measurable_pinPole V lam n).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact pinPole_le_one V hlam y x
  have hL : ENNReal.ofReal (cavU V lam n a x) =
      ∫⁻ y, ENNReal.ofReal (Real.exp (-(lam * ∑ k, V.q (y k) x))) ∂(pinnedLaw V lam n a) := by
    unfold cavU
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  rw [hL]
  unfold fieldNorm
  simp_rw [fieldWeight_pinsWith]
  unfold pinnedLaw fieldLaw
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_fieldDensity hψ.measurable V lam n) hP]
  simp only [Pi.mul_apply]
  unfold fieldDensity
  have h1 : fieldNorm V (pinField V lam a) lam n ≠ 0 := (fieldNorm_pos hψ.measurable V lam n).ne'
  have h2 : fieldNorm V (pinField V lam a) lam n ≠ ⊤ := (fieldNorm_lt_top hψ hlam n).ne
  have : ∀ y : Fin n → E, fieldWeight V (pinField V lam a) lam y *
      ENNReal.ofReal (Real.exp (-(lam * ∑ k, V.q (y k) x))) =
      fieldNorm V (pinField V lam a) lam n *
        ((fieldWeight V (pinField V lam a) lam y * (fieldNorm V (pinField V lam a) lam n)⁻¹) *
          ENNReal.ofReal (Real.exp (-(lam * ∑ k, V.q (y k) x)))) := by
    intro y
    calc _ = (fieldNorm V (pinField V lam a) lam n * (fieldNorm V (pinField V lam a) lam n)⁻¹) *
          (fieldWeight V (pinField V lam a) lam y *
            ENNReal.ofReal (Real.exp (-(lam * ∑ k, V.q (y k) x)))) := by
          rw [ENNReal.mul_inv_cancel h1 h2, one_mul]
      _ = _ := by ring
  simp_rw [this]
  rw [lintegral_const_mul' _ _ h2]
  rfl

/-- **One-coordinate marginal of the `(n+1)`-particle ensemble** (cavity formula): its density with respect
to `μ` is `c · e^{ψ(x)} u(x)`, `u = cavU` the pole-insertion factor of the `n`-particle ensemble. -/
theorem marginal_eq_withDensity (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) :
    (pinnedLaw V lam (n + 1) a).map (fun y => y i) =
      μ.withDensity (fun x =>
        (fieldNorm V (pinField V lam a) lam n * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹) *
          (ENNReal.ofReal (Real.exp (pinField V lam a x)) * ENNReal.ofReal (cavU V lam n a x))) := by
  have hψ := isField_pinField V hlam a
  have hψx : ∀ x, IsField μ (pinField V lam (pinsWith a x)) V.M
      (V.M' + lam * Fintype.card (Option B) * V.γ) := fun x => isField_pinField V hlam _
  ext A hA
  have hS : MeasurableSet ((fun y : Fin (n + 1) → E => y i) ⁻¹' A) := measurable_pi_apply _ hA
  rw [Measure.map_apply (measurable_pi_apply _) hA]
  change (fieldLaw V (pinField V lam a) lam (n + 1)) _ = _
  unfold fieldLaw
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hsymm : ∀ (x : E) (y : Fin n → E), e.symm (x, y) = insertAt i x y := fun _ _ => rfl
  set h : (Fin (n + 1) → E) → ℝ≥0∞ := fun y =>
    ((fun y : Fin (n + 1) → E => y i) ⁻¹' A).indicator
      (fieldDensity V (pinField V lam a) lam (n + 1)) y with hh
  have hhm : Measurable h :=
    (measurable_fieldDensity hψ.measurable V lam (n + 1)).indicator hS
  have step1 : ∫⁻ y, h y ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫⁻ p, h (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => h (e.symm p))
    rw [← this]
    exact lintegral_congr fun y => by rw [e.symm_apply_apply]
  rw [step1, lintegral_prod (fun p => h (e.symm p)) (hhm.comp e.symm.measurable).aemeasurable]
  rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  simp only [hsymm]
  have hx : ∀ y : Fin n → E, h (insertAt i x y)
      = A.indicator (fun _ => (ENNReal.ofReal (Real.exp (pinField V lam a x))
            * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹)) x
            * fieldWeight V (pinField V lam (pinsWith a x)) lam y := by
    intro y
    by_cases hm : x ∈ A
    · have h1 : insertAt i x y ∈ (fun y : Fin (n + 1) → E => y i) ⁻¹' A := by
        simp [hm]
      simp only [hh]
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hm]
      unfold fieldDensity
      rw [fieldWeight_insertAt]; ring
    · have h1 : insertAt i x y ∉ (fun y : Fin (n + 1) → E => y i) ⁻¹' A := by
        simp [hm]
      simp only [hh]
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hm]
      simp
  simp_rw [hx]
  have hFW : Measurable (fieldWeight V (pinField V lam (pinsWith a x)) lam (n := n)) :=
    measurable_fieldWeight (hψx x).measurable V lam
  rw [lintegral_const_mul _ hFW]
  have hn : ∫⁻ y, fieldWeight V (pinField V lam (pinsWith a x)) lam y ∂(Measure.pi fun _ : Fin n => μ)
      = fieldNorm V (pinField V lam a) lam n * ENNReal.ofReal (cavU V lam n a x) := by
    rw [← lintegral_fieldWeight_pinsWith V hlam a n x]; rfl
  rw [hn]
  by_cases hm : x ∈ A
  · simp only [Set.indicator_of_mem hm]
    ring
  · simp [Set.indicator_of_notMem hm]

lemma measurable_cavU (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (a : B → E) :
    Measurable (cavU V lam n a) := by
  haveI := isProb_pinnedLaw V hlam n a
  unfold cavU
  exact ((measurable_pinPole V lam n).stronglyMeasurable.integral_prod_left'
    (μ := pinnedLaw V lam n a)).measurable

lemma integrable_pinPole (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) (x : E) :
    Integrable (fun y : Fin n → E => Real.exp (-(lam * ∑ k, V.q (y k) x))) (pinnedLaw V lam n a) := by
  haveI := isProb_pinnedLaw V hlam n a
  refine Integrable.of_bound (C := 1) ((measurable_pinPole V lam n).comp
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact pinPole_le_one V hlam y x

lemma cavU_pos (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) (x : E) :
    0 < cavU V lam n a x := by
  haveI := isProb_pinnedLaw V hlam n a
  exact integral_exp_pos (f := fun y : Fin n → E => -(lam * ∑ k, V.q (y k) x))
    (integrable_pinPole V hlam a n x)

lemma cavU_le_one (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) (x : E) :
    cavU V lam n a x ≤ 1 := by
  haveI := isProb_pinnedLaw V hlam n a
  unfold cavU
  calc ∫ y, Real.exp (-(lam * ∑ k, V.q (y k) x)) ∂(pinnedLaw V lam n a)
      ≤ ∫ _y, (1 : ℝ) ∂(pinnedLaw V lam n a) :=
        integral_mono (integrable_pinPole V hlam a n x) (integrable_const _)
          fun y => pinPole_le_one V hlam y x
    _ = 1 := by simp

/-- The unnormalised one-point density `Θ(x) = e^{ψ(x)} u(x)`. -/
def cavTheta (V : WeakPotential μ) (lam : ℝ) (n : ℕ) (a : B → E) (x : E) : ℝ :=
  Real.exp (pinField V lam a x) * cavU V lam n a x

lemma measurable_cavTheta (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) :
    Measurable (cavTheta V lam n a) :=
  ((isField_pinField V hlam a).measurable.exp).mul (measurable_cavU V hlam n a)

lemma cavTheta_pos (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) (x : E) :
    0 < cavTheta V lam n a x := mul_pos (Real.exp_pos _) (cavU_pos V hlam a n x)

lemma cavTheta_le (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) (x : E) :
    cavTheta V lam n a x ≤ Real.exp V.M := by
  unfold cavTheta
  calc Real.exp (pinField V lam a x) * cavU V lam n a x ≤ Real.exp V.M * 1 := by
        refine mul_le_mul (Real.exp_le_exp.2 ((isField_pinField V hlam a).le x)) (cavU_le_one V hlam a n x)
          (cavU_pos V hlam a n x).le (Real.exp_pos _).le
    _ = _ := mul_one _

lemma integrable_cavTheta (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) :
    Integrable (cavTheta V lam n a) μ :=
  Integrable.of_bound (C := Real.exp V.M) (measurable_cavTheta V hlam a n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (cavTheta_pos V hlam a n x)]; exact cavTheta_le V hlam a n x)

lemma integral_cavTheta_pos (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) :
    0 < ∫ x, cavTheta V lam n a x ∂μ :=
  integral_pos_iff_support_of_nonneg (fun x => (cavTheta_pos V hlam a n x).le)
    (integrable_cavTheta V hlam a n) |>.2 (by
      have : Function.support (cavTheta V lam n a) = Set.univ := by
        ext x; simp [(cavTheta_pos V hlam a n x).ne']
      rw [this]; simp)

/-- **Normalised cavity formula**: the one-coordinate marginal of the `(n+1)`-particle pinned weak
ensemble has `μ`-density `Θ / ∫ Θ`. -/
theorem marginal_eq_normalized (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) :
    (pinnedLaw V lam (n + 1) a).map (fun y => y i) =
      μ.withDensity (fun x => ENNReal.ofReal (cavTheta V lam n a x / ∫ x', cavTheta V lam n a x' ∂μ)) := by
  have hmain := marginal_eq_withDensity V hlam a i (n := n)
  haveI := isProb_pinnedLaw V hlam (n + 1) a
  set Z := ∫ x', cavTheta V lam n a x' ∂μ with hZ
  have hZpos : 0 < Z := integral_cavTheta_pos V hlam a n
  set c := fieldNorm V (pinField V lam a) lam n * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹ with hc
  have hΘ : ∀ x, ENNReal.ofReal (Real.exp (pinField V lam a x)) * ENNReal.ofReal (cavU V lam n a x)
      = ENNReal.ofReal (cavTheta V lam n a x) := fun x =>
    (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  simp_rw [hΘ] at hmain
  have hZl : ∫⁻ x, ENNReal.ofReal (cavTheta V lam n a x) ∂μ = ENNReal.ofReal Z :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_cavTheta V hlam a n)
      (Filter.Eventually.of_forall fun x => (cavTheta_pos V hlam a n x).le)).symm
  have hmass := measure_univ (μ := (pinnedLaw V lam (n + 1) a).map (fun y => y i))
  rw [hmain, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_const_mul c (f := fun x => ENNReal.ofReal (cavTheta V lam n a x))
      (ENNReal.measurable_ofReal.comp (measurable_cavTheta V hlam a n)), hZl] at hmass
  have hc' : c = (ENNReal.ofReal Z)⁻¹ := by
    have hne : ENNReal.ofReal Z ≠ 0 := by simpa using hZpos
    exact ENNReal.eq_inv_of_mul_eq_one_left hmass
  rw [hmain]
  congr 1
  funext x
  rw [hc', ENNReal.ofReal_div_of_pos hZpos, div_eq_mul_inv, mul_comm]

omit [IsProbabilityMeasure μ] in
theorem pinnedLaw_empty (V : WeakPotential μ) (lam : ℝ)
    (n : ℕ) (a : Empty → E) : pinnedLaw V lam n a = fieldLaw V V.φ lam n := by
  unfold pinnedLaw
  congr 1
  funext z
  simp [pinField]

end Ensemble

section Prob


theorem exp_le_one_add_add_sq {c : ℝ} (hc : 0 ≤ c) {x : ℝ} (hx : x ≤ c) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 * Real.exp c := by
  set g : ℝ → ℝ := fun x => 1 + x + x ^ 2 / 2 * Real.exp c - Real.exp x with hg
  have hg' : ∀ x, HasDerivAt g (1 + x * Real.exp c - Real.exp x) x := by
    intro x
    have h1 := (((hasDerivAt_id x).const_add 1).add (((hasDerivAt_pow 2 x).div_const 2).mul_const (Real.exp c)))
    have h2 := h1.sub (Real.hasDerivAt_exp x)
    refine (h2.congr_deriv ?_)
    simp
  set g1 : ℝ → ℝ := fun x => 1 + x * Real.exp c - Real.exp x with hg1
  have hg1' : ∀ x, HasDerivAt g1 (Real.exp c - Real.exp x) x := by
    intro x
    have h1 := (((hasDerivAt_id x).mul_const (Real.exp c)).const_add 1).sub (Real.hasDerivAt_exp x)
    refine (h1.congr_deriv ?_)
    simp
  have hmono : MonotoneOn g1 (Set.Iic c) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic c) (fun x _ => (hg1' x).continuousAt.continuousWithinAt)
      (fun x _ => (hg1' x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [(hg1' x).deriv]
    have : x ≤ c := by simpa using interior_subset hx
    linarith [Real.exp_le_exp.2 this]
  have h0 : g1 0 = 0 := by simp [hg1]
  have e0 : g 0 = 0 := by simp [hg]
  rcases le_total x 0 with hx0 | hx0
  · have hanti : AntitoneOn g (Set.Iic 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Iic 0) (fun x _ => (hg' x).continuousAt.continuousWithinAt)
        (fun x _ => (hg' x).differentiableAt.differentiableWithinAt) fun y hy => ?_
      rw [(hg' y).deriv]
      have hy0 : y ≤ 0 := by simpa using interior_subset hy
      have := hmono (show y ∈ Set.Iic c from le_trans hy0 hc) (show (0:ℝ) ∈ Set.Iic c from hc) hy0
      change g1 y ≤ g1 0 at this
      rw [h0] at this
      exact this
    have := hanti (show x ∈ Set.Iic 0 from hx0) (show (0:ℝ) ∈ Set.Iic 0 from Set.mem_Iic.2 le_rfl) hx0
    rw [e0] at this
    simp only [hg] at this
    linarith
  · have hmon : MonotoneOn g (Set.Icc 0 c) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 c) (fun x _ => (hg' x).continuousAt.continuousWithinAt)
        (fun x _ => (hg' x).differentiableAt.differentiableWithinAt) fun y hy => ?_
      rw [(hg' y).deriv]
      rw [interior_Icc] at hy
      have := hmono (show (0:ℝ) ∈ Set.Iic c from hc) (show y ∈ Set.Iic c from hy.2.le) hy.1.le
      change g1 0 ≤ g1 y at this
      rw [h0] at this
      exact this
    have := hmon (show (0:ℝ) ∈ Set.Icc 0 c from ⟨le_rfl, hc⟩) (show x ∈ Set.Icc 0 c from ⟨hx0, hx⟩) hx0
    rw [e0] at this
    simp only [hg] at this
    linarith


theorem log_integral_exp_neg_add_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F F' : Ω → ℝ) (hF : Measurable F) (hF' : Measurable F') (h0 : ∀ ω, 0 ≤ F' ω)
    (hle : ∀ ω, F' ω ≤ F ω) (hF'2 : MemLp F' 2 P) :
    Real.log (∫ ω, Real.exp (-F ω) ∂P) + ∫ ω, F ω ∂P ≤
      Real.exp (∫ ω, F' ω ∂P) / 2 * ProbabilityTheory.variance F' P + (∫ ω, F ω ∂P - ∫ ω, F' ω ∂P) := by
  set m := ∫ ω, F' ω ∂P with hm
  have hm0 : 0 ≤ m := integral_nonneg h0
  have hF'i : Integrable F' P := hF'2.integrable one_le_two
  have hbd : ∀ G : Ω → ℝ, Measurable G → (∀ ω, 0 ≤ G ω) → Integrable (fun ω => Real.exp (-G ω)) P := by
    intro G hG hG0
    refine Integrable.of_bound (C := 1) (Real.measurable_exp.comp hG.neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    linarith [hG0 ω]
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => (h0 ω).trans (hle ω)
  have hiF := hbd F hF hF0
  have hiF' := hbd F' hF' h0
  have hpos : 0 < ∫ ω, Real.exp (-F ω) ∂P := integral_exp_pos (f := fun ω => -F ω) hiF
  have h1 : ∫ ω, Real.exp (-F ω) ∂P ≤ ∫ ω, Real.exp (-F' ω) ∂P :=
    integral_mono hiF hiF' fun ω => Real.exp_le_exp.2 (neg_le_neg (hle ω))
  set v := ProbabilityTheory.variance F' P with hv
  have hvar : ∫ ω, (F' ω - m) ^ 2 ∂P = v := by
    rw [hv, ProbabilityTheory.variance_eq_integral hF'.aemeasurable]
  have hsq : Integrable (fun ω => (m - F' ω) ^ 2) P := by
    have := (hF'2.sub (memLp_const m)).integrable_sq
    refine (this.congr (Filter.Eventually.of_forall fun ω => ?_))
    simp only [Pi.sub_apply]
    ring
  have hX : Integrable (fun ω => m - F' ω) P := (integrable_const m).sub hF'i
  have hXint : ∫ ω, (m - F' ω) ∂P = 0 := by
    rw [integral_sub (integrable_const m) hF'i]
    simp [hm]
  have hX2 : ∫ ω, (m - F' ω) ^ 2 ∂P = v := by
    rw [← hvar]; congr 1; funext ω; ring
  have h2 : ∫ ω, Real.exp (-F' ω) ∂P ≤ Real.exp (-m) * (1 + Real.exp m / 2 * v) := by
    have hpt : ∀ ω, Real.exp (-F' ω) ≤ Real.exp (-m) * (1 + (m - F' ω) + (m - F' ω) ^ 2 / 2 * Real.exp m) := by
      intro ω
      have := exp_le_one_add_add_sq hm0 (x := m - F' ω) (by linarith [h0 ω])
      have e : Real.exp (-F' ω) = Real.exp (-m) * Real.exp (m - F' ω) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    have hi2 : Integrable (fun ω => (m - F' ω) ^ 2 / 2 * Real.exp m) P :=
      (hsq.div_const 2).mul_const _
    have hi1 : Integrable (fun ω => 1 + (m - F' ω)) P := (integrable_const 1).add hX
    have hint : Integrable (fun ω => Real.exp (-m) * (1 + (m - F' ω) + (m - F' ω) ^ 2 / 2 * Real.exp m)) P :=
      (hi1.add hi2).const_mul _
    refine (integral_mono hiF' hint hpt).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add hi1 hi2, integral_add (integrable_const 1) hX, hXint,
      integral_mul_const, integral_div, hX2]
    simp
    ring
  have h3 : Real.log (∫ ω, Real.exp (-F ω) ∂P) ≤ -m + Real.exp m / 2 * v := by
    have hv0 : 0 ≤ v := ProbabilityTheory.variance_nonneg _ _
    have hlog : Real.log (∫ ω, Real.exp (-F ω) ∂P) ≤ Real.log (Real.exp (-m) * (1 + Real.exp m / 2 * v)) :=
      Real.log_le_log hpos (h1.trans h2)
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp] at hlog
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp m / 2 * v by positivity)
    linarith
  linarith

theorem log_integral_exp_neg_add_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (hF : Measurable F) (h0 : ∀ ω, 0 ≤ F ω) (hFi : Integrable F P) :
    0 ≤ Real.log (∫ ω, Real.exp (-F ω) ∂P) + ∫ ω, F ω ∂P := by
  have hbd : Integrable (fun ω => Real.exp (-F ω)) P := by
    refine Integrable.of_bound (C := 1) (Real.measurable_exp.comp hF.neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    linarith [h0 ω]
  have hpos : 0 < ∫ ω, Real.exp (-F ω) ∂P := integral_exp_pos (f := fun ω => -F ω) hbd
  have hJ := convexOn_exp.map_integral_le (μ := P) (f := fun ω => -F ω) Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hFi.neg hbd
  rw [integral_neg] at hJ
  have := Real.log_le_log (Real.exp_pos _) hJ
  rw [Real.log_exp] at this
  linarith


end Prob

section CavD

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

lemma measurable_qx (V : WeakPotential μ) (x : E) : Measurable fun y => V.q y x :=
  V.measurable_q.comp (measurable_id.prodMk measurable_const)

/-- The cavity marginal `ν`: the one-coordinate marginal of the `n`-particle ensemble without pins. -/
def cavMarg (V : WeakPotential μ) (lam : ℝ) (n : ℕ) [NeZero n] : Measure E :=
  (pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun y => y 0)

lemma pinnedLaw_marginal_eq (V : WeakPotential μ) {lam : ℝ} (n : ℕ) [NeZero n] (k : Fin n) :
    (pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun y => y k) = cavMarg V lam n := by
  unfold cavMarg
  rw [pinnedLaw_empty]
  exact map_eval_eq_of_symm μ _ (measurable_fieldDensity V.measurable_φ V lam n)
    (fun σ y => fieldDensity_comp_perm V _ _ σ y) k 0

theorem cavD_bounds (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} [NeZero n] (hN0 : 0 < N)
    (hn : n ≤ N) (hκ : weakKappa V β ≤ 1 / 2) (x : E) {mb : ℝ}
    (hm : β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ≤ mb) :
    0 ≤ Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
        β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ∧
    Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
        β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ≤
      Real.exp mb * (n * ∫ y, (min (β / N * V.q y x) 1) ^ 2 ∂(cavMarg V (β / N) n)) +
        n * ∫ y, max (β / N * V.q y x - 1) 0 ∂(cavMarg V (β / N) n) := by
  set lam : ℝ := β / N with hlam_def
  have hlam : 0 ≤ lam := div_nonneg hβ (Nat.cast_nonneg N)
  set a : Empty → E := fun e => e.elim with ha
  set P := pinnedLaw V lam n a with hP
  haveI : IsProbabilityMeasure P := isProb_pinnedLaw V hlam n a
  set ν := cavMarg V lam n with hν
  have hmarg : ∀ k : Fin n, P.map (fun y => y k) = ν := fun k => pinnedLaw_marginal_eq V n k
  haveI : IsProbabilityMeasure ν := by
    rw [← hmarg 0]; infer_instance
  have hνle : ν ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) • μ := by
    have := marginal_le_smul (B := Empty) V hβ hN0 (n := n) (by simpa using hn) a 0
    exact this
  set g : E → ℝ := fun y => V.q y x with hg
  have hgm : Measurable g := measurable_qx V x
  have hg0 : ∀ y, 0 ≤ g y := fun y => V.q_nonneg _ _
  have hgi : Integrable g ν := by
    have hμ : Integrable g μ := integrable_q_left V x
    exact Integrable.of_measure_le_smul ENNReal.ofReal_ne_top hνle hμ
  -- the statistic `F_x = lam ∑_k g(y_k)` and its truncation
  set Fx : (Fin n → E) → ℝ := fun y => lam * ∑ k, g (y k) with hFx
  have hFxm : Measurable Fx := Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
    hgm.comp (measurable_pi_apply k)) _
  have hFx0 : ∀ y, 0 ≤ Fx y := fun y => mul_nonneg hlam (Finset.sum_nonneg fun k _ => hg0 _)
  have hint_k : ∀ k : Fin n, Integrable (fun y : Fin n → E => g (y k)) P := by
    intro k
    have := hgi
    rw [← hmarg k] at this
    exact (integrable_map_measure hgm.aestronglyMeasurable (measurable_pi_apply k).aemeasurable).1 this
  have hint_k' : ∀ k : Fin n, ∫ y, g (y k) ∂P = ∫ y, g y ∂ν := by
    intro k
    rw [← hmarg k, integral_map (measurable_pi_apply k).aemeasurable hgm.aestronglyMeasurable]
  have hFxi : Integrable Fx P := (integrable_finset_sum _ fun k _ => hint_k k).const_mul lam
  have hEF : ∫ y, Fx y ∂P = lam * n * ∫ y, g y ∂ν := by
    simp only [hFx]
    rw [integral_const_mul, integral_finset_sum _ fun k _ => hint_k k]
    simp_rw [hint_k']
    simp
    ring
  have hcav : cavU V lam n a x = ∫ y, Real.exp (-Fx y) ∂P := rfl
  refine ⟨?_, ?_⟩
  · rw [hcav, ← hEF]
    exact log_integral_exp_neg_add_nonneg P Fx hFxm hFx0 hFxi
  set f : E → ℝ := fun u => min (lam * g u) 1 with hf
  have hfm : Measurable f := (hgm.const_mul lam).min measurable_const
  have hf0 : ∀ u, 0 ≤ f u := fun u => le_min (mul_nonneg hlam (hg0 u)) zero_le_one
  have hf1 : ∀ u, f u ≤ 1 := fun u => min_le_right _ _
  set F' : (Fin n → E) → ℝ := fun y => ∑ k, f (y k) with hF'
  have hF'm : Measurable F' := Finset.measurable_sum _ fun k _ => hfm.comp (measurable_pi_apply k)
  have hF'0 : ∀ y, 0 ≤ F' y := fun y => Finset.sum_nonneg fun k _ => hf0 _
  have hF'le : ∀ y, F' y ≤ Fx y := by
    intro y
    simp only [hF', hFx, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => min_le_left _ _
  have hF'b : ∀ y, ‖F' y‖ ≤ n := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (hF'0 y)]
    calc F' y ≤ ∑ _k : Fin n, (1 : ℝ) := Finset.sum_le_sum fun k _ => hf1 _
      _ = n := by simp
  have hF'2 : MemLp F' 2 P := MemLp.of_bound hF'm.aestronglyMeasurable n (Filter.Eventually.of_forall hF'b)
  have hfi : ∀ k : Fin n, Integrable (fun y : Fin n → E => f (y k)) P := by
    intro k
    exact Integrable.of_bound (hfm.comp (measurable_pi_apply k)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]; exact hf1 _)
  have hfνi : Integrable f ν := Integrable.of_bound hfm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]; exact hf1 _)
  have hfk : ∀ k : Fin n, ∫ y, f (y k) ∂P = ∫ y, f y ∂ν := by
    intro k
    rw [← hmarg k, integral_map (measurable_pi_apply k).aemeasurable hfm.aestronglyMeasurable]
  have hEF' : ∫ y, F' y ∂P = n * ∫ y, f y ∂ν := by
    simp only [hF']
    rw [integral_finset_sum _ fun k _ => hfi k]
    simp_rw [hfk]
    simp
  have hvar : variance F' P ≤ 2 * n * variance f ν := by
    have hf2 : MemLp f 2 ν := MemLp.of_bound hfm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]; exact hf1 _)
    exact weak_linear_variance_real V hβ hN0 (B := Empty) (n := n) (by simpa using hn) a hκ ν hmarg f hfm hf2
  have hvar2 : variance f ν ≤ ∫ y, (f y) ^ 2 ∂ν := by
    have := variance_le_expectation_sq (μ := ν) (X := f) hfm.aestronglyMeasurable
    simpa using this
  have hmaxint : ∫ y, max (lam * g y - 1) 0 ∂ν = lam * ∫ y, g y ∂ν - ∫ y, f y ∂ν := by
    have e : ∀ y, max (lam * g y - 1) 0 = lam * g y - f y := by
      intro y
      simp only [hf]
      rcases le_total (lam * g y) 1 with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]
    simp_rw [e]
    rw [integral_sub (hgi.const_mul lam) hfνi, integral_const_mul]
  have hdiff : ∫ y, Fx y ∂P - ∫ y, F' y ∂P = n * ∫ y, max (lam * g y - 1) 0 ∂ν := by
    rw [hEF, hEF', hmaxint]; ring
  have hEFle : ∫ y, F' y ∂P ≤ ∫ y, Fx y ∂P :=
    integral_mono (integrable_finset_sum _ fun k _ => hfi k) hFxi hF'le
  have hmain := log_integral_exp_neg_add_le P Fx F' hFxm hF'm hF'0 hF'le hF'2
  rw [← hcav] at hmain
  have hexp : Real.exp (∫ y, F' y ∂P) ≤ Real.exp mb := by
    refine Real.exp_le_exp.2 (hEFle.trans ?_)
    rw [hEF]; exact hm
  have hv0 : 0 ≤ variance F' P := variance_nonneg _ _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Real.exp (∫ y, F' y ∂P) / 2 * variance F' P ≤
      Real.exp mb / 2 * (2 * n * ∫ y, (f y) ^ 2 ∂ν) := by
    have hv : variance F' P ≤ 2 * n * ∫ y, (f y) ^ 2 ∂ν :=
      hvar.trans (mul_le_mul_of_nonneg_left hvar2 (by positivity))
    calc Real.exp (∫ y, F' y ∂P) / 2 * variance F' P
        ≤ Real.exp mb / 2 * variance F' P := by gcongr
      _ ≤ _ := by gcongr
  rw [← hEF]
  have e2 : Real.exp mb / 2 * (2 * n * ∫ y, (f y) ^ 2 ∂ν) = Real.exp mb * (n * ∫ y, (f y) ^ 2 ∂ν) := by ring
  have : Real.exp mb * (n * ∫ y, (f y) ^ 2 ∂ν) + n * ∫ y, max (lam * g y - 1) 0 ∂ν =
      Real.exp mb * (n * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν) + n * ∫ y, max (lam * V.q y x - 1) 0 ∂ν := rfl
  rw [← this]
  linarith [hmain, h1, hdiff, e2]

end CavD

section Kernel

variable {d : ℕ} {s : ℝ}

/-- Volume of a small Euclidean ball on the torus. -/
theorem volume_eucBall_le {R : ℝ} (hR : 0 ≤ R) :
    (volume : Measure (Torus d)) {z : Torus d | Torus.eucDist z 0 < R} ≤ ENNReal.ofReal ((2 * R) ^ d) := by
  have hmeas : MeasurableSet {z : Torus d | Torus.eucDist z 0 < R} := by
    have : Continuous fun z : Torus d => Torus.eucDist z 0 := by
      unfold Torus.eucDist
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      refine (continuous_norm.comp ((continuous_apply i).sub continuous_const)).pow 2
    exact measurableSet_lt this.measurable measurable_const
  have h1 := KernelAux.lintegral_torus_box (d := d) ({z : Torus d | Torus.eucDist z 0 < R}.indicator 1)
  rw [lintegral_indicator_one hmeas] at h1
  rw [h1]
  have h2 : ∀ y ∈ KernelAux.Box d, ({z : Torus d | Torus.eucDist z 0 < R}.indicator (1 : Torus d → ℝ≥0∞))
      (KernelAux.boxPt y) ≤ (Set.pi Set.univ fun _ : Fin d => Set.Ioo (-R) R).indicator 1 y := by
    intro y hy
    by_cases h : Torus.eucDist (KernelAux.boxPt y) 0 < R
    · have hmem : ∀ i, y i ∈ Set.Ioo (-R) R := by
        intro i
        have hb := KernelAux.Box_abs_le hy
        rw [eucDist_boxPt hb] at h
        have : |y i| ≤ Real.sqrt (∑ i, (y i) ^ 2) := by
          rw [← Real.sqrt_sq_eq_abs]
          exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => (y i) ^ 2) (fun i _ => sq_nonneg _)
            (Finset.mem_univ i))
        have := lt_of_le_of_lt this h
        exact ⟨by linarith [neg_abs_le (y i)], by linarith [le_abs_self (y i)]⟩
      have hm : y ∈ Set.pi Set.univ fun _ : Fin d => Set.Ioo (-R) R := fun i _ => hmem i
      simp [Set.indicator, h, hm]
    · simp [Set.indicator, h]
  calc ∫⁻ y in KernelAux.Box d, ({z : Torus d | Torus.eucDist z 0 < R}.indicator (1 : Torus d → ℝ≥0∞))
        (KernelAux.boxPt y)
      ≤ ∫⁻ y in KernelAux.Box d, (Set.pi Set.univ fun _ : Fin d => Set.Ioo (-R) R).indicator 1 y :=
        setLIntegral_mono' (KernelAux.measurableSet_Box d) h2
    _ ≤ ∫⁻ y, (Set.pi Set.univ fun _ : Fin d => Set.Ioo (-R) R).indicator 1 y :=
        setLIntegral_le_lintegral _ _
    _ = volume (Set.pi Set.univ fun _ : Fin d => Set.Ioo (-R) R) := by
        rw [lintegral_indicator_one]
        exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo
    _ = ENNReal.ofReal ((2 * R) ^ d) := by
        rw [Real.volume_pi_Ioo]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [ENNReal.ofReal_pow (by linarith)]
        congr 2
        ring


/-- Exponent of the weak-`L^p` bound of the singular kernel: `p = d/s` (`s > 0`), `p = 3` (`s = 0`). -/
def pOf (d : ℕ) (s : ℝ) : ℝ := if s = 0 then 3 else (d : ℝ) / s

theorem one_lt_pOf (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : 1 < pOf d s := by
  unfold pOf
  split_ifs with h
  · norm_num
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    rw [lt_div_iff₀ hs]; linarith

theorem eucDist_le_half_sqrt (z : Torus d) : Torus.eucDist z 0 ≤ Real.sqrt d / 2 := by
  unfold Torus.eucDist
  have h1 : ∀ i, ‖z i - (0 : Torus d) i‖ ^ 2 ≤ 1 / 4 := by
    intro i
    have : ‖z i - (0 : Torus d) i‖ ≤ 1 / 2 := by
      have := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := z i - (0 : Torus d) i) one_ne_zero
      simpa using this
    nlinarith [norm_nonneg (z i - (0 : Torus d) i)]
  have h2 : ∑ i, ‖z i - (0 : Torus d) i‖ ^ 2 ≤ (d : ℝ) / 4 := by
    calc ∑ i, ‖z i - (0 : Torus d) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 / 4 : ℝ) := Finset.sum_le_sum fun i _ => h1 i
      _ = (d : ℝ) / 4 := by simp; ring
  calc Real.sqrt (∑ i, ‖z i - (0 : Torus d) i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) / 4) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt d / 2 := by
        rw [Real.sqrt_div (Nat.cast_nonneg d)]
        have : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
        rw [this]


theorem one_le_singEnvelope'' {s e : ℝ} (he : 0 ≤ e) : 1 ≤ singEnvelope s e := one_le_singEnvelope' he

theorem eucDist_nonneg_aux (z : Torus d) : 0 ≤ Torus.eucDist z 0 := Real.sqrt_nonneg _

theorem eucDist_pos_of_ne {z : Torus d} (hz : z ≠ 0) : 0 < Torus.eucDist z 0 := by
  rcases (eucDist_nonneg_aux z).eq_or_lt with h | h
  · exfalso
    apply hz
    unfold Torus.eucDist at h
    have h0 := (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)).1 h.symm
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (‖z i - (0 : Torus d) i‖))).1 h0 i
      (Finset.mem_univ i)
    have h1 : ‖z i - (0 : Torus d) i‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
    simpa using h1
  · exact h

/-- **Weak-`L^p` bound** for a kernel with the singular envelope `q ≤ B (1 + |x|^{-s})`
(`1 + |log|x||` for `s = 0`): `|{q > r}| ≤ K₀ r^{-p}` with `p = pOf d s`. -/
theorem weakLp_of_envelope (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {B : ℝ} (hB : 0 ≤ B)
    {q : Torus d → ℝ} (hq : ∀ x, x ≠ 0 → q x ≤ B * singEnvelope s (Torus.eucDist x 0)) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ r : ℝ, 0 < r →
      (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤ ENNReal.ofReal (K0 * r ^ (-(pOf d s))) := by
  set B' := B + 1 with hB'
  have hB'pos : 0 < B' := by linarith
  have hq' : ∀ x, x ≠ 0 → q x ≤ B' * singEnvelope s (Torus.eucDist x 0) := fun x hx =>
    (hq x hx).trans (mul_le_mul_of_nonneg_right (by linarith) (by
      have := one_le_singEnvelope' (s := s) (eucDist_nonneg_aux x); linarith))
  have hp1 := one_lt_pOf hd hs0 hsd
  set p := pOf d s with hp
  have hp0 : 0 < p := by linarith
  have hsub : ∀ (R : ℝ), 0 ≤ R → ∀ r : ℝ, (∀ z : Torus d, z ≠ 0 → r < q z → Torus.eucDist z 0 < R) →
      (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤ ENNReal.ofReal ((2 * R) ^ d) := by
    intro R hR r h
    calc (volume : Measure (Torus d)) {z : Torus d | r < q z}
        ≤ (volume : Measure (Torus d)) ({z : Torus d | Torus.eucDist z 0 < R} ∪ {0}) := by
          refine measure_mono fun z hz => ?_
          by_cases hz0 : z = 0
          · exact Or.inr hz0
          · exact Or.inl (h z hz0 hz)
      _ ≤ (volume : Measure (Torus d)) {z : Torus d | Torus.eucDist z 0 < R} +
          (volume : Measure (Torus d)) {0} := measure_union_le _ _
      _ = (volume : Measure (Torus d)) {z : Torus d | Torus.eucDist z 0 < R} := by
          rw [volume_singleton_torus (by omega : 1 ≤ d) 0, add_zero]
      _ ≤ _ := volume_eucBall_le hR
  by_cases hs : s = 0
  · have hp3 : p = 3 := by rw [hp]; unfold pOf; simp [hs]
    set L₁ := |Real.log (Real.sqrt d / 2)| with hL₁
    set r₁ := 2 * B' * (1 + L₁) with hr₁
    have hL₁0 : 0 ≤ L₁ := abs_nonneg _
    have hr₁pos : 0 < r₁ := by positivity
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    set C₃ : ℝ := (3 : ℝ) ^ (3 : ℝ) * Real.exp (-3) with hC₃
    refine ⟨r₁ ^ 3 + 2 ^ d * C₃ * (2 * B' / d) ^ 3, by positivity, fun r hr => ?_⟩
    rw [hp3]
    by_cases hr2 : r < r₁
    · calc (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤ 1 := prob_le_one
        _ ≤ ENNReal.ofReal ((r₁ ^ 3 + 2 ^ d * C₃ * (2 * B' / d) ^ 3) * r ^ (-(3 : ℝ))) := by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (1 : ℝ) ≤ (r₁ / r) ^ 3 := one_le_pow₀ (by rw [le_div_iff₀ hr]; linarith)
          rw [div_pow] at h1
          rw [one_le_div (by positivity)] at h1
          rw [Real.rpow_neg hr.le, ← div_eq_mul_inv]
          have e3 : r ^ (3 : ℝ) = r ^ 3 := by exact_mod_cast Real.rpow_natCast r 3
          rw [e3, le_div_iff₀ (by positivity)]
          have : 0 ≤ 2 ^ d * C₃ * (2 * B' / d) ^ 3 := by positivity
          linarith
    · have hr2 := not_lt.1 hr2
      set E0 := Real.exp (-(r / (2 * B'))) with hE0
      have hE0pos : 0 < E0 := Real.exp_pos _
      have key := hsub E0 hE0pos.le r (fun z hz hrz => by
        by_contra hcon
        have hcon := not_lt.1 hcon
        have he := eucDist_pos_of_ne hz
        have h5 := hq' z hz
        have h6 : singEnvelope s (Torus.eucDist z 0) = 1 + |Real.log (Torus.eucDist z 0)| := by
          unfold singEnvelope; simp [hs]
        rw [h6] at h5
        have hr2B : 2 * B' ≤ r := by
          have : 2 * B' ≤ r₁ := by rw [hr₁]; nlinarith
          linarith
        by_cases he1 : 1 ≤ Torus.eucDist z 0
        · have hlog : |Real.log (Torus.eucDist z 0)| ≤ L₁ := by
            rw [abs_of_nonneg (Real.log_nonneg he1)]
            have : Real.log (Torus.eucDist z 0) ≤ Real.log (Real.sqrt d / 2) :=
              Real.log_le_log he (eucDist_le_half_sqrt z)
            exact this.trans (le_abs_self _)
          have : q z ≤ B' * (1 + L₁) := h5.trans (mul_le_mul_of_nonneg_left (by linarith) hB'pos.le)
          nlinarith
        · have he1' := not_le.1 he1
          have hlog : |Real.log (Torus.eucDist z 0)| ≤ r / (2 * B') := by
            rw [abs_of_neg (Real.log_neg he he1')]
            have : -(r / (2 * B')) ≤ Real.log (Torus.eucDist z 0) := by
              rw [← Real.log_exp (-(r / (2 * B')))]
              exact Real.log_le_log hE0pos hcon
            linarith
          have : q z ≤ B' * (1 + r / (2 * B')) :=
            h5.trans (mul_le_mul_of_nonneg_left (by linarith) hB'pos.le)
          have e : B' * (1 + r / (2 * B')) = B' + r / 2 := by field_simp
          linarith)
      refine key.trans (ENNReal.ofReal_le_ofReal ?_)
      have hv : 0 < (d : ℝ) * r / (2 * B') := by positivity
      have h1 := KernelAux.exp_neg_le_rpow (q := (3 : ℝ)) (by norm_num) hv
      have e1 : (2 * E0) ^ d = 2 ^ d * Real.exp (-((d : ℝ) * r / (2 * B'))) := by
        rw [mul_pow, hE0, ← Real.exp_nat_mul]
        congr 2
        field_simp
      rw [e1]
      have e3 : r ^ (-(3 : ℝ)) = (r ^ 3)⁻¹ := by
        rw [Real.rpow_neg hr.le]; congr 1; exact_mod_cast Real.rpow_natCast r 3
      have e4 : ((d : ℝ) * r / (2 * B')) ^ (-(3 : ℝ)) = (2 * B' / d) ^ 3 * (r ^ 3)⁻¹ := by
        rw [Real.rpow_neg hv.le]
        have : (((d : ℝ) * r / (2 * B')) ^ (3 : ℝ)) = ((d : ℝ) * r / (2 * B')) ^ 3 := by
          exact_mod_cast Real.rpow_natCast _ 3
        rw [this]
        field_simp
      rw [e4] at h1
      rw [e3]
      have hfin : 2 ^ d * Real.exp (-((d : ℝ) * r / (2 * B'))) ≤
          2 ^ d * (C₃ * ((2 * B' / d) ^ 3 * (r ^ 3)⁻¹)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      refine hfin.trans ?_
      have : 0 ≤ (r ^ 3)⁻¹ := by positivity
      have : 0 ≤ 2 ^ d * C₃ * (2 * B' / d) ^ 3 * (r ^ 3)⁻¹ := by positivity
      nlinarith [pow_nonneg hr.le 3, mul_nonneg (pow_nonneg hr₁pos.le 3) (inv_nonneg.2 (pow_nonneg hr.le 3))]
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hpdef : p = (d : ℝ) / s := by rw [hp]; unfold pOf; simp [hs]
    refine ⟨2 ^ d * (2 * B') ^ p, by positivity, fun r hr => ?_⟩
    by_cases hr2 : r < 2 * B'
    · calc (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤ 1 := prob_le_one
        _ ≤ ENNReal.ofReal (2 ^ d * (2 * B') ^ p * r ^ (-p)) := by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 1 ≤ ((2 * B') / r) ^ p := Real.one_le_rpow (by rw [le_div_iff₀ hr]; linarith) hp0.le
          rw [Real.div_rpow (by positivity) hr.le] at h1
          rw [one_le_div (Real.rpow_pos_of_pos hr p)] at h1
          have h2 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
          rw [Real.rpow_neg hr.le, ← div_eq_mul_inv]
          calc (1 : ℝ) ≤ (2 * B') ^ p / r ^ p := by rw [le_div_iff₀ (Real.rpow_pos_of_pos hr p)]; linarith
            _ ≤ 2 ^ d * (2 * B') ^ p / r ^ p := by
              gcongr
              nlinarith [Real.rpow_pos_of_pos (show 0 < 2 * B' by linarith) p]
    · have hr2 := not_lt.1 hr2
      set R := ((2 * B') / r) ^ (1 / s) with hR
      have hRpos : 0 < R := Real.rpow_pos_of_pos (by positivity) _
      have key := hsub R hRpos.le r (fun z hz hrz => by
        by_contra hcon
        have hcon := not_lt.1 hcon
        have he := eucDist_pos_of_ne hz
        have h3 : Torus.eucDist z 0 ^ (-s) ≤ R ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos hRpos hcon (by linarith)
        have h4 : R ^ (-s) = r / (2 * B') := by
          rw [hR, ← Real.rpow_mul (by positivity)]
          have : 1 / s * -s = -1 := by field_simp
          rw [this, Real.rpow_neg_one, inv_div]
        have h5 := hq' z hz
        have h6 : singEnvelope s (Torus.eucDist z 0) = 1 + Torus.eucDist z 0 ^ (-s) := by
          unfold singEnvelope; simp [hs]
        rw [h6] at h5
        have h7 : r < B' * (1 + r / (2 * B')) := by
          calc r < q z := hrz
            _ ≤ B' * (1 + Torus.eucDist z 0 ^ (-s)) := h5
            _ ≤ B' * (1 + r / (2 * B')) := by
              rw [← h4]; gcongr
        have : B' * (1 + r / (2 * B')) = B' + r / 2 := by field_simp
        linarith)
      refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [mul_pow, hR]
      have e1 : (((2 * B') / r) ^ (1 / s)) ^ d = ((2 * B') / r) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hpdef]
        congr 1
        field_simp
      rw [e1, Real.div_rpow (by positivity) hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
      ring


section Layer

variable {q : Torus d → ℝ}

/-- Second moment of the truncated kernel via the distribution function. -/
theorem lintegral_minsq_le (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z) {K : ℝ} (hK : 1 ≤ K) {p K0 : ℝ}
    (hp : 1 < p) (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-p))) :
    ∫⁻ z, ENNReal.ofReal (min (q z) K ^ 2) ≤
      ENNReal.ofReal (1 + 2 * K0 * ∫ t in (1 : ℝ)..K, t ^ (1 - p)) := by
  have hf : Measurable fun z => min (q z) K := hq.min measurable_const
  have hf0 : ∀ z, 0 ≤ min (q z) K := fun z => le_min (hq0 z) (by linarith)
  have e1 : ∀ z, ENNReal.ofReal (min (q z) K ^ 2) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..min (q z) K, 2 * t) := by
    intro z
    congr 1
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  simp_rw [e1]
  rw [lintegral_comp_eq_lintegral_meas_lt_mul (volume : Measure (Torus d)) (f := fun z => min (q z) K)
    (Filter.Eventually.of_forall hf0) hf.aemeasurable (g := fun t => 2 * t)
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable _ _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
      have : (0 : ℝ) < t := ht
      show 0 ≤ 2 * t
      linarith))]
  set H : ℝ → ℝ≥0∞ := fun t => (Set.Ioc (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (2 * t)) t +
    (Set.Ioc (1 : ℝ) K).indicator (fun t => ENNReal.ofReal (2 * K0 * t ^ (1 - p))) t with hH
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), (volume : Measure (Torus d)) {a | t < min (q a) K} *
      ENNReal.ofReal (2 * t) ≤ H t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht0, ht1⟩
      have hn : t ∉ Set.Ioc (1 : ℝ) K := fun h => absurd h.1 (not_lt.2 ht1)
      simp only [hH, Set.indicator_of_mem hm, Set.indicator_of_notMem hn, add_zero]
      calc (volume : Measure (Torus d)) {a | t < min (q a) K} * ENNReal.ofReal (2 * t)
          ≤ 1 * ENNReal.ofReal (2 * t) := by gcongr; exact prob_le_one
        _ = _ := one_mul _
    · have ht1' := not_le.1 ht1
      by_cases htK : t ≤ K
      · have hm : t ∈ Set.Ioc (1 : ℝ) K := ⟨ht1', htK⟩
        have hn : t ∉ Set.Ioc (0 : ℝ) 1 := fun h => absurd h.2 ht1
        simp only [hH, Set.indicator_of_mem hm, Set.indicator_of_notMem hn, zero_add]
        calc (volume : Measure (Torus d)) {a | t < min (q a) K} * ENNReal.ofReal (2 * t)
            ≤ ENNReal.ofReal (K0 * t ^ (-p)) * ENNReal.ofReal (2 * t) := by
              gcongr
              refine le_trans (measure_mono fun a ha => ?_) (hw t ht0)
              have ha' : t < min (q a) K := ha
              exact lt_of_lt_of_le ha' (min_le_left _ _)
          _ = ENNReal.ofReal (2 * K0 * t ^ (1 - p)) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [show (1 - p) = 1 + (-p) by ring, Real.rpow_add ht0, Real.rpow_one]
              ring
      · have htK' := not_le.1 htK
        have hempty : {a : Torus d | t < min (q a) K} = ∅ := by
          ext a
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
          exact (min_le_right _ _).trans htK'.le
        rw [hempty]
        simp
  refine (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpt))).trans ?_
  have hmeas1 : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc
  have hmeas2 : MeasurableSet (Set.Ioc (1 : ℝ) K) := measurableSet_Ioc
  have hf1 : Measurable fun t : ℝ => ENNReal.ofReal (2 * t) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)
  have hf2 : Measurable fun t : ℝ => ENNReal.ofReal (2 * K0 * t ^ (1 - p)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  simp only [hH]
  rw [lintegral_add_left (hf1.indicator hmeas1), lintegral_indicator hmeas1, lintegral_indicator hmeas2,
    Measure.restrict_restrict hmeas1, Measure.restrict_restrict hmeas2]
  have i1 : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi 0 = Set.Ioc 0 1 := Set.inter_eq_left.2 fun x hx => hx.1
  have i2 : Set.Ioc (1 : ℝ) K ∩ Set.Ioi 0 = Set.Ioc 1 K := Set.inter_eq_left.2 fun x hx => by
    exact lt_trans zero_lt_one hx.1
  rw [i1, i2]
  have j1 : ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (2 * t) = ENNReal.ofReal 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul, integral_id]
      norm_num
    · exact (continuous_const.mul continuous_id).integrableOn_Ioc
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => by
        have : 0 < t := ht.1
        show 0 ≤ 2 * t
        linarith)
  have hcont : ContinuousOn (fun t : ℝ => 2 * K0 * t ^ (1 - p)) (Set.Icc 1 K) :=
    continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl (by
      have : (1 : ℝ) ≤ x := hx.1
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one this)))
  have j2 : ∫⁻ t in Set.Ioc (1 : ℝ) K, ENNReal.ofReal (2 * K0 * t ^ (1 - p)) =
      ENNReal.ofReal (2 * K0 * ∫ t in (1 : ℝ)..K, t ^ (1 - p)) := by
    rw [← intervalIntegral.integral_const_mul, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [intervalIntegral.integral_of_le hK]
    · exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => by
        have : 0 < t := lt_trans zero_lt_one ht.1
        positivity)
  rw [j1, j2, ← ENNReal.ofReal_add zero_le_one (by
    have : 0 ≤ ∫ t in (1 : ℝ)..K, t ^ (1 - p) :=
      intervalIntegral.integral_nonneg hK fun t ht => Real.rpow_nonneg (by linarith [ht.1]) _
    positivity)]

/-- Tail of the kernel above level `K` via the distribution function. -/
theorem lintegral_tail_le (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z) {K : ℝ} (hK : 0 < K) {p K0 : ℝ}
    (hp : 1 < p) (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-p))) :
    ∫⁻ z, ENNReal.ofReal (q z - K) ≤ ENNReal.ofReal (K0 * K ^ (1 - p) * (p / (p - 1))) := by
  have hf : Measurable fun z => max (q z - K) 0 := (hq.sub_const K).max measurable_const
  have e1 : ∀ z, ENNReal.ofReal (q z - K) = ENNReal.ofReal (max (q z - K) 0) := by
    intro z
    rw [ENNReal.ofReal_max]
    simp
  simp_rw [e1]
  rw [lintegral_eq_lintegral_meas_lt (volume : Measure (Torus d)) (f := fun z => max (q z - K) 0)
    (Filter.Eventually.of_forall fun z => le_max_right _ _) hf.aemeasurable]
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), (volume : Measure (Torus d)) {a | t < max (q a - K) 0} ≤
      (Set.Ioc (0 : ℝ) K).indicator (fun _ => ENNReal.ofReal (K0 * K ^ (-p))) t +
        (Set.Ioi K).indicator (fun t => ENNReal.ofReal (K0 * t ^ (-p))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hsub : {a : Torus d | t < max (q a - K) 0} ⊆ {a | K + t < q a} := by
      intro a ha
      have ha' : t < max (q a - K) 0 := ha
      rcases lt_max_iff.1 ha' with h | h
      · show K + t < q a
        linarith
      · exact absurd h (not_lt.2 ht0.le)
    have hKt : 0 < K + t := by linarith
    by_cases htK : t ≤ K
    · have hm : t ∈ Set.Ioc (0 : ℝ) K := ⟨ht0, htK⟩
      have hn : t ∉ Set.Ioi K := fun h => absurd h (not_lt.2 htK)
      rw [Set.indicator_of_mem hm, Set.indicator_of_notMem hn, add_zero]
      refine (measure_mono hsub).trans ((hw _ hKt).trans (ENNReal.ofReal_le_ofReal ?_))
      refine mul_le_mul_of_nonneg_left ?_ hK0.le
      exact Real.rpow_le_rpow_of_nonpos hK (by linarith) (by linarith)
    · have htK' := not_le.1 htK
      have hm : t ∈ Set.Ioi K := htK'
      have hn : t ∉ Set.Ioc (0 : ℝ) K := fun h => absurd h.2 htK
      rw [Set.indicator_of_mem hm, Set.indicator_of_notMem hn, zero_add]
      refine (measure_mono hsub).trans ((hw _ hKt).trans (ENNReal.ofReal_le_ofReal ?_))
      refine mul_le_mul_of_nonneg_left ?_ hK0.le
      exact Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
  refine (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpt))).trans ?_
  have hmeas1 : MeasurableSet (Set.Ioc (0 : ℝ) K) := measurableSet_Ioc
  have hmeas2 : MeasurableSet (Set.Ioi K) := measurableSet_Ioi
  have hf2 : Measurable fun t : ℝ => ENNReal.ofReal (K0 * t ^ (-p)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  rw [lintegral_add_left (measurable_const.indicator hmeas1), lintegral_indicator hmeas1,
    lintegral_indicator hmeas2, Measure.restrict_restrict hmeas1, Measure.restrict_restrict hmeas2]
  have i1 : Set.Ioc (0 : ℝ) K ∩ Set.Ioi 0 = Set.Ioc 0 K := Set.inter_eq_left.2 fun x hx => hx.1
  have i2 : Set.Ioi K ∩ Set.Ioi (0 : ℝ) = Set.Ioi K := Set.inter_eq_left.2 fun x hx => lt_trans hK hx
  rw [i1, i2, setLIntegral_const, Real.volume_Ioc]
  have hint : IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioi K) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hK
  have hI : ∫⁻ t in Set.Ioi K, ENNReal.ofReal (K0 * t ^ (-p)) =
      ENNReal.ofReal (K0 * (K ^ (1 - p) / (p - 1))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul K0)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
        have : 0 < t := lt_trans hK ht
        positivity))]
    congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hK]
    have h1 : -p + 1 = 1 - p := by ring
    rw [h1]
    congr 1
    rw [neg_div, ← div_neg, neg_sub]
  rw [hI, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by
    have : 0 < p - 1 := by linarith
    have := Real.rpow_pos_of_pos hK (1 - p)
    positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have e : K ^ (1 - p) = K * K ^ (-p) := by
    rw [show (1 - p) = 1 + (-p) by ring, Real.rpow_add hK, Real.rpow_one]
  have hp1 : p - 1 ≠ 0 := by linarith
  rw [sub_zero, e]
  field_simp
  ring

end Layer

end Kernel

section Rates

variable {d : ℕ} {s : ℝ}


theorem one_lt_pOf_aux (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : 1 < pOf d s := by
  unfold pOf
  split_ifs with h
  · norm_num
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    rw [lt_div_iff₀ hs]; linarith

theorem pOf_cases (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    (s < (d : ℝ) / 2 ∧ 2 < pOf d s) ∨ (s = (d : ℝ) / 2 ∧ pOf d s = 2) ∨
      ((d : ℝ) / 2 < s ∧ pOf d s = (d : ℝ) / s ∧ pOf d s < 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  by_cases hs : s = 0
  · left
    have hp3 : pOf d s = 3 := by unfold pOf; simp [hs]
    refine ⟨by rw [hs]; positivity, by rw [hp3]; norm_num⟩
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hpdef : pOf d s = (d : ℝ) / s := by unfold pOf; simp [hs]
    rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
    · left
      refine ⟨h, ?_⟩
      rw [hpdef, lt_div_iff₀ hspos]; linarith
    · right; left
      refine ⟨h, ?_⟩
      rw [hpdef, h]; field_simp
    · right; right
      refine ⟨h, hpdef, ?_⟩
      rw [hpdef, div_lt_iff₀ hspos]; linarith

/-- The growth function `g(K) = N δ_N`-profile: `1` (`s < d/2`), `log(eK)` (`s = d/2`), `K^{2-d/s}`. -/
def gFun (d : ℕ) (s : ℝ) (K : ℝ) : ℝ :=
  if s < (d : ℝ) / 2 then 1 else if s = (d : ℝ) / 2 then Real.log (Real.exp 1 * K) else K ^ (2 - (d : ℝ) / s)

theorem deltaN_eq_gFun (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : 1 ≤ N) :
    deltaN d s N = (N : ℝ)⁻¹ * gFun d s N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold deltaN gFun
  by_cases h1 : s < (d : ℝ) / 2
  · simp [h1]
  · by_cases h2 : s = (d : ℝ) / 2
    · simp [h2]
    · simp only [h1, h2, if_false]
      rw [show (2 : ℝ) - d / s = 1 + (1 - d / s) by ring, Real.rpow_add hN0, Real.rpow_one]
      field_simp

theorem one_le_gFun (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ gFun d s K := by
  unfold gFun
  have hK0 : 0 < K := by linarith
  split_ifs with h1 h2
  · exact le_rfl
  · have : Real.exp 1 ≤ Real.exp 1 * K := by nlinarith [Real.exp_pos 1]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  · have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
    have hs : 0 < s := by
      have : (0 : ℝ) < d / 2 := by
        have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        positivity
      linarith
    exact Real.one_le_rpow hK (by rw [sub_nonneg, div_le_iff₀ hs]; linarith)

theorem integral_one_rpow_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {K : ℝ} (hK : 1 ≤ K) :
    (s < (d : ℝ) / 2 → ∫ t in (1 : ℝ)..K, t ^ (1 - pOf d s) ≤ 1 / (pOf d s - 2)) ∧
    (s = (d : ℝ) / 2 → ∫ t in (1 : ℝ)..K, t ^ (1 - pOf d s) = Real.log K) ∧
    ((d : ℝ) / 2 < s → ∫ t in (1 : ℝ)..K, t ^ (1 - pOf d s) ≤ K ^ (2 - pOf d s) / (2 - pOf d s)) := by
  have hK0 : 0 < K := by linarith
  have hcases := pOf_cases hd hs0 hsd
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hp : 2 < pOf d s := by
      rcases hcases with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h2
      · linarith
      · linarith
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.mem_uIcc]; push Not; constructor <;> intro h <;> linarith⟩)]
    have : 1 - pOf d s + 1 = 2 - pOf d s := by ring
    rw [this]
    have h1 : (1 : ℝ) ^ (2 - pOf d s) = 1 := Real.one_rpow _
    rw [h1]
    have h2 : 0 < K ^ (2 - pOf d s) := Real.rpow_pos_of_pos hK0 _
    have e : (K ^ (2 - pOf d s) - 1) / (2 - pOf d s) = (1 - K ^ (2 - pOf d s)) / (pOf d s - 2) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · have hp : pOf d s = 2 := by
      rcases hcases with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
      · linarith
      · exact h2
      · linarith
    rw [hp, show (1 : ℝ) - 2 = -1 by norm_num]
    simp_rw [Real.rpow_neg_one]
    rw [integral_inv_of_pos one_pos hK0, div_one]
  · have hp : pOf d s < 2 := by
      rcases hcases with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, h3⟩
      · linarith
      · linarith
      · exact h3
    have hp1 := one_lt_pOf_aux hd hs0 hsd
    rw [integral_rpow (Or.inl (by linarith))]
    have : 1 - pOf d s + 1 = 2 - pOf d s := by ring
    rw [this]
    have h1 : (1 : ℝ) ^ (2 - pOf d s) = 1 := Real.one_rpow _
    rw [h1]
    have : 0 < 2 - pOf d s := by linarith
    rw [div_le_div_iff_of_pos_right this]
    linarith

theorem second_moment_gFun (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {K0 : ℝ} (hK0 : 0 < K0) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ K : ℝ, 1 ≤ K →
      1 + 2 * K0 * ∫ t in (1 : ℝ)..K, t ^ (1 - pOf d s) ≤ c₁ * gFun d s K := by
  have hcases := pOf_cases hd hs0 hsd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · refine ⟨1 + 2 * K0 / (pOf d s - 2), by have : 0 < pOf d s - 2 := by linarith
                                           positivity, fun K hK => ?_⟩
    have hI := (integral_one_rpow_le hd hs0 hsd hK).1 h1
    have hg : gFun d s K = 1 := by unfold gFun; simp [h1]
    rw [hg, mul_one]
    have : 0 < pOf d s - 2 := by linarith
    calc 1 + 2 * K0 * ∫ t in (1 : ℝ)..K, t ^ (1 - pOf d s) ≤ 1 + 2 * K0 * (1 / (pOf d s - 2)) := by gcongr
      _ = 1 + 2 * K0 / (pOf d s - 2) := by ring
  · refine ⟨1 + 2 * K0, by positivity, fun K hK => ?_⟩
    have hI := (integral_one_rpow_le hd hs0 hsd hK).2.1 h1
    have hg : gFun d s K = Real.log (Real.exp 1 * K) := by
      unfold gFun; simp [h1]
    have hK0 : 0 < K := by linarith
    rw [hg, hI, Real.log_mul (Real.exp_pos 1).ne' hK0.ne', Real.log_exp]
    have : 0 ≤ Real.log K := Real.log_nonneg hK
    nlinarith
  · refine ⟨1 + 2 * K0 / (2 - pOf d s), by have : 0 < 2 - pOf d s := by linarith
                                           positivity, fun K hK => ?_⟩
    have hI := (integral_one_rpow_le hd hs0 hsd hK).2.2 (by linarith)
    have hs : 0 < s := by linarith
    have hg : gFun d s K = K ^ (2 - pOf d s) := by
      unfold gFun
      have h4 : ¬ s < (d : ℝ) / 2 := by linarith
      have h5 : s ≠ (d : ℝ) / 2 := by linarith
      simp [h4, h5, h2]
    rw [hg]
    have hKp : 1 ≤ K ^ (2 - pOf d s) := Real.one_le_rpow hK (by linarith)
    have : 0 < 2 - pOf d s := by linarith
    calc 1 + 2 * K0 * ∫ t in (1 : ℝ)..K, t ^ (1 - pOf d s)
        ≤ 1 + 2 * K0 * (K ^ (2 - pOf d s) / (2 - pOf d s)) := by gcongr
      _ ≤ (1 + 2 * K0 / (2 - pOf d s)) * K ^ (2 - pOf d s) := by
        have : 2 * K0 * (K ^ (2 - pOf d s) / (2 - pOf d s)) = 2 * K0 / (2 - pOf d s) * K ^ (2 - pOf d s) := by
          ring
        rw [this]
        nlinarith

theorem gFun_mul_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ K : ℝ, 1 ≤ K → 1 ≤ c * K → gFun d s (c * K) ≤ c' * gFun d s K := by
  by_cases h1 : s < (d : ℝ) / 2
  · refine ⟨1, one_pos, fun K hK hcK => ?_⟩
    unfold gFun; simp [h1]
  · by_cases h2 : s = (d : ℝ) / 2
    · refine ⟨1 + |Real.log c|, by positivity, fun K hK hcK => ?_⟩
      have hg : ∀ K', gFun d s K' = Real.log (Real.exp 1 * K') := fun K' => by unfold gFun; simp [h2]
      rw [hg, hg]
      have hK0 : 0 < K := by linarith
      have e : Real.log (Real.exp 1 * (c * K)) = Real.log (Real.exp 1 * K) + Real.log c := by
        rw [show Real.exp 1 * (c * K) = (Real.exp 1 * K) * c by ring,
          Real.log_mul (by positivity) hc.ne']
      have h3 : 1 ≤ Real.log (Real.exp 1 * K) := by
        rw [Real.log_mul (Real.exp_pos 1).ne' hK0.ne', Real.log_exp]
        linarith [Real.log_nonneg hK]
      rw [e]
      nlinarith [le_abs_self (Real.log c), abs_nonneg (Real.log c)]
    · have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
      refine ⟨c ^ (2 - (d : ℝ) / s), by positivity, fun K hK hcK => ?_⟩
      have hg : ∀ K', gFun d s K' = K' ^ (2 - (d : ℝ) / s) := fun K' => by unfold gFun; simp [h1, h2]
      rw [hg, hg, Real.mul_rpow hc.le (by linarith)]

/-- `K^{1-p} ≤ K⁻¹ g(K)`. -/
theorem rpow_one_sub_le_gFun (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {K : ℝ} (hK : 1 ≤ K) :
    K ^ (1 - pOf d s) ≤ K⁻¹ * gFun d s K := by
  have hK0 : 0 < K := by linarith
  have hcases := pOf_cases hd hs0 hsd
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · have hg : gFun d s K = 1 := by unfold gFun; simp [h1]
    rw [hg, mul_one, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  · have hg : gFun d s K = Real.log (Real.exp 1 * K) := by unfold gFun; simp [h1]
    rw [hg, h2, Real.log_mul (Real.exp_pos 1).ne' hK0.ne', Real.log_exp]
    norm_num
    rw [Real.rpow_neg_one]
    have : 0 ≤ Real.log K := Real.log_nonneg hK
    have : K⁻¹ * (1 + Real.log K) = K⁻¹ + K⁻¹ * Real.log K := by ring
    have h4 : 0 ≤ K⁻¹ * Real.log K := by positivity
    linarith
  · have hs : 0 < s := by
      have : (0 : ℝ) < d / 2 := by
        have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        positivity
      linarith
    have hg : gFun d s K = K ^ (2 - (d : ℝ) / s) := by
      unfold gFun
      have h4 : ¬ s < (d : ℝ) / 2 := by linarith
      have h5 : s ≠ (d : ℝ) / 2 := by linarith
      simp [h4, h5]
    rw [hg, ← h2, ← Real.rpow_neg_one, ← Real.rpow_add hK0]
    exact le_of_eq (by congr 1; ring)

end Rates

section Conv

variable {d : ℕ}

theorem enorm_sq_add_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  have e : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rw [e] at h
  simpa [ENNReal.rpow_two] using h

/-- **`L²` convolution estimate** (`A:eq:convolution` in `ℝ≥0∞` form): splitting the kernel at the
level `K` (`q = (q - K)₊ + min(q, K)`), Young's inequality gives
`‖q * w‖₂² ≤ 2 ‖(q-K)₊‖₁² ‖w‖₂² + 2 ‖w‖₁² ‖min(q,K)‖₂²`. -/
theorem conv_sq_le {q w : Torus d → ℝ} (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hw : Measurable w)
    {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ x, ‖ResponseAux.cv q w x‖ₑ ^ 2 ≤
      2 * (((∫⁻ y, ENNReal.ofReal (q y - K)) ^ 2 * ∫⁻ y, ‖w y‖ₑ ^ 2) +
        ((∫⁻ y, ‖w y‖ₑ) ^ 2 * ∫⁻ y, ENNReal.ofReal (min (q y) K ^ 2))) := by
  set q1 : Torus d → ℝ := fun z => max (q z - K) 0 with hq1
  set q2 : Torus d → ℝ := fun z => min (q z) K with hq2
  have hq1m : Measurable q1 := (hq.sub_const K).max measurable_const
  have hq2m : Measurable q2 := hq.min measurable_const
  have hq10 : ∀ z, 0 ≤ q1 z := fun z => le_max_right _ _
  have hq20 : ∀ z, 0 ≤ q2 z := fun z => le_min (hq0 z) hK
  have hsplit : ∀ z, q z = q1 z + q2 z := by
    intro z
    simp only [hq1, hq2]
    rcases le_total (q z) K with h | h
    · rw [max_eq_right (by linarith), min_eq_left h]; ring
    · rw [max_eq_left (by linarith), min_eq_right h]; ring
  have hen1 : ∀ z, ‖q1 z‖ₑ = ENNReal.ofReal (q z - K) := by
    intro z
    rw [Real.enorm_of_nonneg (hq10 z), hq1]
    simp only
    rw [ENNReal.ofReal_max]; simp
  have hen2 : ∀ z, ‖q2 z‖ₑ ^ 2 = ENNReal.ofReal (min (q z) K ^ 2) := by
    intro z
    rw [Real.enorm_of_nonneg (hq20 z), ← ENNReal.ofReal_pow (hq20 z)]
  have hpt : ∀ x, ‖ResponseAux.cv q w x‖ₑ ≤
      (∫⁻ y, ‖q1 (x - y)‖ₑ * ‖w y‖ₑ) + ∫⁻ y, ‖q2 (x - y)‖ₑ * ‖w y‖ₑ := by
    intro x
    have h1 : ‖ResponseAux.cv q w x‖ₑ ≤ ∫⁻ y, ‖q (x - y)‖ₑ * ‖w y‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp [enorm_mul, ResponseAux.cv]
    refine h1.trans (le_of_eq ?_)
    rw [← lintegral_add_left]
    · refine lintegral_congr fun y => ?_
      rw [← add_mul]
      congr 1
      rw [hsplit (x - y), Real.enorm_of_nonneg (add_nonneg (hq10 _) (hq20 _)),
        ENNReal.ofReal_add (hq10 _) (hq20 _), Real.enorm_of_nonneg (hq10 _),
        Real.enorm_of_nonneg (hq20 _)]
    · exact ((hq1m.comp (measurable_const.sub measurable_id)).enorm).mul hw.enorm
  have hE1 := ResponseAux.young_lintegral q1 w hq1m hw
  have hE2 : ∫⁻ x, (∫⁻ y, ‖q2 (x - y)‖ₑ * ‖w y‖ₑ) ^ 2 ≤ (∫⁻ y, ‖w y‖ₑ) ^ 2 * ∫⁻ y, ‖q2 y‖ₑ ^ 2 := by
    have := ResponseAux.young_lintegral w q2 hw hq2m
    refine le_trans (le_of_eq ?_) this
    refine lintegral_congr fun x => ?_
    congr 1
    -- commute the convolution
    have := ResponseAux.lintegral_sub_left (fun u => ‖w u‖ₑ * ‖q2 (x - u)‖ₑ) x
    simp only [sub_sub_cancel] at this
    rw [this]
    refine lintegral_congr fun y => ?_
    rw [mul_comm]
  calc ∫⁻ x, ‖ResponseAux.cv q w x‖ₑ ^ 2
      ≤ ∫⁻ x, 2 * (((∫⁻ y, ‖q1 (x - y)‖ₑ * ‖w y‖ₑ) ^ 2) + ((∫⁻ y, ‖q2 (x - y)‖ₑ * ‖w y‖ₑ) ^ 2)) :=
        lintegral_mono fun x => (pow_le_pow_left' (hpt x) 2).trans (enorm_sq_add_le _ _)
    _ = 2 * ((∫⁻ x, (∫⁻ y, ‖q1 (x - y)‖ₑ * ‖w y‖ₑ) ^ 2) + (∫⁻ x, (∫⁻ y, ‖q2 (x - y)‖ₑ * ‖w y‖ₑ) ^ 2)) := by
        have hm1 : Measurable fun x : Torus d => (∫⁻ y, ‖q1 (x - y)‖ₑ * ‖w y‖ₑ) ^ 2 := by
          refine Measurable.pow_const ?_ 2
          exact Measurable.lintegral_prod_right' (f := fun p : Torus d × Torus d =>
            ‖q1 (p.1 - p.2)‖ₑ * ‖w p.2‖ₑ)
            (((hq1m.comp (measurable_fst.sub measurable_snd)).enorm).mul (hw.comp measurable_snd).enorm)
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hm1]
    _ ≤ 2 * (((∫⁻ y, ENNReal.ofReal (q y - K)) ^ 2 * ∫⁻ y, ‖w y‖ₑ ^ 2) +
          ((∫⁻ y, ‖w y‖ₑ) ^ 2 * ∫⁻ y, ENNReal.ofReal (min (q y) K ^ 2))) := by
        gcongr
        · simpa only [hen1] using hE1
        · simpa only [hen2] using hE2

end Conv

section Absorb

variable {d : ℕ}

theorem mul_log_ge {θ C : ℝ} (hθ : 0 < θ) (hC : 1 ≤ C) (hθC : θ ≤ C) :
    (θ - 1) ^ 2 / C ≤ (θ - 1) * Real.log θ := by
  have hC0 : 0 < C := by linarith
  rcases le_total 1 θ with h | h
  · -- θ ≥ 1: log θ ≥ (θ-1)/θ
    have h1 : (θ - 1) / θ ≤ Real.log θ := by
      have := Real.one_sub_inv_le_log_of_pos hθ
      calc (θ - 1) / θ = 1 - θ⁻¹ := by field_simp
        _ ≤ _ := this
    have h2 : (θ - 1) / C ≤ (θ - 1) / θ := div_le_div_of_nonneg_left (by linarith) hθ hθC
    calc (θ - 1) ^ 2 / C = (θ - 1) * ((θ - 1) / C) := by ring
      _ ≤ (θ - 1) * Real.log θ := mul_le_mul_of_nonneg_left (h2.trans h1) (by linarith)
  · have h1 : Real.log θ ≤ θ - 1 := Real.log_le_sub_one_of_pos hθ
    have h2 : (θ - 1) ^ 2 / C ≤ (θ - 1) ^ 2 := div_le_self (sq_nonneg _) hC
    calc (θ - 1) ^ 2 / C ≤ (θ - 1) ^ 2 := h2
      _ = (θ - 1) * (θ - 1) := by ring
      _ ≤ (θ - 1) * Real.log θ := mul_le_mul_of_nonpos_left h1 (by linarith)

theorem integral_mul_self_eq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 ν) : ∫ x, f x * f x ∂ν = (eLpNorm f 2 ν).toReal ^ 2 := by
  have h := real_inner_self_eq_norm_sq (hf.toLp f)
  rw [L2.inner_def, Lp.norm_toLp] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x h1
  rw [h1]
  simp [sq]

theorem integral_mul_le_eLpNorm {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ∫ x, f x * g x ∂ν ≤ (eLpNorm f 2 ν).toReal * (eLpNorm g 2 ν).toReal := by
  have h := real_inner_le_norm (hf.toLp f) (hg.toLp g)
  rw [L2.inner_def, Lp.norm_toLp, Lp.norm_toLp] at h
  refine le_trans (le_of_eq ?_) h
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- **Absorption** (`A:eq:marginal-absorption`): if `log θ + β K̃_k(θ - 1) = Φ + c` with `θ ∈ (0, C]`,
`∫ θ dμ = 1` and `k` positive definite, then `‖θ - 1‖_{L²(μ)} ≤ C ‖Φ‖_{L²(μ)}`. -/
theorem absorption {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ)
    {k : Torus d → ℝ} (hk : Measurable k) (hki : Integrable k)
    (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (k x : ℂ) = (ĝ n : ℂ))
    {β : ℝ} (hβ : 0 ≤ β) {θ : Torus d → ℝ} (hθm : Measurable θ) (hθ0 : ∀ x, 0 < θ x)
    {C : ℝ} (hC : 1 ≤ C) (hθC : ∀ᵐ x ∂(withDensityReal ρ), θ x ≤ C) (hθ1 : ∫ x, θ x ∂(withDensityReal ρ) = 1)
    {Φ : Torus d → ℝ} (hΦ : MemLp Φ 2 (withDensityReal ρ)) {c : ℝ}
    (heq : ∀ x, Real.log (θ x) + β * ResponseAux.Kt k (withDensityReal ρ) (fun y => θ y - 1) x = Φ x + c) :
    eLpNorm (fun x => θ x - 1) 2 (withDensityReal ρ) ≤
      ENNReal.ofReal C * eLpNorm Φ 2 (withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  set z : Torus d → ℝ := fun x => θ x - 1 with hz
  have hzm : Measurable z := hθm.sub_const 1
  have hzb : ∀ᵐ x ∂μ, ‖z x‖ ≤ C := hθC.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_le]
    have := hθ0 x
    constructor <;> simp only [hz] <;> linarith
  have hz2 : MemLp z 2 μ := MemLp.of_bound hzm.aestronglyMeasurable C hzb
  have hz1 : Integrable z μ := hz2.integrable one_le_two
  have hzint : ∫ x, z x ∂μ = 0 := by
    simp only [hz]
    rw [integral_sub (hz1.add (integrable_const 1) |>.congr (Filter.Eventually.of_forall fun x => by simp [hz]))
      (integrable_const _), hθ1]
    simp
  set Kz := ResponseAux.Kt k μ z with hKz
  obtain ⟨hKz2, -⟩ := ResponseAux.memLp_Kt hρ hΛ hk hki hz2
  have hlog : ∀ x, Real.log (θ x) = Φ x + c - β * Kz x := fun x => by
    have := heq x; simp only [hz, hKz] at this ⊢; linarith
  have hnn := ResponseAux.Kt_form_nonneg hρ hΛ hk hki ĝ hĝ hcoef hz2
  have i1 : Integrable (fun x => z x * Φ x) μ := MemLp.integrable_mul hz2 hΦ
  have i2 : Integrable (fun x => z x * Kz x) μ := MemLp.integrable_mul hz2 hKz2
  have i3 : Integrable (fun x => z x * c) μ := hz1.mul_const c
  have hid : ∀ x, z x * Real.log (θ x) = z x * Φ x + z x * c - β * (z x * Kz x) := fun x => by
    rw [hlog x]; ring
  have hi : Integrable (fun x => z x * Real.log (θ x)) μ := by
    have := (i1.add i3).sub (i2.const_mul β)
    exact this.congr (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply, Pi.sub_apply]; rw [hid x])
  have hsq : Integrable (fun x => (z x) ^ 2 / C) μ := (hz2.integrable_sq.div_const C)
  have hmono := integral_mono_ae hsq hi (hθC.mono fun x hx => mul_log_ge (hθ0 x) hC hx)
  have hrhs : ∫ x, z x * Real.log (θ x) ∂μ = ∫ x, z x * Φ x ∂μ - β * ∫ x, Kz x * z x ∂μ := by
    simp_rw [hid]
    have i13 : Integrable (fun x => z x * Φ x + z x * c) μ := i1.add i3
    have i2' : Integrable (fun x => β * (z x * Kz x)) μ := i2.const_mul β
    rw [integral_sub i13 i2', integral_add i1 i3, integral_mul_const, hzint,
      integral_const_mul]
    simp_rw [mul_comm (Kz _) (z _)]
    ring
  have hK0 : 0 ≤ β * ∫ x, Kz x * z x ∂μ := mul_nonneg hβ hnn
  set a := (eLpNorm z 2 μ).toReal with ha
  set b := (eLpNorm Φ 2 μ).toReal with hb
  have hzz : ∫ x, z x * z x ∂μ = a ^ 2 := integral_mul_self_eq hz2
  have hCS : ∫ x, z x * Φ x ∂μ ≤ a * b := integral_mul_le_eLpNorm hz2 hΦ
  have hlhs : ∫ x, (z x) ^ 2 / C ∂μ = a ^ 2 / C := by
    rw [integral_div]
    congr 1
    rw [← hzz]; congr 1; funext x; ring
  have key : a ^ 2 / C ≤ a * b := by
    calc a ^ 2 / C = ∫ x, (z x) ^ 2 / C ∂μ := hlhs.symm
      _ ≤ _ := hmono
      _ = _ := hrhs
      _ ≤ ∫ x, z x * Φ x ∂μ := by linarith
      _ ≤ a * b := hCS
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hC0 : 0 < C := by linarith
  have hab : a ≤ C * b := by
    rcases ha0.eq_or_lt with h | h
    · rw [← h]; positivity
    · have : a / C ≤ b := by
        have h2 : a ^ 2 / C / a ≤ a * b / a := div_le_div_of_nonneg_right key h.le
        have e1 : a ^ 2 / C / a = a / C := by field_simp
        have e2 : a * b / a = b := by field_simp
        rwa [e1, e2] at h2
      rw [div_le_iff₀ hC0] at this
      linarith
  have hzfin : eLpNorm z 2 μ ≠ ⊤ := hz2.eLpNorm_ne_top
  have hΦfin : eLpNorm Φ 2 μ ≠ ⊤ := hΦ.eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hzfin, ← ENNReal.ofReal_toReal hΦfin, ← ENNReal.ofReal_mul hC0.le]
  exact ENNReal.ofReal_le_ofReal hab

end Absorb

section TorusInt

variable {d : ℕ}

/-- Integral of a translated nonnegative kernel against a measure dominated by `Cν · ρ dx`. -/
theorem integral_kernel_le {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ)
    {ν : Measure (Torus d)} {Cν : ℝ}
    (hν : ν ≤ ENNReal.ofReal Cν • withDensityReal ρ) (hCν : 0 ≤ Cν)
    {h : Torus d → ℝ} (hm : Measurable h) (h0 : ∀ z, 0 ≤ h z) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∫⁻ z, ENNReal.ofReal (h z) ≤ ENNReal.ofReal c) (x : Torus d) :
    ∫ y, h (x - y) ∂ν ≤ Cν * (Λ * c) := by
  have hcm : Measurable fun y : Torus d => h (x - y) := hm.comp (measurable_const.sub measurable_id)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => h0 _) hcm.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc ∫⁻ y, ENNReal.ofReal (h (x - y)) ∂ν
      ≤ ∫⁻ y, ENNReal.ofReal (h (x - y)) ∂(ENNReal.ofReal Cν • withDensityReal ρ) :=
        lintegral_mono' hν le_rfl
    _ = ENNReal.ofReal Cν * ∫⁻ y, ENNReal.ofReal (h (x - y)) ∂(withDensityReal ρ) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal Cν * (ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (h z)) := by
        gcongr
        exact KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (h z)) x
    _ ≤ ENNReal.ofReal Cν * (ENNReal.ofReal Λ * ENNReal.ofReal c) := by gcongr
    _ = ENNReal.ofReal (Cν * (Λ * c)) := by
        rw [← ENNReal.ofReal_mul hΛ0, ← ENNReal.ofReal_mul hCν]


theorem cavD_torus (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    {q : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqe : ∀ z, q (-z) = q z)
    {c : ℝ} (hc0 : 0 ≤ c) (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c)
    {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s))))
    {β : ℝ} (hβ : 0 < β) {Cν : ℝ} (hCν : 1 ≤ Cν)  :
    ∃ (CD : ℝ) (N₁ : ℕ), 0 ≤ CD ∧ ∀ (ρ : Torus d → ℝ), IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ (V : WeakPotential (withDensityReal ρ)),
      (∀ x y, V.q x y = q (x - y)) → Real.exp (V.M + V.M' + β * V.γ) ≤ Cν → weakKappa V β ≤ 1 / 2 →
      ∀ (N n : ℕ) [NeZero n], N₁ ≤ N → n ≤ N → ∀ x : Torus d,
        0 ≤ Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ∧
        Real.log (cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(cavMarg V (β / N) n) ≤ CD * deltaN d s N := by
  have hp := one_lt_pOf hd hs0 hsd
  set p := pOf d s with hpdef
  obtain ⟨c₁, hc₁, hR2⟩ := second_moment_gFun hd hs0 hsd hK0
  obtain ⟨c', hc', hscale⟩ := gFun_mul_le hd hs0 hsd (c := 1 / β) (by positivity)
  have hΛ0 : 0 ≤ Λ := by linarith
  set mb : ℝ := β * (Cν * (Λ * c)) with hmb
  set CD : ℝ := Real.exp mb * β ^ 2 * Cν * Λ * c₁ * c' +
      β * Cν * Λ * (K0 * (p / (p - 1))) * β ^ (p - 1) with hCD
  refine ⟨CD, ⌈β⌉₊ + 1, by positivity, ?_⟩
  intro ρ hρ hΛ V hVq hVC hκ N n _ hN hn x
  haveI := isProb_withDensityReal hρ
  have hNβ : β ≤ N := by
    have : (⌈β⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith [Nat.le_ceil β]
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  set lam : ℝ := β / N with hlam
  have hlampos : 0 < lam := by positivity
  have hVqx : ∀ y, V.q y x = q (x - y) := fun y => by rw [hVq, ← hqe, neg_sub]
  have hν : cavMarg V lam n ≤ ENNReal.ofReal Cν • withDensityReal ρ := by
    have h1 := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simpa using hn)
      (fun e : Empty => e.elim) 0
    refine h1.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  have hCν0 : 0 ≤ Cν := by linarith
  have hI1 : ∫ y, V.q y x ∂(cavMarg V lam n) ≤ Cν * (Λ * c) := by
    simp_rw [hVqx]
    exact integral_kernel_le hΛ hΛ0 hν hCν0 hqm hq0 hc0 hqc x
  have hI0 : 0 ≤ ∫ y, V.q y x ∂(cavMarg V lam n) := integral_nonneg fun y => V.q_nonneg _ _
  have hlamn : lam * n ≤ β := by
    have : (n : ℝ) ≤ N := by exact_mod_cast hn
    calc lam * n ≤ lam * N := by gcongr
      _ = β := by rw [hlam]; field_simp
  have hlamn' : (n : ℝ) * lam ≤ β := by linarith [hlamn, mul_comm (n : ℝ) lam]
  have hm : lam * n * ∫ y, V.q y x ∂(cavMarg V lam n) ≤ mb := by
    calc lam * n * ∫ y, V.q y x ∂(cavMarg V lam n) ≤ β * ∫ y, V.q y x ∂(cavMarg V lam n) := by gcongr
      _ ≤ β * (Cν * (Λ * c)) := by gcongr
  obtain ⟨h1, h2⟩ := cavD_bounds V hβ.le hN0 hn hκ x hm
  refine ⟨h1, h2.trans ?_⟩
  set ν := cavMarg V lam n with hνdef
  set K : ℝ := N / β with hK
  have hKpos : 0 < K := by positivity
  have hK1 : 1 ≤ K := by rw [hK, le_div_iff₀ hβ]; linarith
  have hKlam : lam * K = 1 := by rw [hlam, hK]; field_simp
  -- the second-moment term
  have hA : ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν ≤ Cν * (Λ * (lam ^ 2 * (c₁ * gFun d s K))) := by
    simp_rw [hVqx]
    refine integral_kernel_le (h := fun z => (min (lam * q z) 1) ^ 2) hΛ hΛ0 hν hCν0
      ((hqm.const_mul lam).min measurable_const |>.pow_const 2) (fun z => sq_nonneg _)
      (by have := hR2 K hK1; have := one_le_gFun hd hs0 hsd hK1; positivity) ?_ x
    have e : ∀ z, ENNReal.ofReal ((min (lam * q z) 1) ^ 2) =
        ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (min (q z) K ^ 2) := by
      intro z
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : min (lam * q z) 1 = lam * min (q z) K := by
        rw [mul_min_of_nonneg _ _ hlampos.le, hKlam]
      rw [this]; ring
    simp_rw [e]
    rw [lintegral_const_mul (ENNReal.ofReal (lam ^ 2)) (f := fun z => ENNReal.ofReal (min (q z) K ^ 2))
      (ENNReal.measurable_ofReal.comp ((hqm.min measurable_const).pow_const 2))]
    calc ENNReal.ofReal (lam ^ 2) * ∫⁻ z, ENNReal.ofReal (min (q z) K ^ 2)
        ≤ ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (1 + 2 * K0 * ∫ t in (1 : ℝ)..K, t ^ (1 - p)) := by
          gcongr
          exact lintegral_minsq_le hqm hq0 hK1 hp hK0 hw
      _ ≤ ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (c₁ * gFun d s K) := by
          gcongr
          exact hR2 K hK1
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  -- the tail term
  set T : ℝ := K0 * K ^ (1 - p) * (p / (p - 1)) with hT
  have hT0 : 0 ≤ T := by
    have : 0 < p - 1 := by linarith
    positivity
  have hB : ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ Cν * (Λ * (lam * T)) := by
    simp_rw [hVqx]
    refine integral_kernel_le (h := fun z => max (lam * q z - 1) 0) hΛ hΛ0 hν hCν0
      (((hqm.const_mul lam).sub_const 1).max measurable_const) (fun z => le_max_right _ _)
      (by positivity) ?_ x
    have e : ∀ z, ENNReal.ofReal (max (lam * q z - 1) 0) = ENNReal.ofReal lam * ENNReal.ofReal (q z - K) := by
      intro z
      rw [← ENNReal.ofReal_mul hlampos.le, ENNReal.ofReal_max]
      simp only [ENNReal.ofReal_zero]
      rw [max_eq_left (by simp)]
      congr 1
      rw [mul_sub, hKlam]
    simp_rw [e]
    rw [lintegral_const_mul (ENNReal.ofReal lam) (f := fun z => ENNReal.ofReal (q z - K))
      (ENNReal.measurable_ofReal.comp (hqm.sub_const K))]
    calc ENNReal.ofReal lam * ∫⁻ z, ENNReal.ofReal (q z - K)
        ≤ ENNReal.ofReal lam * ENNReal.ofReal T := by
          gcongr
          exact lintegral_tail_le hqm hq0 hKpos hp hK0 hw
      _ = _ := by rw [← ENNReal.ofReal_mul hlampos.le]
  -- assemble
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hG := deltaN_eq_gFun hd hs0 hsd hN1
  have hgN1 := one_le_gFun hd hs0 hsd hN1'
  have hgK : gFun d s K ≤ c' * gFun d s N := by
    have hK' : K = 1 / β * N := by rw [hK]; field_simp
    rw [hK']
    exact hscale N hN1' (by rw [← hK']; exact hK1)
  have hKr : K ^ (1 - p) ≤ β ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N) := by
    have h1 := rpow_one_sub_le_gFun hd hs0 hsd hN1'
    have e : K ^ (1 - p) = (N : ℝ) ^ (1 - p) * β ^ (p - 1) := by
      rw [hK, Real.div_rpow hNpos.le hβ.le, div_eq_mul_inv, ← Real.rpow_neg hβ.le]
      congr 2; ring
    rw [e, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hgK0 : 0 ≤ gFun d s K := by have := one_le_gFun hd hs0 hsd hK1; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE1' : (n : ℝ) * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν ≤ β * lam * Cν * Λ * c₁ * gFun d s K := by
    have h0 : (0 : ℝ) ≤ lam * Cν * Λ * c₁ * gFun d s K := by positivity
    calc (n : ℝ) * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν
        ≤ n * (Cν * (Λ * (lam ^ 2 * (c₁ * gFun d s K)))) := mul_le_mul_of_nonneg_left hA hn0
      _ = (n * lam) * (lam * Cν * Λ * c₁ * gFun d s K) := by ring
      _ ≤ β * (lam * Cν * Λ * c₁ * gFun d s K) := mul_le_mul_of_nonneg_right hlamn' h0
      _ = _ := by ring
  have hE1 : Real.exp mb * (n * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν) ≤
      Real.exp mb * (β * lam * Cν * Λ * c₁ * gFun d s K) :=
    mul_le_mul_of_nonneg_left hE1' (Real.exp_pos _).le
  have hE2 : (n : ℝ) * ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ β * Cν * Λ * T := by
    have h0 : (0 : ℝ) ≤ Cν * Λ * T := by positivity
    calc (n : ℝ) * ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ n * (Cν * (Λ * (lam * T))) :=
          mul_le_mul_of_nonneg_left hB hn0
      _ = (n * lam) * (Cν * Λ * T) := by ring
      _ ≤ β * (Cν * Λ * T) := mul_le_mul_of_nonneg_right hlamn' h0
      _ = _ := by ring
  have hNi : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
  have hlam' : lam = β * (N : ℝ)⁻¹ := by rw [hlam]; ring
  calc Real.exp mb * (n * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν) + n * ∫ y, max (lam * V.q y x - 1) 0 ∂ν
      ≤ Real.exp mb * (β * lam * Cν * Λ * c₁ * gFun d s K) + β * Cν * Λ * T := add_le_add hE1 hE2
    _ ≤ Real.exp mb * (β * lam * Cν * Λ * c₁ * (c' * gFun d s N)) +
          β * Cν * Λ * (K0 * (β ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N)) * (p / (p - 1))) := by
        have hp1 : 0 < p - 1 := by linarith
        have hexpp : 0 < Real.exp mb := Real.exp_pos _
        have h1 : Real.exp mb * (β * lam * Cν * Λ * c₁ * gFun d s K) ≤
            Real.exp mb * (β * lam * Cν * Λ * c₁ * (c' * gFun d s N)) := by
          refine mul_le_mul_of_nonneg_left ?_ hexpp.le
          have : 0 ≤ β * lam * Cν * Λ * c₁ := by positivity
          exact mul_le_mul_of_nonneg_left hgK this
        have h2 : β * Cν * Λ * T ≤
            β * Cν * Λ * (K0 * (β ^ (p - 1) * ((N : ℝ)⁻¹ * gFun d s N)) * (p / (p - 1))) := by
          have : 0 ≤ β * Cν * Λ := by positivity
          refine mul_le_mul_of_nonneg_left ?_ this
          simp only [hT]
          have : 0 ≤ p / (p - 1) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKr hK0.le) this
        exact add_le_add h1 h2
    _ = CD * deltaN d s N := by
        rw [hG, hCD, hlam']
        ring
end TorusInt

section Setting

variable {d M : ℕ} {μ : Measure (Torus d)} {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} [IsProbabilityMeasure μ]

/-- The weak potential of the calibrated reference with a one-body field `hh = t·Ξ`, `|hh| ≤ K`:
`φ = β q*μ + hh`, pair kernel `q(x - y)`, `M = βγ + K`, `M' = 0` (`∫ hh dμ = 0` for `hh = t·Ξ`). -/
def weakPotK (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 ≤ β) (t : EuclideanSpace ℝ (Fin M)) {K : ℝ}
    (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ K) : WeakPotential μ where
  φ := fun x => β * convMeasure q μ x + inner ℝ t (Xi μ Ψ x)
  q := fun x y => q (x - y)
  M := β * γ + K
  M' := 0
  γ := γ
  measurable_φ := (h.measurable_conv.const_mul β).add (measurable_const.inner h.measurable_Xi)
  measurable_q := h.q_meas.comp (measurable_fst.sub measurable_snd)
  q_nonneg := fun x y => h.q_nonneg _
  q_symm := fun x y => by rw [← h.q_even (x - y), neg_sub]
  γ_nonneg := h.gamma_nonneg
  φ_le := fun x => by
    have h1 : β * convMeasure q μ x ≤ β * γ := mul_le_mul_of_nonneg_left (h.conv_le x) hβ
    have h2 := (le_abs_self _).trans (ht x)
    linarith
  integrable_φ := by
    have hK : 0 ≤ K := (abs_nonneg _).trans (ht 0)
    refine integrable_of_abs_le ((h.measurable_conv.const_mul β).add (measurable_const.inner h.measurable_Xi))
      (β * γ + K) fun x => ?_
    have h1 : 0 ≤ β * convMeasure q μ x := mul_nonneg hβ (h.conv_nonneg x)
    have h1' : β * convMeasure q μ x ≤ β * γ := mul_le_mul_of_nonneg_left (h.conv_le x) hβ
    have h2 := ht x
    rw [abs_le] at h2 ⊢
    constructor <;> linarith [h2.1, h2.2]
  neg_le_integral_φ := by
    have hi1 : Integrable (fun x => β * convMeasure q μ x) μ :=
      integrable_of_abs_le (h.measurable_conv.const_mul β) (β * γ) fun x => by
        rw [abs_of_nonneg (mul_nonneg hβ (h.conv_nonneg x))]
        exact mul_le_mul_of_nonneg_left (h.conv_le x) hβ
    have hK : 0 ≤ K := (abs_nonneg _).trans (ht 0)
    have hi2 : Integrable (fun x => inner ℝ t (Xi μ Ψ x)) μ :=
      integrable_of_abs_le (measurable_const.inner h.measurable_Xi) K ht
    rw [integral_add hi1 hi2, integral_inner h.integrable_Xi t, h.integral_Xi]
    have : 0 ≤ ∫ x, β * convMeasure q μ x ∂μ :=
      integral_nonneg fun x => mul_nonneg hβ (h.conv_nonneg x)
    simpa using this
  integrable_q := h.q_int
  row_le := h.q_row

variable {β : ℝ} {N : ℕ}

theorem RN_eq_fieldLawK (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) {K : ℝ}
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ K) :
    RN q μ Ψ β N = fieldLaw (weakPotK h hβ (tN q μ Ψ β N) ht) (weakPotK h hβ (tN q μ Ψ β N) ht).φ
      (β / N) N := by
  rw [h.RN_eq_tilted hβ, fieldLaw_eq_tilted]
  · congr 1
    funext X
    simp only [E0, Yf, weakPotK, pairEnergy, Finset.sum_add_distrib]
    ring
  · have := h.integrable_exp_E0_Yf hβ N (tN q μ Ψ β N)
    convert this using 2 with X
    simp only [E0, Yf, weakPotK, pairEnergy, Finset.sum_add_distrib]
    ring_nf

/-- `|t_N · Ξ(x)| ≤ 4 β g_L(0)` for every `N ≥ 1`. -/
theorem abs_tN_inner_le (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 0 < N) (x : Torus d) :
    |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 4 * β * gL 0 := by
  haveI := h.isProb_R0 hβ.le N
  have h1 := h.tN_norm_le hβ hN
  have h2 : ‖∫ X, empXi μ Ψ X ∂(R0 q μ β N)‖ ≤ 2 * Real.sqrt (gL 0) := by
    have := norm_integral_le_of_norm_le_const (μ := R0 q μ β N) (f := empXi μ Ψ)
      (C := 2 * Real.sqrt (gL 0)) (Filter.Eventually.of_forall (h.norm_empXi_le hN))
    simpa using this
  calc |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ ‖tN q μ Ψ β N‖ * ‖Xi μ Ψ x‖ := abs_real_inner_le_norm _ _
    _ ≤ (β * (2 * Real.sqrt (gL 0))) * (2 * Real.sqrt (gL 0)) := by
        refine mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hβ.le)) (h.norm_Xi_le x)
          (norm_nonneg _) (by positivity)
    _ = 4 * β * (Real.sqrt (gL 0) ^ 2) := by ring
    _ = 4 * β * gL 0 := by rw [Real.sq_sqrt h.gL_zero_nonneg]

/-- **(i), measure form**: `π_N ≤ e^{M + βγ} μ` for all `N ≥ 1` (any bound `K` of the field `t_N·Ξ`). -/
theorem firstMarginal_RN_leK (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 1 ≤ N) {K : ℝ}
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ K) :
    firstMarginal (RN q μ Ψ β N) ≤
      ENNReal.ofReal (Real.exp ((β * γ + K) + 0 + β * γ)) • μ := by
  have hN0 : 0 < N := hN
  set V := weakPotK h hβ.le (tN q μ Ψ β N) ht with hV
  have hRN := RN_eq_fieldLawK h hβ.le ht (N := N)
  rw [← hV] at hRN
  have hm := marginal_le_smul (B := Empty) V hβ.le hN0 (n := N) (by simp) (fun e => e.elim) ⟨0, hN0⟩
  rw [pinnedLaw_empty] at hm
  unfold firstMarginal
  rw [dif_pos hN0, hRN]
  refine hm.trans (le_of_eq ?_)
  rfl

/-- **(i), measure form**: `π_N ≤ e^{M + βγ} μ` for all `N ≥ 1`. -/
theorem firstMarginal_RN_le (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) (hN : 1 ≤ N) :
    firstMarginal (RN q μ Ψ β N) ≤
      ENNReal.ofReal (Real.exp ((β * γ + 4 * β * gL 0) + 0 + β * γ)) • μ :=
  firstMarginal_RN_leK h hβ hN (abs_tN_inner_le h hβ (Nat.succ_le_iff.1 hN))

/-- `κ ≤ 1/2` for `V = weakPotK` with `K = 1`, from `KappaSmall`. -/
theorem weakKappa_weakPotK_le (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) {t : EuclideanSpace ℝ (Fin M)}
    (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β γ) :
    weakKappa (weakPotK h hβ t ht) β ≤ 1 / 2 := by
  have e : weakKappa (weakPotK h hβ t ht) β = 4 * Real.exp ((β * γ + 1) + 0 + β * γ) * (β * γ) := rfl
  rw [e]
  have : (β * γ + 1) + 0 + β * γ = 2 * (β * γ) + 1 := by ring
  rw [this]
  exact hκ

end Setting


section Main

variable {d : ℕ}

theorem reference_marginal_density_le (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 < β)
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∃ C : ℝ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 1 ≤ N →
      firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        ∀ᵐ x ∂(withDensityReal ρ),
          (firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)).rnDeriv
            (withDensityReal ρ) x ≤ ENNReal.ofReal C := by
  refine ⟨Real.exp ((β * (Λ * (weakSplit d s τ L).c) + 4 * β * (weakSplit d s τ L).gL 0) + 0 +
    β * (Λ * (weakSplit d s τ L).c)), fun ρ hρ hρΛ N hN => ?_⟩
  haveI := isProb_withDensityReal hρ
  have h := refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  have hle := firstMarginal_RN_le h hβ hN
  have hle' : firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ≤
      (withDensityReal ρ).withDensity (fun _ => ENNReal.ofReal (Real.exp ((β * (Λ * (weakSplit d s τ L).c) +
        4 * β * (weakSplit d s τ L).gL 0) + 0 + β * (Λ * (weakSplit d s τ L).c)))) := by
    rw [withDensity_const]; exact hle
  haveI : IsFiniteMeasure (firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)) := by
    refine ⟨lt_of_le_of_lt (hle' Set.univ) ?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  exact PoleCavityAux.rnDeriv_le_of_le_withDensity _ _ _ hle'

end Main

section Cavity

variable {d M : ℕ} {μ : Measure (Torus d)} {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} [IsProbabilityMeasure μ]
  {β : ℝ} {n : ℕ}

omit [IsProbabilityMeasure μ] in
theorem pinField_empty {E : Type*} [MeasurableSpace E] {μ : Measure E} (V : WeakPotential μ) (lam : ℝ)
    (a : Empty → E) : pinField V lam a = V.φ := by
  funext z; simp [pinField]

/-- The explicit one-point density `θ = Θ / ∫ Θ` of the first marginal (`n + 1` particles). -/
def theta (V : WeakPotential μ) (lam : ℝ) (n : ℕ) (x : Torus d) : ℝ :=
  cavTheta V lam n (fun e : Empty => e.elim) x / ∫ x', cavTheta V lam n (fun e : Empty => e.elim) x' ∂μ

theorem firstMarginal_RN_eq (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) {K : ℝ}
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) :
    firstMarginal (RN q μ Ψ β (n + 1)) =
      μ.withDensity (fun x => ENNReal.ofReal (theta (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht)
        (β / ((n + 1 : ℕ) : ℝ)) n x)) := by
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  have hRN := RN_eq_fieldLawK h hβ.le ht (N := n + 1)
  rw [← hV] at hRN
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
  unfold firstMarginal
  rw [dif_pos (Nat.succ_pos n), hRN, ← pinnedLaw_empty V _ _ (fun e : Empty => e.elim)]
  exact marginal_eq_normalized V hlam (fun e : Empty => e.elim) (n := n) 0

end Cavity

section Cavity2

variable {d M : ℕ} {μ : Measure (Torus d)} {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} [IsProbabilityMeasure μ]
  {β : ℝ} {n : ℕ}

theorem measurable_theta (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) :
    Measurable (theta V lam n) :=
  (measurable_cavTheta V hlam (fun e : Empty => e.elim) n).div_const _

theorem theta_pos (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (x : Torus d) :
    0 < theta V lam n x :=
  div_pos (cavTheta_pos V hlam _ n x) (integral_cavTheta_pos V hlam _ n)

theorem integral_theta (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) :
    ∫ x, theta V lam n x ∂μ = 1 := by
  unfold theta
  rw [integral_div]
  exact div_self (integral_cavTheta_pos V hlam _ n).ne'

theorem integrable_theta (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) :
    Integrable (theta V lam n) μ :=
  (integrable_cavTheta V hlam (fun e : Empty => e.elim) n).div_const _

/-- **The cavity equation** (pointwise): `log θ = φ + log u - log Z`. -/
theorem log_theta_eq (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (x : Torus d) :
    Real.log (theta V lam n x) = V.φ x + Real.log (cavU V lam n (fun e : Empty => e.elim) x) -
      Real.log (∫ x', cavTheta V lam n (fun e : Empty => e.elim) x' ∂μ) := by
  have hZ := integral_cavTheta_pos V hlam (fun e : Empty => e.elim) n
  have h1 := cavTheta_pos V hlam (fun e : Empty => e.elim) n x
  have e : cavTheta V lam n (fun e : Empty => e.elim) x = Real.exp (V.φ x) *
      cavU V lam n (fun e : Empty => e.elim) x := by
    unfold cavTheta; rw [pinField_empty]
  unfold theta
  rw [Real.log_div h1.ne' hZ.ne', e, Real.log_mul (Real.exp_pos _).ne' (cavU_pos V hlam _ n x).ne',
    Real.log_exp]


/-- `Ξ̄_N = ∫ Ξ dπ_N` (all one-coordinate marginals of `R_N` coincide). -/
theorem Xibar_eq_integral (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) {K : ℝ}
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) :
    Xibar q μ Ψ β (n + 1) = ∫ y, Xi μ Ψ y ∂(firstMarginal (RN q μ Ψ β (n + 1))) := by
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  have hRN := RN_eq_fieldLawK h hβ.le ht (N := n + 1)
  rw [← hV] at hRN
  haveI := h.isProb_RN hβ.le (N := n + 1)
  have hmarg : ∀ i : Fin (n + 1), (RN q μ Ψ β (n + 1)).map (fun X => X i) =
      firstMarginal (RN q μ Ψ β (n + 1)) := by
    intro i
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    rw [hRN]
    exact map_eval_eq_of_symm μ _ (measurable_fieldDensity V.measurable_φ V _ _)
      (fun σ y => fieldDensity_comp_perm V _ _ σ y) i ⟨0, Nat.succ_pos n⟩
  unfold Xibar empXi
  have hint : ∀ i : Fin (n + 1), Integrable (fun X : Config d (n + 1) => Xi μ Ψ (X i)) (RN q μ Ψ β (n + 1)) :=
    fun i => Integrable.of_bound (h.measurable_Xi.comp (measurable_pi_apply i)).aestronglyMeasurable
      (2 * Real.sqrt (gL 0)) (Filter.Eventually.of_forall fun X => h.norm_Xi_le _)
  rw [integral_smul, integral_finsetSum _ fun i _ => hint i]
  have h2 : ∀ i : Fin (n + 1), ∫ X : Config d (n + 1), Xi μ Ψ (X i) ∂(RN q μ Ψ β (n + 1)) =
      ∫ y, Xi μ Ψ y ∂(firstMarginal (RN q μ Ψ β (n + 1))) := by
    intro i
    rw [← hmarg i, integral_map (measurable_pi_apply i).aemeasurable h.measurable_Xi.aestronglyMeasurable]
  simp_rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (1 / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) = 1 := by field_simp
  rw [this, one_smul]


theorem gL_symm (h : RefHyp μ q gL Ψ γ) (x y : Torus d) : gL (x - y) = gL (y - x) := by
  rw [h.gL_eq, h.gL_eq, real_inner_comm]

theorem measurable_gL_sub (h : RefHyp μ q gL Ψ γ) (x : Torus d) : Measurable fun y => gL (x - y) := by
  have : (fun y => gL (x - y)) = fun y => inner ℝ (Ψ x) (Ψ y) := funext (h.gL_eq x)
  rw [this]; exact measurable_const.inner h.Ψ_meas

theorem abs_gL_le (h : RefHyp μ q gL Ψ γ) (z : Torus d) : |gL z| ≤ gL 0 := by
  have h1 := h.gL_eq z 0
  rw [sub_zero] at h1
  rw [h1]
  calc |inner ℝ (Ψ z) (Ψ 0)| ≤ ‖Ψ z‖ * ‖Ψ 0‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt (gL 0) * Real.sqrt (gL 0) :=
        mul_le_mul (h.norm_Ψ_le z) (h.norm_Ψ_le 0) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = gL 0 := Real.mul_self_sqrt h.gL_zero_nonneg

/-- **Calibration identity** (`A:eq:calibration-potential`): `t_N·Ξ = -β g_L*(π - μ)` up to a constant. -/
theorem hh_eq (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) {K : ℝ}
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) :
    ∃ c₀ : ℝ, ∀ x, inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x) =
      -β * ResponseAux.Kt gL μ (fun y => theta (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht)
        (β / ((n + 1 : ℕ) : ℝ)) n y - 1) x + c₀ := by
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  set lam := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := theta V lam n with hθ
  have hθ0 : ∀ x, 0 < θ x := theta_pos V hlam0 n
  have hθ1 : ∫ x, θ x ∂μ = 1 := integral_theta V hlam0 n
  have hθi : Integrable θ μ := integrable_theta V hlam0 n
  have hθm : Measurable θ := measurable_theta V hlam0 n
  have hmarg := firstMarginal_RN_eq h hβ ht (n := n)
  have hX := Xibar_eq_integral h hβ ht (n := n)
  have htN := h.tN_eq hβ (Nat.succ_pos n)
  set Ξ := Xi μ Ψ with hΞ
  set Ψbar := ∫ y, Ψ y ∂μ with hΨbar
  set u := Xibar q μ Ψ β (n + 1) with hu
  have hu' : u = ∫ y, θ y • Ξ y ∂μ := by
    rw [hX, hmarg, integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (θ x))
      (ENNReal.measurable_ofReal.comp hθm) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (ENNReal.ofReal (θ y)).toReal • Ξ y = θ y • Ξ y
    rw [ENNReal.toReal_ofReal (hθ0 y).le]
  have hΞi : ∀ x, Integrable (fun y => inner ℝ (Ξ x) (Ξ y) * θ y) μ := by
    intro x
    refine Integrable.bdd_mul (c := ‖Ξ x‖ * (2 * Real.sqrt (gL 0))) hθi ?_ ?_
    · exact (measurable_const.inner h.measurable_Xi).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      calc ‖inner ℝ (Ξ x) (Ξ y)‖ ≤ ‖Ξ x‖ * ‖Ξ y‖ := norm_inner_le_norm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (h.norm_Xi_le y) (norm_nonneg _)
  have hΨi : Integrable Ψ μ := h.integrable_Ψ
  -- the constant `C1 = ∫ θ ⟪Ψ̄, Ψ⟫`
  set C1 : ℝ := ∫ y, inner ℝ Ψbar (Ψ y) * θ y ∂μ with hC1
  have hgi : ∀ x, Integrable (fun y => gL (x - y) * θ y) μ := by
    intro x
    refine Integrable.bdd_mul (c := gL 0) hθi ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (measurable_gL_sub h x).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact abs_gL_le h _
  refine ⟨-β * (inner ℝ Ψbar Ψbar - C1), fun x => ?_⟩
  have hint : Integrable (fun y => θ y • Ξ y) μ := by
    refine Integrable.mono' (hθi.mul_const (2 * Real.sqrt (gL 0)))
      (hθm.smul h.measurable_Xi).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hθ0 y)]
    exact mul_le_mul_of_nonneg_left (h.norm_Xi_le y) (hθ0 y).le
  have e1 : inner ℝ (tN q μ Ψ β (n + 1)) (Ξ x) = -β * inner ℝ u (Ξ x) := by
    rw [htN, real_inner_smul_left]
  have e2 : inner ℝ u (Ξ x) = ∫ y, inner ℝ (Ξ x) (Ξ y) * θ y ∂μ := by
    rw [real_inner_comm, hu', ← integral_inner hint (Ξ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_right]
    ring
  have hexp : ∀ y, inner ℝ (Ξ x) (Ξ y) * θ y = gL (x - y) * θ y - inner ℝ (Ψ x) Ψbar * θ y -
      inner ℝ Ψbar (Ψ y) * θ y + inner ℝ Ψbar Ψbar * θ y := by
    intro y
    simp only [hΞ, Xi, ← hΨbar, inner_sub_left, inner_sub_right, h.gL_eq x y]
    rw [real_inner_comm (Ψ y) Ψbar]
    ring
  have hi2 : Integrable (fun y => inner ℝ Ψbar (Ψ y) * θ y) μ := by
    refine Integrable.bdd_mul (c := ‖Ψbar‖ * Real.sqrt (gL 0)) hθi
      (measurable_const.inner h.Ψ_meas).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    calc ‖inner ℝ Ψbar (Ψ y)‖ ≤ ‖Ψbar‖ * ‖Ψ y‖ := norm_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (h.norm_Ψ_le y) (norm_nonneg _)
  have e3 : ∫ y, inner ℝ (Ξ x) (Ξ y) * θ y ∂μ =
      ∫ y, gL (x - y) * θ y ∂μ - inner ℝ (Ψ x) Ψbar - C1 + inner ℝ Ψbar Ψbar := by
    simp_rw [hexp]
    have j2 : Integrable (fun y => inner ℝ (Ψ x) Ψbar * θ y) μ := hθi.const_mul _
    have j4 : Integrable (fun y => inner ℝ Ψbar Ψbar * θ y) μ := hθi.const_mul _
    have j12 : Integrable (fun y => gL (x - y) * θ y - inner ℝ (Ψ x) Ψbar * θ y) μ := (hgi x).sub j2
    have j123 : Integrable (fun y => gL (x - y) * θ y - inner ℝ (Ψ x) Ψbar * θ y -
        inner ℝ Ψbar (Ψ y) * θ y) μ := j12.sub hi2
    rw [integral_add j123 j4, integral_sub j12 hi2, integral_sub (hgi x) j2,
      integral_const_mul, integral_const_mul, hθ1]
    ring
  have e4 : ResponseAux.Kt gL μ (fun y => θ y - 1) x = ∫ y, gL (x - y) * θ y ∂μ - inner ℝ (Ψ x) Ψbar := by
    unfold ResponseAux.Kt
    have hg1 : Integrable (fun y => gL (x - y)) μ :=
      Integrable.of_bound (measurable_gL_sub h x).aestronglyMeasurable (gL 0)
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_gL_le h _)
    have : ∫ y, gL (x - y) ∂μ = inner ℝ (Ψ x) Ψbar := by
      rw [hΨbar, ← integral_inner hΨi (Ψ x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      exact h.gL_eq x y
    simp_rw [mul_sub, mul_one]
    rw [integral_sub (hgi x) hg1, this]
  rw [e1, e2, e3, e4]
  ring

end Cavity2

section TV

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem real_withDensity {θ : α → ℝ} (hθ0 : ∀ x, 0 ≤ θ x) (hθi : Integrable θ μ) {A : Set α}
    (hA : MeasurableSet A) :
    (μ.withDensity fun x => ENNReal.ofReal (θ x)).real A = ∫ x in A, θ x ∂μ := by
  unfold Measure.real
  rw [withDensity_apply _ hA, ← ofReal_integral_eq_lintegral_ofReal hθi.integrableOn
    ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall fun x _ => hθ0 x))]
  exact ENNReal.toReal_ofReal (setIntegral_nonneg hA fun x _ => hθ0 x)

/-- `L¹` distance of densities from the total-variation (event) distance of the measures. -/
theorem integral_abs_sub_le {θ θ' : α → ℝ} (hθm : Measurable θ) (hθ'm : Measurable θ')
    (hθ0 : ∀ x, 0 ≤ θ x) (hθ'0 : ∀ x, 0 ≤ θ' x) (hθi : Integrable θ μ) (hθ'i : Integrable θ' μ)
    {ε : ℝ} (h : ∀ A : Set α, MeasurableSet A →
      |(μ.withDensity fun x => ENNReal.ofReal (θ x)).real A -
        (μ.withDensity fun x => ENNReal.ofReal (θ' x)).real A| ≤ ε) :
    ∫ x, |θ x - θ' x| ∂μ ≤ 2 * ε := by
  set S : Set α := {x | θ' x < θ x} with hS
  have hSm : MeasurableSet S := measurableSet_lt hθ'm hθm
  have hSc : MeasurableSet Sᶜ := hSm.compl
  have h1 : ∫ x, |θ x - θ' x| ∂μ = (∫ x in S, (θ x - θ' x) ∂μ) + ∫ x in Sᶜ, (θ' x - θ x) ∂μ := by
    have habs : Integrable (fun x => |θ x - θ' x|) μ := (hθi.sub hθ'i).abs
    rw [← integral_add_compl hSm habs]
    congr 1
    · refine setIntegral_congr_fun hSm fun x hx => ?_
      exact abs_of_pos (sub_pos.2 hx)
    · refine setIntegral_congr_fun hSc fun x hx => ?_
      have : θ x ≤ θ' x := not_lt.1 hx
      rw [abs_of_nonpos (by linarith)]; ring
  have h2 : ∫ x in S, (θ x - θ' x) ∂μ =
      (μ.withDensity fun x => ENNReal.ofReal (θ x)).real S -
        (μ.withDensity fun x => ENNReal.ofReal (θ' x)).real S := by
    rw [real_withDensity hθ0 hθi hSm, real_withDensity hθ'0 hθ'i hSm,
      integral_sub hθi.integrableOn hθ'i.integrableOn]
  have h3 : ∫ x in Sᶜ, (θ' x - θ x) ∂μ =
      (μ.withDensity fun x => ENNReal.ofReal (θ' x)).real Sᶜ -
        (μ.withDensity fun x => ENNReal.ofReal (θ x)).real Sᶜ := by
    rw [real_withDensity hθ0 hθi hSc, real_withDensity hθ'0 hθ'i hSc,
      integral_sub hθ'i.integrableOn hθi.integrableOn]
  rw [h1, h2, h3]
  have a1 := h S hSm
  have a2 := h Sᶜ hSc
  rw [abs_le] at a1 a2
  linarith [a1.2, a2.1]

end TV

section ConvL2

variable {d : ℕ}

/-- `L²(μ)` bound of the convolution of the kernel with the density difference `ρ(θ - θ')`. -/
theorem cv_L2_bound {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ)
    (hΛ0 : 0 ≤ Λ) {q : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z)
    {θ θ' : Torus d → ℝ} (hθm : Measurable θ) (hθ'm : Measurable θ') {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hθb : ∀ x, |θ x - θ' x| ≤ Cb) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∫ x, |θ x - θ' x| ∂(withDensityReal ρ) ≤ η) {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ x, ‖ResponseAux.cv q (fun y => ρ y * (θ y - θ' y)) x‖ₑ ^ 2 ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Λ * (2 * ((∫⁻ y, ENNReal.ofReal (q y - K)) ^ 2 * ENNReal.ofReal (Λ * Cb * η) +
        ENNReal.ofReal η ^ 2 * ∫⁻ y, ENNReal.ofReal (min (q y) K ^ 2))) := by
  set w : Torus d → ℝ := fun y => ρ y * (θ y - θ' y) with hw
  have hwm : Measurable w := hρ.measurable.mul (hθm.sub hθ'm)
  -- step a: from `μ` to Lebesgue measure
  have ha : ∫⁻ x, ‖ResponseAux.cv q w x‖ₑ ^ 2 ∂(withDensityReal ρ) ≤
      ENNReal.ofReal Λ * ∫⁻ x, ‖ResponseAux.cv q w x‖ₑ ^ 2 := by
    calc ∫⁻ x, ‖ResponseAux.cv q w x‖ₑ ^ 2 ∂(withDensityReal ρ)
        ≤ ∫⁻ x, ‖ResponseAux.cv q w x‖ₑ ^ 2 ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
          lintegral_mono' (ResponseAux.dens_le Λ hΛ) le_rfl
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
  -- step c: `L¹` norm of `w`
  have hb : ∫⁻ y, ‖w y‖ₑ ≤ ENNReal.ofReal η := by
    have hint : Integrable (fun x => |θ x - θ' x|) (withDensityReal ρ) := by
      haveI := isProb_withDensityReal hρ
      exact Integrable.of_bound (hθm.sub hθ'm).abs.aestronglyMeasurable Cb
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hθb x)
    have h1 : ∫ x, |θ x - θ' x| ∂(withDensityReal ρ) = ∫ x, ρ x * |θ x - θ' x| := ResponseAux.integral_dens hρ _
    have hint2 : Integrable (fun x => ρ x * |θ x - θ' x|) volume := by
      refine Integrable.mono' ((ResponseAux.integrable_rho hρ).mul_const Cb)
        (hρ.measurable.mul (hθm.sub hθ'm).abs).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg x) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hθb x) (hρ.nonneg x)
    have e : ∀ y, ‖w y‖ₑ = ENNReal.ofReal (ρ y * |θ y - θ' y|) := by
      intro y
      rw [hw]
      simp only
      rw [← Real.enorm_of_nonneg (mul_nonneg (hρ.nonneg y) (abs_nonneg _)), enorm_mul, enorm_mul]
      simp [Real.enorm_of_nonneg (hρ.nonneg y)]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hint2
      (Filter.Eventually.of_forall fun x => mul_nonneg (hρ.nonneg x) (abs_nonneg _)), ← h1]
    exact ENNReal.ofReal_le_ofReal hη
  -- step d: `L²` norm of `w`
  have hd : ∫⁻ y, ‖w y‖ₑ ^ 2 ≤ ENNReal.ofReal (Λ * Cb) * ENNReal.ofReal η := by
    calc ∫⁻ y, ‖w y‖ₑ ^ 2 ≤ ∫⁻ y, ENNReal.ofReal (Λ * Cb) * ‖w y‖ₑ := by
          refine lintegral_mono fun y => ?_
          rw [sq]
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hw]; simp only
          rw [abs_mul, abs_of_nonneg (hρ.nonneg y)]
          exact mul_le_mul (hΛ y) (hθb y) (abs_nonneg _) hΛ0
      _ = ENNReal.ofReal (Λ * Cb) * ∫⁻ y, ‖w y‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  have hconv := conv_sq_le hqm hq0 hwm hK
  have hd' : ∫⁻ y, ‖w y‖ₑ ^ 2 ≤ ENNReal.ofReal (Λ * Cb * η) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hΛ0 hCb)]; exact hd
  refine ha.trans (mul_le_mul_right (hconv.trans ?_) _)
  gcongr

end ConvL2

section CavEq

variable {d M : ℕ} {μ : Measure (Torus d)} {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} [IsProbabilityMeasure μ]
  {β : ℝ} {n : ℕ}

/-- **The exact cavity equation for the reference marginal** (`A:eq:reference-cavity-equation`):
`log θ + β (g_L + q) * (π - μ) = D + β q*(π - ν) + λ q*ν + const`, with `θ = dπ/dμ`, `ν` the
cavity marginal, `D = log u + m` the cavity correction and `m = λ n q*ν`. -/
theorem cavity_equation (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) {K : ℝ}
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) [NeZero n]
    {Cz : ℝ} (hCz : ∀ᵐ y ∂μ, |theta (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht)
      (β / ((n + 1 : ℕ) : ℝ)) n y - 1| ≤ Cz) :
    ∃ c : ℝ, ∀ x, Real.log (theta (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n x) +
      β * ResponseAux.Kt (fun w => gL w + q w) μ
        (fun y => theta (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n y - 1) x =
      (Real.log (cavU (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n
          (fun e : Empty => e.elim) x) +
        β / ((n + 1 : ℕ) : ℝ) * n *
          ∫ y, (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht).q y x
            ∂(cavMarg (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n)) +
      β * ((∫ y, q (x - y) * theta (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n y ∂μ) -
        ∫ y, q (x - y) ∂(cavMarg (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n)) +
      β / ((n + 1 : ℕ) : ℝ) *
        ∫ y, q (x - y) ∂(cavMarg (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n) + c := by
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := theta V lam n with hθ
  set ν := cavMarg V lam n with hν
  have hθ0 : ∀ x, 0 < θ x := theta_pos V hlam0 n
  have hθ1 : ∫ x, θ x ∂μ = 1 := integral_theta V hlam0 n
  have hθi : Integrable θ μ := integrable_theta V hlam0 n
  have hθm : Measurable θ := measurable_theta V hlam0 n
  obtain ⟨c₀, hc₀⟩ := hh_eq h hβ ht (n := n)
  have hlamn : lam * (n + 1 : ℕ) = β := by
    rw [hlam]; field_simp
  have hVqx : ∀ x y, V.q y x = q (x - y) := fun x y => by
    show q (y - x) = q (x - y)
    rw [← h.q_even (x - y), neg_sub]
  refine ⟨c₀ - Real.log (∫ x', cavTheta V lam n (fun e : Empty => e.elim) x' ∂μ), fun x => ?_⟩
  have e0 := log_theta_eq V hlam0 n x
  have e1 : V.φ x = β * convMeasure q μ x + inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x) := rfl
  have e2 := hc₀ x
  -- integrability
  have hzi : Integrable (fun y => θ y - 1) μ := hθi.sub (integrable_const _)
  have hgi : Integrable (fun y => gL (x - y) * (θ y - 1)) μ := by
    refine Integrable.bdd_mul (c := gL 0) hzi (measurable_gL_sub h x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]; exact abs_gL_le h _
  have hzb : ∀ᵐ y ∂μ, ‖θ y - 1‖ ≤ Cz := hCz.mono fun y hy => by rwa [Real.norm_eq_abs]
  have hqi : Integrable (fun y => q (x - y) * (θ y - 1)) μ := by
    have := Integrable.bdd_mul (c := Cz) (h.q_int x) hzi.aestronglyMeasurable hzb
    exact this.congr (Filter.Eventually.of_forall fun y => by simp [mul_comm])
  have hq1 : Integrable (fun y => q (x - y)) μ := h.q_int x
  have hqθ : Integrable (fun y => q (x - y) * θ y) μ := by
    have := hqi.add hq1
    exact this.congr (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring)
  have hKt : ResponseAux.Kt (fun w => gL w + q w) μ (fun y => θ y - 1) x =
      ResponseAux.Kt gL μ (fun y => θ y - 1) x +
        ((∫ y, q (x - y) * θ y ∂μ) - convMeasure q μ x) := by
    unfold ResponseAux.Kt
    simp_rw [add_mul]
    rw [integral_add hgi hqi]
    congr 1
    simp_rw [mul_sub, mul_one]
    rw [integral_sub hqθ hq1]
    rfl
  rw [hKt]
  have hm : (∫ y, V.q y x ∂ν) = ∫ y, q (x - y) ∂ν := by simp_rw [hVqx]
  rw [hm]
  rw [e0, e1, e2]
  have hn1 : lam * n = β - lam := by
    have : lam * ((n : ℝ) + 1) = β := by exact_mod_cast hlamn
    linarith
  have : lam * ↑n * ∫ y, q (x - y) ∂ν = (β - lam) * ∫ y, q (x - y) ∂ν := by rw [hn1]
  linarith

end CavEq

section Event2

variable {d M : ℕ} {μ : Measure (Torus d)} {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} [IsProbabilityMeasure μ]
  {β : ℝ} {n : ℕ}

/-- **Cavity versus full marginal** (`A:eq:weak-pin-comparison`): `|π_N(A) - ν_n(A)| ≤ κ/N`. -/
theorem event_pi_nu (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β) {K : ℝ}
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) [NeZero n]
    (hκ : weakKappa (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) β ≤ 1 / 2) {A : Set (Torus d)}
    (hA : MeasurableSet A) :
    |(firstMarginal (RN q μ Ψ β (n + 1))).real A -
        (cavMarg (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) (β / ((n + 1 : ℕ) : ℝ)) n).real A| ≤
      weakKappa (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) β / ((n + 1 : ℕ) : ℝ) := by
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  have hRN := RN_eq_fieldLawK h hβ.le ht (N := n + 1)
  rw [← hV] at hRN
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 := rvh_pin_removed (B := Empty) V hβ.le (N := n + 1) (n := n) (Nat.succ_pos n) (by simp)
    (fun e : Empty => e.elim) hκ (Fin.last n) ⟨0, hn⟩ hA
  rw [pinnedLaw_empty, pinnedLaw_empty] at h1
  have e : (Fin.last n).succAbove (⟨0, hn⟩ : Fin n) = ⟨0, Nat.succ_pos n⟩ := by
    ext; simp [Fin.succAbove, Fin.lt_def]; omega
  rw [e] at h1
  unfold firstMarginal cavMarg
  rw [dif_pos (Nat.succ_pos n), hRN, pinnedLaw_empty]
  exact h1

end Event2

section CvId

variable {d : ℕ}

/-- `q*π - q*ν = q * (ρ(θ - θ'))` for two measures with bounded densities. -/
theorem cv_identity {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ)
    {q : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqi : Integrable q)
    {θ θ' : Torus d → ℝ} (hθm : Measurable θ) (hθ'm : Measurable θ') (hθ0 : ∀ x, 0 ≤ θ x)
    (hθ'0 : ∀ x, 0 ≤ θ' x) {Cb : ℝ} (hθb : ∀ x, θ x ≤ Cb) (hθ'b : ∀ x, θ' x ≤ Cb) (x : Torus d) :
    (∫ y, q (x - y) * θ y ∂(withDensityReal ρ)) -
        ∫ y, q (x - y) ∂((withDensityReal ρ).withDensity fun y => ENNReal.ofReal (θ' y)) =
      ResponseAux.cv q (fun y => ρ y * (θ y - θ' y)) x := by
  haveI : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have hq1 : Integrable (fun y => q (x - y)) volume := hqi.comp_sub_left x
  have hρm := hρ.measurable
  have hb : ∀ (f : Torus d → ℝ), Measurable f → (∀ y, 0 ≤ f y) → (∀ y, f y ≤ Cb) →
      Integrable (fun y => q (x - y) * (ρ y * f y)) volume := by
    intro f hf hf0 hfb
    refine Integrable.mono' (hq1.mul_const (Λ * Cb))
      ((hqm.comp (measurable_const.sub measurable_id)).mul (hρm.mul hf)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (mul_nonneg (hρ.nonneg y) (hf0 y)))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hΛ y) (hfb y) (hf0 y) (le_trans (hρ.nonneg y) (hΛ y))) (hq0 _)
  have e1 : ∫ y, q (x - y) * θ y ∂(withDensityReal ρ) = ∫ y, q (x - y) * (ρ y * θ y) := by
    rw [ResponseAux.integral_dens hρ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have e2 : ∫ y, q (x - y) ∂((withDensityReal ρ).withDensity fun y => ENNReal.ofReal (θ' y)) =
      ∫ y, q (x - y) * (ρ y * θ' y) := by
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun y => ENNReal.ofReal (θ' y))
      (ENNReal.measurable_ofReal.comp hθ'm) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (hθ'0 _), smul_eq_mul]
    rw [ResponseAux.integral_dens hρ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [e1, e2, ← integral_sub (hb θ hθm hθ0 hθb) (hb θ' hθ'm hθ'0 hθ'b)]
  unfold ResponseAux.cv
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

end CvId

section CoreCv

variable {d : ℕ}

/-- The `L²(μ)` estimate of `q * (ρ(θ - θ'))` at the rate `N⁻¹ g(N)` (`K = N`), with `T₀, c₁` constants. -/
theorem cv_L2_rate (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {q : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s)))) :
    ∃ T₀ c₁ : ℝ, 0 ≤ T₀ ∧ 0 < c₁ ∧ ∀ (ρ : Torus d → ℝ), IsProbDensity ρ → ∀ {Λ : ℝ}, (∀ x, ρ x ≤ Λ) → 0 ≤ Λ →
      ∀ {θ θ' : Torus d → ℝ}, Measurable θ → Measurable θ' → ∀ {Cb : ℝ}, 0 ≤ Cb →
      (∀ x, |θ x - θ' x| ≤ Cb) → ∀ {η : ℝ}, 0 ≤ η → ∫ x, |θ x - θ' x| ∂(withDensityReal ρ) ≤ η →
      ∀ {N : ℕ}, 1 ≤ N →
      ∫⁻ x, ‖ResponseAux.cv q (fun y => ρ y * (θ y - θ' y)) x‖ₑ ^ 2 ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (Λ * (2 * ((T₀ * ((N : ℝ)⁻¹ * gFun d s N)) ^ 2 * (Λ * Cb * η) +
          η ^ 2 * (c₁ * gFun d s N)))) := by
  have hp := one_lt_pOf hd hs0 hsd
  set p := pOf d s with hpdef
  obtain ⟨c₁, hc₁, hR2⟩ := second_moment_gFun hd hs0 hsd hK0
  have hpp : 0 < p - 1 := by linarith
  have hT00 : 0 ≤ K0 * (p / (p - 1)) := by positivity
  refine ⟨K0 * (p / (p - 1)), c₁, hT00, hc₁, ?_⟩
  intro ρ hρ Λ hΛ hΛ0 θ θ' hθm hθ'm Cb hCb hθb η hη0 hη N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 := cv_L2_bound hρ hΛ hΛ0 hqm hq0 hθm hθ'm hCb hθb hη0 hη (K := (N : ℝ)) hNpos.le
  refine h1.trans ?_
  have hT : ∫⁻ y, ENNReal.ofReal (q y - N) ≤ ENNReal.ofReal (K0 * (p / (p - 1)) * ((N : ℝ)⁻¹ * gFun d s N)) := by
    refine (lintegral_tail_le hqm hq0 hNpos hp hK0 hw).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 := rpow_one_sub_le_gFun hd hs0 hsd hN1
    calc K0 * (N : ℝ) ^ (1 - p) * (p / (p - 1)) = (K0 * (p / (p - 1))) * (N : ℝ) ^ (1 - p) := by ring
      _ ≤ (K0 * (p / (p - 1))) * ((N : ℝ)⁻¹ * gFun d s N) := by gcongr
  have hR : ∫⁻ y, ENNReal.ofReal (min (q y) N ^ 2) ≤ ENNReal.ofReal (c₁ * gFun d s N) :=
    (lintegral_minsq_le hqm hq0 hN1 hp hK0 hw).trans (ENNReal.ofReal_le_ofReal (hR2 N hN1))
  have hg1 : 1 ≤ gFun d s N := one_le_gFun hd hs0 hsd hN1
  have hT0 : 0 ≤ K0 * (p / (p - 1)) * ((N : ℝ)⁻¹ * gFun d s N) := by positivity
  have : ENNReal.ofReal Λ * (2 * ((∫⁻ y, ENNReal.ofReal (q y - N)) ^ 2 * ENNReal.ofReal (Λ * Cb * η) +
      ENNReal.ofReal η ^ 2 * ∫⁻ y, ENNReal.ofReal (min (q y) N ^ 2))) ≤
      ENNReal.ofReal Λ * (2 * (ENNReal.ofReal (K0 * (p / (p - 1)) * ((N : ℝ)⁻¹ * gFun d s N)) ^ 2 *
        ENNReal.ofReal (Λ * Cb * η) + ENNReal.ofReal η ^ 2 * ENNReal.ofReal (c₁ * gFun d s N))) := by
    gcongr
  refine this.trans (le_of_eq ?_)
  have hη2 : 0 ≤ η := hη0
  rw [← ENNReal.ofReal_pow hT0, ← ENNReal.ofReal_pow hη2,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by have := hc₁; positivity)]
  rw [ENNReal.ofReal_mul hΛ0, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

end CoreCv

section CoreSetup

variable {d M : ℕ}

theorem measurable_integral_kernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure β}
    [SFinite ν] {F : α × β → ℝ} (hF : Measurable F) : Measurable fun x => ∫ y, F (x, y) ∂ν :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

theorem eLpNorm_two_le_const {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal C := by
  refine (eLpNorm_le_of_ae_bound hf (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hC x)).trans ?_
  simp

theorem core_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 < β)
    {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {c : ℝ} (hc0 : 0 ≤ c)
    (hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q gL Ψ (Λ * c))
    (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqe : ∀ z, q (-z) = q z) (hqi : Integrable q)
    (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c)
    {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s))))
    (hkm : Measurable (fun w => gL w + q w)) (hki : Integrable (fun w => gL w + q w))
    (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) = (ĝ n : ℂ))
    (hκ : KappaSmall β (Λ * c)) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₁ ≤ N →
      ∀ (ht : ∀ x, |inner ℝ (tN q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ 1),
      firstMarginal (RN q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (RN q (withDensityReal ρ) Ψ β N)).rnDeriv
          (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  set γ : ℝ := Λ * c with hγ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hγ0 : 0 ≤ γ := mul_nonneg hΛ0 hc0
  set Cν : ℝ := Real.exp ((β * γ + 1) + 0 + β * γ) with hCν
  have hCν1 : 1 ≤ Cν := Real.one_le_exp (by positivity)
  obtain ⟨CD, ND, hCD0, hD⟩ := cavD_torus hd hs0 hsd hΛ1 hqm hq0 hqe hc0 hqc hK0 hw hβ hCν1
  obtain ⟨T₀, c₁, hT₀, hc₁, hconv⟩ := cv_L2_rate hd hs0 hsd hqm hq0 hK0 hw
  set κ₀ : ℝ := 4 * Cν * (β * γ) with hκ₀
  set E : ℝ := Λ * (2 * (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) + (2 * κ₀) ^ 2 * c₁)) with hE
  have hE0 : 0 ≤ E := by positivity
  set Ccv : ℝ := Real.sqrt E with hCcv
  set Cphi : ℝ := CD + β * Ccv + β * (Cν * (Λ * c)) with hCphi
  have hCphi0 : 0 ≤ Cphi := by positivity
  refine ⟨Cν * Cphi, max ND 2, ?_⟩
  intro ρ hρ hΛρ N hN ht
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have h := hRef ρ hρ hΛρ
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := theta V lam n with hθdef
  have hθ0 : ∀ x, 0 < θ x := theta_pos V hlam0 n
  have hθm : Measurable θ := measurable_theta V hlam0 n
  have hθ1 : ∫ x, θ x ∂μ = 1 := integral_theta V hlam0 n
  have hθi : Integrable θ μ := integrable_theta V hlam0 n
  have hVq : ∀ x y, V.q x y = q (x - y) := fun _ _ => rfl
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cν := le_of_eq rfl
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le h hβ.le ht hκ
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  set ν := cavMarg V lam n with hν
  haveI hνp : IsProbabilityMeasure ν := by
    haveI := isProb_pinnedLaw V hlam0 n (fun e : Empty => e.elim)
    have : IsProbabilityMeasure (cavMarg V lam n) := by unfold cavMarg; infer_instance
    exact this
  have hπle : firstMarginal (RN q μ Ψ β (n + 1)) ≤ ENNReal.ofReal Cν • μ :=
    firstMarginal_RN_leK h hβ hN0 ht
  have hπeq := firstMarginal_RN_eq h hβ ht (n := n)
  rw [← hV] at hπeq
  have hνle : ν ≤ ENNReal.ofReal Cν • μ := by
    have := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simp) (fun e : Empty => e.elim) 0
    exact this
  haveI : IsFiniteMeasure (firstMarginal (RN q μ Ψ β (n + 1))) :=
    ⟨lt_of_le_of_lt (hπle Set.univ) (by simp [Measure.smul_apply])⟩
  have hπ_ac := PoleCavityAux.rnDeriv_le_of_le_withDensity μ (firstMarginal (RN q μ Ψ β (n + 1)))
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hπle)
  have hrn : (firstMarginal (RN q μ Ψ β (n + 1))).rnDeriv μ =ᵐ[μ] fun y => ENNReal.ofReal (θ y) := by
    rw [hπeq]; exact Measure.rnDeriv_withDensity μ (ENNReal.measurable_ofReal.comp hθm)
  have hθC : ∀ᵐ y ∂μ, θ y ≤ Cν := by
    filter_upwards [hrn, hπ_ac.2] with y h1 h2
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h2
  refine ⟨hπ_ac.1, ?_⟩
  have hfin : (fun y => ((firstMarginal (RN q μ Ψ β (n + 1))).rnDeriv μ y).toReal - 1) =ᵐ[μ]
      fun y => θ y - 1 := by
    filter_upwards [hrn] with y h1
    rw [h1, ENNReal.toReal_ofReal (hθ0 y).le]
  rw [eLpNorm_congr_ae hfin]
  have hCz : ∀ᵐ y ∂μ, |θ y - 1| ≤ Cν := hθC.mono fun y hy => by
    rw [abs_le]; constructor <;> linarith [hθ0 y]
  obtain ⟨c', hc'⟩ := cavity_equation h hβ ht (n := n) (Cz := Cν) hCz
  -- clipped densities
  have hCν0 : 0 ≤ Cν := by linarith
  set θc : Torus d → ℝ := fun y => min (θ y) Cν with hθc
  have hθcm : Measurable θc := hθm.min measurable_const
  have hθc0 : ∀ y, 0 ≤ θc y := fun y => le_min (hθ0 y).le hCν0
  have hθcb : ∀ y, θc y ≤ Cν := fun y => min_le_right _ _
  have hθc_ae : ∀ᵐ y ∂μ, θc y = θ y := hθC.mono fun y hy => min_eq_left hy
  have hνac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hνle
  haveI : IsFiniteMeasure ν := inferInstance
  have hν_rn := PoleCavityAux.rnDeriv_le_of_le_withDensity μ ν (fun _ => ENNReal.ofReal Cν)
    (by rw [withDensity_const]; exact hνle)
  set θ' : Torus d → ℝ := fun y => (ν.rnDeriv μ y).toReal with hθ'
  set θ'c : Torus d → ℝ := fun y => min (θ' y) Cν with hθ'c
  have hθ'm : Measurable θ' := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hθ'cm : Measurable θ'c := hθ'm.min measurable_const
  have hθ'c0 : ∀ y, 0 ≤ θ'c y := fun y => le_min ENNReal.toReal_nonneg hCν0
  have hθ'cb : ∀ y, θ'c y ≤ Cν := fun y => min_le_right _ _
  have hνeq : ν = μ.withDensity (fun y => ENNReal.ofReal (θ'c y)) := by
    calc ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ hνac).symm
      _ = _ := by
        refine withDensity_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top ν μ, hν_rn.2] with y h1 h2
        have h3 : (ν.rnDeriv μ y).toReal ≤ Cν := ENNReal.toReal_le_of_le_ofReal hCν0 h2
        simp only [hθ'c, hθ', min_eq_left h3, ENNReal.ofReal_toReal h1.ne]
  have hπeq' : firstMarginal (RN q μ Ψ β (n + 1)) = μ.withDensity (fun y => ENNReal.ofReal (θc y)) := by
    rw [hπeq]
    refine withDensity_congr_ae ?_
    filter_upwards [hθc_ae] with y hy
    rw [hy]
  have hθci : Integrable θc μ := Integrable.of_bound hθcm.aestronglyMeasurable Cν
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθc0 y)]; exact hθcb y)
  have hθ'ci : Integrable θ'c μ := Integrable.of_bound hθ'cm.aestronglyMeasurable Cν
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθ'c0 y)]; exact hθ'cb y)
  have hTV : ∫ y, |θc y - θ'c y| ∂μ ≤ 2 * (weakKappa V β / ((n + 1 : ℕ) : ℝ)) := by
    refine integral_abs_sub_le hθcm hθ'cm hθc0 hθ'c0 hθci hθ'ci (fun A hA => ?_)
    rw [← hπeq', ← hνeq]
    exact event_pi_nu h hβ ht hκV hA
  -- the convolution term
  set w : Torus d → ℝ := fun y => ρ y * (θc y - θ'c y) with hw
  have hcvid : ∀ x, (∫ y, q (x - y) * θ y ∂μ) - ∫ y, q (x - y) ∂ν = ResponseAux.cv q w x := by
    intro x
    have e1 : ∫ y, q (x - y) * θ y ∂μ = ∫ y, q (x - y) * θc y ∂μ :=
      integral_congr_ae (hθc_ae.mono fun y hy => by show q (x - y) * θ y = q (x - y) * θc y; rw [hy])
    rw [e1]
    have := cv_identity hρ hΛρ hqm hq0 hqi hθcm hθ'cm hθc0 hθ'c0 hθcb hθ'cb x
    rw [← hνeq] at this
    exact this
  set Dfun : Torus d → ℝ := fun x => Real.log (cavU V lam n (fun e : Empty => e.elim) x) +
    lam * n * ∫ y, V.q y x ∂ν with hDfun
  set Qν : Torus d → ℝ := fun x => ∫ y, q (x - y) ∂ν with hQν
  set Φ : Torus d → ℝ := fun x => Dfun x + β * ResponseAux.cv q w x + lam * Qν x with hΦ
  have heq : ∀ x, Real.log (θ x) + β * ResponseAux.Kt (fun w => gL w + q w) μ (fun y => θ y - 1) x =
      Φ x + c' := by
    intro x
    rw [hc' x]
    simp only [hΦ, hDfun, hQν]
    rw [← hcvid x]
  -- the rate `δ = N⁻¹ g(N)`
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ n + 1 := by omega
    show (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast this
  have hNpos : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hδ : deltaN d s (n + 1) = N⁻¹ * gFun d s N := deltaN_eq_gFun hd hs0 hsd (by omega)
  have hg1 : 1 ≤ gFun d s N := one_le_gFun hd hs0 hsd hN1
  set δ : ℝ := deltaN d s (n + 1) with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδ1 : N⁻¹ ≤ δ := by
    rw [hδ]
    calc N⁻¹ = N⁻¹ * 1 := (mul_one _).symm
      _ ≤ N⁻¹ * gFun d s N := by gcongr
  have hlam_le : lam ≤ β * δ := by
    have : lam = β * N⁻¹ := by rw [hlam]; ring
    rw [this]; gcongr
  -- the cavity correction `D`
  have hDb : ∀ x, 0 ≤ Dfun x ∧ Dfun x ≤ CD * δ := fun x =>
    hD ρ hρ hΛρ V hVq hVC hκV (n + 1) n (by omega) (Nat.le_succ n) x
  have hDm : Measurable Dfun := by
    refine ((Real.measurable_log.comp (measurable_cavU V hlam0 n _)).add (measurable_const.mul ?_))
    exact measurable_integral_kernel (F := fun p : Torus d × Torus d => V.q p.2 p.1)
      (V.measurable_q.comp (measurable_snd.prodMk measurable_fst))
  have hDL2 : eLpNorm Dfun 2 μ ≤ ENNReal.ofReal (CD * δ) :=
    eLpNorm_two_le_const hDm.aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (hDb x).1]; exact (hDb x).2
  -- the convolution term
  have hwm : Measurable w := hρ.measurable.mul (hθcm.sub hθ'cm)
  have hcvm : Measurable (ResponseAux.cv q w) := by
    unfold ResponseAux.cv
    exact measurable_integral_kernel (F := fun p : Torus d × Torus d => q (p.1 - p.2) * w p.2)
      ((hqm.comp (measurable_fst.sub measurable_snd)).mul (hwm.comp measurable_snd))
  have hκ0 : 0 ≤ weakKappa V β := weakKappa_nonneg V hβ.le
  have hκeq : weakKappa V β = κ₀ := rfl
  set η : ℝ := 2 * (weakKappa V β / N) with hη
  have hη0 : 0 ≤ η := by positivity
  have hb : ∀ y, |θc y - θ'c y| ≤ Cν := fun y => by
    rw [abs_le]; constructor <;> linarith [hθc0 y, hθ'c0 y, hθcb y, hθ'cb y]
  have h1 := hconv ρ hρ hΛρ hΛ0 hθcm hθ'cm hCν0 hb hη0 hTV (N := n + 1) (by omega)
  have hE' : Λ * (2 * ((T₀ * (N⁻¹ * gFun d s N)) ^ 2 * (Λ * Cν * η) + η ^ 2 * (c₁ * gFun d s N))) ≤
      E * δ ^ 2 := by
    have ha0 : 0 < N⁻¹ := inv_pos.2 hNpos
    have ha1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    set a : ℝ := N⁻¹ with ha
    set g : ℝ := gFun d s N with hg
    have hηa : η = 2 * κ₀ * a := by rw [hη, hκeq, div_eq_mul_inv]; ring
    have hX : δ ^ 2 = (a * g) ^ 2 := by rw [hδ]
    have hX0 : 0 ≤ (a * g) ^ 2 := sq_nonneg _
    have t1 : (T₀ * (a * g)) ^ 2 * (Λ * Cν * η) ≤ T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 := by
      rw [hηa]
      have : (T₀ * (a * g)) ^ 2 * (Λ * Cν * (2 * κ₀ * a)) =
          (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * a := by ring
      rw [this]
      have hnn : 0 ≤ T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 := by positivity
      calc (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * a ≤ (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left ha1 hnn
        _ = _ := mul_one _
    have t2 : η ^ 2 * (c₁ * g) ≤ (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2 := by
      rw [hηa]
      have : (2 * κ₀ * a) ^ 2 * (c₁ * g) = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) := by ring
      rw [this]
      have : (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2 = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) * g := by ring
      rw [this]
      have hnn : 0 ≤ (2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g) := by positivity
      calc (2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g) = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hg1 hnn
    rw [hX]
    calc Λ * (2 * ((T₀ * (a * g)) ^ 2 * (Λ * Cν * η) + η ^ 2 * (c₁ * g)))
        ≤ Λ * (2 * (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 + (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2)) := by
          gcongr
      _ = E * (a * g) ^ 2 := by rw [hE]; ring
  have hAE : AEStronglyMeasurable (ResponseAux.cv q w) μ := hcvm.aestronglyMeasurable
  have hsq : (eLpNorm (ResponseAux.cv q w) 2 μ) ^ 2 ≤ ENNReal.ofReal (Ccv * δ) ^ 2 := by
    rw [ResponseAux.eLpNorm_two_sq hAE, ← ENNReal.ofReal_pow (by positivity), mul_pow, hCcv,
      Real.sq_sqrt hE0]
    exact h1.trans (ENNReal.ofReal_le_ofReal hE')
  have hcvL2 : eLpNorm (ResponseAux.cv q w) 2 μ ≤ ENNReal.ofReal (Ccv * δ) :=
    (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq
  -- the `λ q*ν` term
  have hQνm : Measurable Qν := measurable_integral_kernel (F := fun p : Torus d × Torus d => q (p.1 - p.2))
    (hqm.comp (measurable_fst.sub measurable_snd))
  have hQb : ∀ x, 0 ≤ Qν x ∧ Qν x ≤ Cν * (Λ * c) := fun x =>
    ⟨integral_nonneg fun y => hq0 _, integral_kernel_le hΛρ hΛ0 hνle hCν0 hqm hq0 hc0 hqc x⟩
  have hQL2 : eLpNorm (fun x => lam * Qν x) 2 μ ≤ ENNReal.ofReal (β * (Cν * (Λ * c)) * δ) :=
    eLpNorm_two_le_const (hQνm.const_mul lam).aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (mul_nonneg hlam0 (hQb x).1)]
      calc lam * Qν x ≤ (β * δ) * (Cν * (Λ * c)) :=
            mul_le_mul hlam_le (hQb x).2 (hQb x).1 (by positivity)
        _ = _ := by ring
  -- Minkowski
  have hΦe : Φ = (Dfun + fun x => β * ResponseAux.cv q w x) + fun x => lam * Qν x := by
    funext x; simp [hΦ]
  have hΦnorm : eLpNorm Φ 2 μ ≤ ENNReal.ofReal (Cphi * δ) := by
    have m1 : AEStronglyMeasurable Dfun μ := hDm.aestronglyMeasurable
    have m2 : AEStronglyMeasurable (fun x => β * ResponseAux.cv q w x) μ :=
      (hcvm.const_mul β).aestronglyMeasurable
    have m3 : AEStronglyMeasurable (fun x => lam * Qν x) μ := (hQνm.const_mul lam).aestronglyMeasurable
    have e2 : eLpNorm (fun x => β * ResponseAux.cv q w x) 2 μ =
        ENNReal.ofReal β * eLpNorm (ResponseAux.cv q w) 2 μ := by
      have := eLpNorm_const_smul (p := 2) (μ := μ) β (ResponseAux.cv q w)
      rw [show (fun x => β * ResponseAux.cv q w x) = β • ResponseAux.cv q w from rfl, this,
        Real.enorm_of_nonneg hβ.le]
    rw [hΦe]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine (add_le_add_left (eLpNorm_add_le (by norm_num)) _).trans ?_
    rw [e2]
    calc eLpNorm Dfun 2 μ + ENNReal.ofReal β * eLpNorm (ResponseAux.cv q w) 2 μ +
          eLpNorm (fun x => lam * Qν x) 2 μ
        ≤ ENNReal.ofReal (CD * δ) + ENNReal.ofReal β * ENNReal.ofReal (Ccv * δ) +
          ENNReal.ofReal (β * (Cν * (Λ * c)) * δ) := by gcongr
      _ = ENNReal.ofReal (Cphi * δ) := by
          rw [← ENNReal.ofReal_mul hβ.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hCphi]; ring
  have hΦm : Measurable Φ := (hDm.add (hcvm.const_mul β)).add (hQνm.const_mul lam)
  have hΦmem : MemLp Φ 2 μ := lt_of_le_of_lt hΦnorm ENNReal.ofReal_lt_top
  -- absorption
  have habs := absorption hρ hΛρ hkm hki ĝ hĝ hcoef hβ.le hθm hθ0 hCν1 hθC hθ1 hΦmem heq
  refine habs.trans ?_
  calc ENNReal.ofReal Cν * eLpNorm Φ 2 μ ≤ ENNReal.ofReal Cν * ENNReal.ofReal (Cphi * δ) := by gcongr
    _ = ENNReal.ofReal (Cν * Cphi * δ) := by
        rw [← ENNReal.ofReal_mul hCν0]; congr 1; ring

end CoreSetup

section Small

variable {d M : ℕ} {μ : Measure (Torus d)} {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} [IsProbabilityMeasure μ] {β : ℝ}

/-- The two descriptions of the weak reference `R⁰_N` agree. -/
theorem R0_eq_R0small (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (N : ℕ) :
    R0 q μ β N = RefSmall.R0small q β μ N := by
  have e : E0 q μ β N = RefSmall.R0w q β μ N := by
    funext X
    unfold E0 RefSmall.R0w
    rw [← Finset.mul_sum, RefSmall.pairSum_eq_half h.q_even]
  have hRs : RefSmall.R0small q β μ N = tiltMeasure (Measure.pi fun _ : Fin N => μ) (E0 q μ β N) := by
    rw [e]; rfl
  rw [hRs]
  unfold R0
  exact (RefSmall.tiltMeasure_eq_tilted _ _ (h.measurable_E0 β N) (β * N * γ) (h.E0_le hβ N)).symm

/-- `∫ μ_N(Ξ) dP = ∫ Ξ dπ` when all one-coordinate marginals of `P` coincide. -/
theorem integral_empXi_eq (h : RefHyp μ q gL Ψ γ) {n : ℕ} (P : Measure (Config d (n + 1)))
    [IsProbabilityMeasure P] (hmarg : ∀ i : Fin (n + 1), P.map (fun X => X i) = P.map (fun X => X 0)) :
    ∫ X, empXi μ Ψ X ∂P = ∫ y, Xi μ Ψ y ∂(P.map (fun X => X 0)) := by
  unfold empXi
  have hint : ∀ i : Fin (n + 1), Integrable (fun X : Config d (n + 1) => Xi μ Ψ (X i)) P :=
    fun i => Integrable.of_bound (h.measurable_Xi.comp (measurable_pi_apply i)).aestronglyMeasurable
      (2 * Real.sqrt (gL 0)) (Filter.Eventually.of_forall fun X => h.norm_Xi_le _)
  rw [integral_smul, integral_finsetSum _ fun i _ => hint i]
  have h2 : ∀ i : Fin (n + 1), ∫ X : Config d (n + 1), Xi μ Ψ (X i) ∂P =
      ∫ y, Xi μ Ψ y ∂(P.map (fun X => X 0)) := by
    intro i
    rw [← hmarg i, integral_map (measurable_pi_apply i).aemeasurable h.measurable_Xi.aestronglyMeasurable]
  simp_rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (1 / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) = 1 := by field_simp
  rw [this, one_smul]


theorem aN_nonneg {s : ℝ} {N : ℕ} (hN : 1 ≤ N) : 0 ≤ aN d s N := by
  unfold aN
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine mul_nonneg ?_ (Real.rpow_nonneg (by linarith) _)
  split_ifs
  · have := Real.log_nonneg hN0; linarith
  · linarith

open HRS.External.Entropy InformationTheory in
/-- **Uniform smallness of the calibration field** `‖t_N·Ξ‖_∞ → 0`, uniformly over the densities
`ρ ≤ Λ` (quantitative form of `sup_calibration_field_le_one`). -/
theorem small_field (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 < β)
    (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, N₀ ≤ N → ∀ x : Torus d,
        |inner ℝ (tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ ε := by
  intro ε hε
  obtain ⟨C, hC0, N₁, hN₁2, hKL⟩ := RefSmall.klDiv_R0small_weakSplit_le hd hs0 hsd hτ L hΛ1 hβ.le
  set g0 : ℝ := (weakSplit d s τ L).gL 0 with hg0
  have hg00 : 0 ≤ g0 := by
    have := hΨ 0 0
    rw [sub_self] at this
    rw [hg0, this]; exact real_inner_self_nonneg
  set B : ℝ := 2 * Real.sqrt g0 with hB
  have hB0 : 0 ≤ B := by positivity
  set f : ℕ → ℝ := fun N => β * (2 * B * Real.sqrt (β * C * aN d s N / 2)) * B with hf
  have hf0 : Tendsto f atTop (𝓝 0) := by
    have h1 := (RefSmall.tendsto_aN (by omega : 1 ≤ d) hs0 hsd)
    have h2 : Tendsto (fun N : ℕ => β * C * aN d s N / 2) atTop (𝓝 0) := by
      simpa using (h1.const_mul (β * C)).div_const 2
    have h3 : Tendsto (fun N : ℕ => Real.sqrt (β * C * aN d s N / 2)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h2
      rw [Real.sqrt_zero] at this
      exact this
    have h4 := ((h3.const_mul (2 * B)).const_mul β).mul_const B
    simpa [hf] using h4
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hf0.eventually (gt_mem_nhds hε))
  refine ⟨max N₁ N₂, fun ρ hρ hΛρ N hN x => ?_⟩
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have h := refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := le_trans (le_max_left N₁ N₂) hN; omega⟩
  have hN1 : N₁ ≤ n + 1 := le_trans (le_max_left _ _) hN
  have hfN := hN₂ (n + 1) (le_trans (le_max_right _ _) hN)
  have hq := RefSmall.smallKernel_weakSplit hd hs0 hsd hτ L
  set P := RefSmall.R0small (weakSplit d s τ L).q β μ (n + 1) with hP
  haveI : IsProbabilityMeasure P := hq.isProb_R0small hρ hΛρ hβ.le (n + 1)
  have hPex := RefSmall.R0small_isExchangeable hq.meas hq.even β μ (n + 1)
  have hmarg : ∀ i : Fin (n + 1), P.map (fun X => X i) = P.map (fun X => X 0) :=
    fun i => hPex.marginal_eq i 0
  have hR0 : R0 (weakSplit d s τ L).q μ β (n + 1) = P := R0_eq_R0small h hβ.le (n + 1)
  have h1 := h.tN_norm_le hβ (Nat.succ_pos n)
  rw [hR0, integral_empXi_eq h P hmarg] at h1
  set π0 := P.map (fun X => X 0) with hπ0
  have h2 : ‖∫ y, Xi μ Ψ y ∂π0‖ ≤ 2 * B * tvDist π0 μ := by
    have := RefSmall.norm_integral_sub_le_two_mul_tvDist π0 μ h.measurable_Xi hB0
      (fun y => h.norm_Xi_le y)
    rwa [h.integral_Xi, sub_zero] at this
  have h3 : tvDist π0 μ ≤ Real.sqrt (β * C * aN d s (n + 1) / 2) := by
    have hmul := hPex.mul_klDiv_marginal_le μ 0 P
    have hK := hKL ρ hρ hΛρ (n + 1) hN1
    have ha0 := aN_nonneg (s := s) (d := d) (N := n + 1) (by omega)
    have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have e : ENNReal.ofReal (β * ((n + 1 : ℕ) : ℝ) * (C * aN d s (n + 1))) =
        ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (β * (C * aN d s (n + 1))) := by
      rw [show β * ((n + 1 : ℕ) : ℝ) * (C * aN d s (n + 1)) =
        ((n + 1 : ℕ) : ℝ) * (β * (C * aN d s (n + 1))) by ring,
        ENNReal.ofReal_mul hn0.le, ENNReal.ofReal_natCast]
    have hK2 : InformationTheory.klDiv π0 μ ≤ ENNReal.ofReal (β * (C * aN d s (n + 1))) := by
      rw [e] at hK
      have := hmul.trans hK
      exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 this
    have hKne : InformationTheory.klDiv π0 μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK2
    refine (tvDist_le_sqrt_klDiv π0 μ hKne).trans (Real.sqrt_le_sqrt ?_)
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hK2
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  have h4 : ‖tN (weakSplit d s τ L).q μ Ψ β (n + 1)‖ ≤ β * (2 * B * Real.sqrt (β * C * aN d s (n + 1) / 2)) :=
    h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) hβ.le)
  calc |inner ℝ (tN (weakSplit d s τ L).q μ Ψ β (n + 1)) (Xi μ Ψ x)|
      ≤ ‖tN (weakSplit d s τ L).q μ Ψ β (n + 1)‖ * ‖Xi μ Ψ x‖ := abs_real_inner_le_norm _ _
    _ ≤ (β * (2 * B * Real.sqrt (β * C * aN d s (n + 1) / 2))) * B :=
        mul_le_mul h4 (h.norm_Xi_le x) (norm_nonneg _) (by positivity)
    _ = f (n + 1) := rfl
    _ ≤ ε := hfN.le

end Small

section Final2

variable {d : ℕ}

/-- **Prop 4.2, reference part, `L²` bound**: `‖dπ_N/dμ - 1‖_{L²(μ)} ≤ C δ_N`. -/
theorem reference_marginal_density_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 < β)
    (hκ : KappaSmall β (Λ * (weakSplit d s τ L).c))
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₀ ≤ N →
      firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)).rnDeriv
            (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, -, -, h13, -, h15, -, -⟩ :=
    weakSplit_spec hd hs0 hsd hτ hτ1 L
  set c : ℝ := (weakSplit d s τ L).c with hc
  set q : Torus d → ℝ := (weakSplit d s τ L).q with hq
  set gL : Torus d → ℝ := (weakSplit d s τ L).gL with hgL
  obtain ⟨B, hB0, hB⟩ := h15
  obtain ⟨K0, hK0, hw⟩ := weakLp_of_envelope hd hs0 hsd hB0 hB
  have hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c := by
    have := ofReal_integral_eq_lintegral_ofReal h7 (Filter.Eventually.of_forall h6)
    rw [h8] at this
    exact le_of_eq this.symm
  have hgLi : Integrable gL := h13.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace gL)
  have hkm : Measurable (fun w => gL w + q w) := h13.measurable.add h5
  have hki : Integrable (fun w => gL w + q w) := hgLi.add h7
  set ĝ : Lattice d → ℝ := fun n => rieszCoeff d s n + (if n = 0 then c else 0) with hĝdef
  have hĝ : ∀ n, 0 ≤ ĝ n := by
    intro n
    by_cases hn : n = 0
    · simp [hĝdef, hn, rieszCoeff, h10]
    · have := rieszCoeff_pos hd hs0 hsd n hn
      simp [hĝdef, hn]; exact this.le
  have hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) = (ĝ n : ℂ) := by
    intro n
    have e1 : ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) =
        ∫ x, (Torus.mode (-n) x * ((periodicRiesz d s x : ℝ) : ℂ) + Torus.mode (-n) x * (c : ℂ)) := by
      refine integral_congr_ae ?_
      filter_upwards [h4] with x hx
      rw [← mul_add]
      congr 1
      rw [hx]; push_cast; ring
    rw [e1]
    have hgi : Integrable (fun x => Torus.mode (-n) x * ((periodicRiesz d s x : ℝ) : ℂ)) := by
      have := (KernelAux.integrable_periodicRiesz hd hs0 hsd).ofReal (𝕜 := ℂ)
      exact this.bdd_mul (c := 1) (Torus.continuous_mode (-n)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-n) x).le)
    have hci : Integrable (fun x => Torus.mode (-n) x * (c : ℂ)) := by
      have : Integrable (fun x => Torus.mode (-n) x) :=
        (integrable_const (1 : ℂ)).bdd_mul (c := 1) (Torus.continuous_mode (-n)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-n) x).le) |>.congr
          (Filter.Eventually.of_forall fun x => by simp)
      exact this.mul_const _
    rw [integral_add hgi hci, KernelAux.integral_periodicRiesz_mode hd hs0 hsd n, integral_mul_const,
      Torus.integral_mode (-n)]
    by_cases hn : n = 0
    · simp [hĝdef, hn, rieszCoeff]
    · have : -n ≠ 0 := neg_ne_zero.2 hn
      simp [hĝdef, hn, this]
  have hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q gL Ψ (Λ * c) := fun ρ hρ hΛρ =>
    refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  obtain ⟨C, N₁, hcore⟩ := core_L2 hd hs0 hsd hΛ1 hβ h10 hRef h5 h6 (hQ_even hd hs0 hsd τ L) h7 hqc hK0 hw
    hkm hki ĝ hĝ hcoef hκ
  obtain ⟨N₂, hsmall⟩ := small_field hd hs0 hsd hτ hτ1 L hΛ1 hβ Ψ hΨ 1 one_pos
  refine ⟨C, max N₁ N₂, fun ρ hρ hΛρ N hN => ?_⟩
  exact hcore ρ hρ hΛρ N (le_trans (le_max_left _ _) hN)
    (fun x => hsmall ρ hρ hΛρ N (le_trans (le_max_right _ _) hN) x)

end Final2

section FieldCmp

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- **Two weak ensembles with different one-body fields** (`A:eq:disagreement`): the marginals differ by
at most `4 e^{M+M'+βγ} ‖ψ - ψ'‖_{L¹(μ)}`. -/
theorem field_event_comparison (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hnN : n ≤ N) {ψ ψ' : E → ℝ} (hψ : IsField μ ψ V.M V.M') (hψ' : IsField μ ψ' V.M V.M')
    (hκ : weakKappa V β ≤ 1 / 2) {D : ℝ} (hD : ∫ z, |ψ z - ψ' z| ∂μ ≤ D) (j : Fin n)
    {A : Set E} (hA : MeasurableSet A) :
    |((fieldLaw V ψ (β / N) n).map (fun y => y j)).real A -
        ((fieldLaw V ψ' (β / N) n).map (fun y => y j)).real A| ≤
      4 * Real.exp (V.M + V.M' + β * V.γ) * D := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hD0 : 0 ≤ D := le_trans (integral_nonneg fun z => abs_nonneg _) hD
  have hΛ : V.M' + β / N * n * V.γ ≤ V.M' + β * V.γ := by
    have h1 : β / N * n ≤ β := by
      have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
      calc β / N * n ≤ β / N * N := by gcongr
        _ = β := by field_simp
    have := mul_le_mul_of_nonneg_right h1 V.γ_nonneg
    linarith
  have h := rvh_field_event (V := V) j hψ hψ' hlam (Λ := V.M' + β * V.γ) hΛ hD
    (r := weakKappa V β) (fun i => by
      rw [four_exp_eq]
      exact row_sum_le_of_uniform hN0 hnN (weakKappa_nonneg V hβ) i) (by linarith) hA
  refine h.trans ?_
  have e : V.M + (V.M' + β * V.γ) = V.M + V.M' + β * V.γ := by ring
  rw [e]
  have h1 : (1 : ℝ) / 2 ≤ 1 - weakKappa V β := by linarith
  have h2 : 0 ≤ 2 * Real.exp (V.M + V.M' + β * V.γ) * D := by positivity
  rw [div_le_iff₀ (by linarith)]
  calc 2 * Real.exp (V.M + V.M' + β * V.γ) * D
      = 4 * Real.exp (V.M + V.M' + β * V.γ) * D * (1 / 2) := by ring
    _ ≤ 4 * Real.exp (V.M + V.M' + β * V.γ) * D * (1 - weakKappa V β) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)

end FieldCmp

section TvRN

variable {d M : ℕ} {μ : Measure (Torus d)} {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} [IsProbabilityMeasure μ] {β : ℝ} {n : ℕ}

theorem R0_eq_fieldLawK (h : RefHyp μ q gL Ψ γ) (hβ : 0 ≤ β) (N : ℕ) {K : ℝ}
    (ht0 : ∀ x, |inner ℝ (0 : EuclideanSpace ℝ (Fin M)) (Xi μ Ψ x)| ≤ K) :
    R0 q μ β N = fieldLaw (weakPotK h hβ 0 ht0) (weakPotK h hβ 0 ht0).φ (β / N) N := by
  unfold R0
  rw [fieldLaw_eq_tilted]
  · congr 1
    funext X
    simp only [E0, weakPotK, pairEnergy, inner_zero_left, add_zero]
  · have := h.integrable_exp_E0 hβ N
    convert this using 2 with X
    simp only [E0, weakPotK, pairEnergy, inner_zero_left, add_zero]

/-- **`R_N` versus `R⁰_N`** (`A:eq:disagreement`): the first marginals differ by at most
`4 e^{M + βγ} ‖t_N·Ξ‖_∞` in total variation. -/
theorem tv_RN_R0 (h : RefHyp μ q gL Ψ γ) (hβ : 0 < β)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : weakKappa (weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht) β ≤ 1 / 2) {εh : ℝ}
    (hεh : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ εh) {A : Set (Torus d)}
    (hA : MeasurableSet A) :
    |(firstMarginal (RN q μ Ψ β (n + 1))).real A -
        ((R0 q μ β (n + 1)).map (fun X => X ⟨0, Nat.succ_pos n⟩)).real A| ≤
      4 * Real.exp ((β * γ + 1) + 0 + β * γ) * εh := by
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  have ht0 : ∀ x, |inner ℝ (0 : EuclideanSpace ℝ (Fin M)) (Xi μ Ψ x)| ≤ 1 := fun x => by simp
  set V0 := weakPotK h hβ.le (0 : EuclideanSpace ℝ (Fin M)) ht0 with hV0
  have hRN := RN_eq_fieldLawK h hβ.le ht (N := n + 1)
  rw [← hV] at hRN
  have hR0 := R0_eq_fieldLawK h hβ.le (n + 1) ht0
  rw [← hV0] at hR0
  have hψ : IsField μ V.φ V.M V.M' := ⟨V.measurable_φ, V.φ_le, V.integrable_φ, V.neg_le_integral_φ⟩
  have hψ' : IsField μ V0.φ V.M V.M' :=
    ⟨V0.measurable_φ, fun x => V0.φ_le x, V0.integrable_φ, V0.neg_le_integral_φ⟩
  have hD : ∫ z, |V.φ z - V0.φ z| ∂μ ≤ εh := by
    have hb : ∀ z, |V.φ z - V0.φ z| ≤ εh := fun z => by
      have : V.φ z - V0.φ z = inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ z) := by
        show β * convMeasure q μ z + inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ z) -
          (β * convMeasure q μ z + inner ℝ (0 : EuclideanSpace ℝ (Fin M)) (Xi μ Ψ z)) = _
        simp
      rw [this]; exact hεh z
    calc ∫ z, |V.φ z - V0.φ z| ∂μ ≤ ∫ _z, εh ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hb)
      _ = εh := by simp
  have h1 := field_event_comparison V hβ.le (N := n + 1) (n := n + 1) (Nat.succ_pos n) le_rfl hψ hψ' hκ hD
    ⟨0, Nat.succ_pos n⟩ hA
  have e1 : firstMarginal (RN q μ Ψ β (n + 1)) =
      (fieldLaw V V.φ (β / ((n + 1 : ℕ) : ℝ)) (n + 1)).map (fun y => y ⟨0, Nat.succ_pos n⟩) := by
    unfold firstMarginal; rw [dif_pos (Nat.succ_pos n), hRN]
  have e2 : (R0 q μ β (n + 1)).map (fun X => X ⟨0, Nat.succ_pos n⟩) =
      (fieldLaw V V0.φ (β / ((n + 1 : ℕ) : ℝ)) (n + 1)).map (fun y => y ⟨0, Nat.succ_pos n⟩) := by
    rw [hR0]; rfl
  rw [e1, e2]
  exact h1

end TvRN

section TvR0

variable {d M : ℕ}

open HRS.External.Entropy InformationTheory in
/-- `‖π⁰_N - μ‖_TV ≤ √(β C a_N / 2)` uniformly over the densities `ρ ≤ Λ`. -/
theorem tv_R0_mu (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 < β)
    (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∃ (C : ℝ) (N₁ : ℕ), 0 ≤ C ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ n : ℕ,
      N₁ ≤ n + 1 →
      tvDist ((R0 (weakSplit d s τ L).q (withDensityReal ρ) β (n + 1)).map
          (fun X => X ⟨0, Nat.succ_pos n⟩)) (withDensityReal ρ) ≤
        Real.sqrt (β * C * aN d s (n + 1) / 2) := by
  obtain ⟨C, hC0, N₁, hN₁2, hKL⟩ := RefSmall.klDiv_R0small_weakSplit_le hd hs0 hsd hτ L hΛ1 hβ.le
  refine ⟨C, N₁, hC0, fun ρ hρ hΛρ n hN1 => ?_⟩
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have h := refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  have hq := RefSmall.smallKernel_weakSplit hd hs0 hsd hτ L
  set P := RefSmall.R0small (weakSplit d s τ L).q β μ (n + 1) with hP
  haveI : IsProbabilityMeasure P := hq.isProb_R0small hρ hΛρ hβ.le (n + 1)
  have hPex := RefSmall.R0small_isExchangeable hq.meas hq.even β μ (n + 1)
  have hR0 : R0 (weakSplit d s τ L).q μ β (n + 1) = P := R0_eq_R0small h hβ.le (n + 1)
  rw [hR0]
  set π0 := P.map (fun X => X ⟨0, Nat.succ_pos n⟩) with hπ0
  have hmul := hPex.mul_klDiv_marginal_le μ ⟨0, Nat.succ_pos n⟩ P
  have hK := hKL ρ hρ hΛρ (n + 1) hN1
  have ha0 := aN_nonneg (s := s) (d := d) (N := n + 1) (by omega)
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have e : ENNReal.ofReal (β * ((n + 1 : ℕ) : ℝ) * (C * aN d s (n + 1))) =
      ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (β * (C * aN d s (n + 1))) := by
    rw [show β * ((n + 1 : ℕ) : ℝ) * (C * aN d s (n + 1)) =
      ((n + 1 : ℕ) : ℝ) * (β * (C * aN d s (n + 1))) by ring,
      ENNReal.ofReal_mul hn0.le, ENNReal.ofReal_natCast]
  have hK2 : InformationTheory.klDiv π0 μ ≤ ENNReal.ofReal (β * (C * aN d s (n + 1))) := by
    rw [e] at hK
    have := hmul.trans hK
    exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 this
  have hKne : InformationTheory.klDiv π0 μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK2
  refine (tvDist_le_sqrt_klDiv π0 μ hKne).trans (Real.sqrt_le_sqrt ?_)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hK2
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  linarith

end TvR0

section ConvDiff

variable {d : ℕ}

open HRS.External.Entropy in
/-- **Truncation estimate** for `q * (P - Q)`: `|q*P(x) - q*Q(x)| ≤ K ‖P - Q‖_TV + 2 C_b Λ T(K)`, where
`T(K) ≥ ∫ (q - K)₊`. -/
theorem conv_diff_le {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) (hΛ0 : 0 ≤ Λ)
    {q : Torus d → ℝ} (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z)
    {P Q : Measure (Torus d)} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hP : P ≤ ENNReal.ofReal Cb • withDensityReal ρ) (hQ : Q ≤ ENNReal.ofReal Cb • withDensityReal ρ)
    {c : ℝ} (hc0 : 0 ≤ c) (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c) {K : ℝ} (hK : 0 ≤ K)
    {T : ℝ} (hT0 : 0 ≤ T) (hT : ∫⁻ z, ENNReal.ofReal (q z - K) ≤ ENNReal.ofReal T) (x : Torus d) :
    |∫ y, q (x - y) ∂P - ∫ y, q (x - y) ∂Q| ≤ K * tvDist P Q + 2 * (Cb * (Λ * T)) := by
  set g1 : Torus d → ℝ := fun z => min (q z) K with hg1
  set g2 : Torus d → ℝ := fun z => max (q z - K) 0 with hg2
  have hg1m : Measurable g1 := hqm.min measurable_const
  have hg2m : Measurable g2 := (hqm.sub_const K).max measurable_const
  have hg10 : ∀ z, 0 ≤ g1 z := fun z => le_min (hq0 z) hK
  have hg20 : ∀ z, 0 ≤ g2 z := fun z => le_max_right _ _
  have hsplit : ∀ z, q z = g1 z + g2 z := by
    intro z
    simp only [hg1, hg2]
    rcases le_total (q z) K with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hxm : ∀ f : Torus d → ℝ, Measurable f → Measurable fun y => f (x - y) :=
    fun f hf => hf.comp (measurable_const.sub measurable_id)
  -- integrability of the pieces
  have hg1b : ∀ y, |g1 (x - y)| ≤ K := fun y => by
    rw [abs_of_nonneg (hg10 _)]; exact min_le_right _ _
  have hg2i : ∀ (Pm : Measure (Torus d)), Pm ≤ ENNReal.ofReal Cb • withDensityReal ρ →
      Integrable (fun y => g2 (x - y)) Pm := by
    intro Pm hR
    have h1 : ∫⁻ y, ENNReal.ofReal (g2 (x - y)) ∂Pm ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Λ *
        ENNReal.ofReal T) := by
      calc ∫⁻ y, ENNReal.ofReal (g2 (x - y)) ∂Pm
          ≤ ∫⁻ y, ENNReal.ofReal (g2 (x - y)) ∂(ENNReal.ofReal Cb • withDensityReal ρ) :=
            lintegral_mono' hR le_rfl
        _ = ENNReal.ofReal Cb * ∫⁻ y, ENNReal.ofReal (g2 (x - y)) ∂(withDensityReal ρ) := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (g2 z)) := by
            gcongr
            exact KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (g2 z)) x
        _ ≤ _ := by
            gcongr
            have : ∫⁻ z, ENNReal.ofReal (g2 z) = ∫⁻ z, ENNReal.ofReal (q z - K) := by
              refine lintegral_congr fun z => ?_
              simp only [hg2]
              rw [ENNReal.ofReal_max]; simp
            rw [this]; exact hT
    refine ⟨(hxm g2 hg2m).aestronglyMeasurable, ?_⟩
    have : ∫⁻ y, ‖g2 (x - y)‖ₑ ∂Pm = ∫⁻ y, ENNReal.ofReal (g2 (x - y)) ∂Pm := by
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_of_nonneg (hg20 _)]
    rw [HasFiniteIntegral, this]
    exact lt_of_le_of_lt h1 (by
      refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ENNReal.ofReal_lt_top))
  have hg1i : ∀ (Pm : Measure (Torus d)) [IsProbabilityMeasure Pm], Integrable (fun y => g1 (x - y)) Pm :=
    fun Pm _ => Integrable.of_bound (hxm g1 hg1m).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hg1b y)
  have e : ∀ (Pm : Measure (Torus d)) [IsProbabilityMeasure Pm], Pm ≤ ENNReal.ofReal Cb • withDensityReal ρ →
      ∫ y, q (x - y) ∂Pm = ∫ y, g1 (x - y) ∂Pm + ∫ y, g2 (x - y) ∂Pm := by
    intro Pm _ hR
    rw [← integral_add (hg1i Pm) (hg2i Pm hR)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hsplit _)
  have hI2 : ∀ (Pm : Measure (Torus d)), Pm ≤ ENNReal.ofReal Cb • withDensityReal ρ →
      ∫ y, g2 (x - y) ∂Pm ≤ Cb * (Λ * T) := fun Pm hR => by
    refine integral_kernel_le hΛ hΛ0 hR hCb hg2m hg20 hT0 ?_ x
    have : ∫⁻ z, ENNReal.ofReal (g2 z) = ∫⁻ z, ENNReal.ofReal (q z - K) := by
      refine lintegral_congr fun z => ?_
      simp only [hg2]
      rw [ENNReal.ofReal_max]; simp
    rw [this]; exact hT
  have hI20 : ∀ (Pm : Measure (Torus d)), 0 ≤ ∫ y, g2 (x - y) ∂Pm := fun Pm =>
    integral_nonneg fun y => hg20 _
  rw [e P hP, e Q hQ]
  have hTV := RefSmall.abs_integral_sub_le_tvDist_of_nonneg P Q (g := fun y => g1 (x - y)) (hxm g1 hg1m)
    hK (fun y => hg10 _) (fun y => min_le_right _ _)
  have h2 := hI2 P hP
  have h3 := hI2 Q hQ
  have h4 := hI20 P
  have h5 := hI20 Q
  rw [abs_le] at hTV ⊢
  constructor <;> linarith [hTV.1, hTV.2]

end ConvDiff

section Aux3

variable {d : ℕ}

theorem tendsto_deltaN (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Tendsto (fun N : ℕ => deltaN d s N) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold deltaN
  by_cases h1 : s < (d : ℝ) / 2
  · simp only [h1, if_true]
    exact tendsto_inv_atTop_zero.comp hcast
  · by_cases h2 : s = (d : ℝ) / 2
    · simp only [h2, lt_irrefl, if_false, if_true]
      have h3 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
      have h4 : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := h3.comp hcast
      have h5 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ + Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp hcast).add h4
      refine h5.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
      field_simp
    · simp only [h1, h2, if_false]
      have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
      have hs : 0 < s := by linarith
      have hneg : 1 - (d : ℝ) / s < 0 := by
        have : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs]; linarith
        linarith
      have := (tendsto_rpow_neg_atTop (y := (d : ℝ) / s - 1) (by
        have : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs]; linarith
        linarith)).comp hcast
      refine this.congr fun N => ?_
      simp only [Function.comp]
      congr 1; ring


open HRS.External.Entropy in
theorem tvDist_le_of_forall {α : Type*} [MeasurableSpace α] (P Q : Measure α) {c : ℝ}
    (h : ∀ A : Set α, MeasurableSet A → |P.real A - Q.real A| ≤ c) : tvDist P Q ≤ c :=
  ciSup_le fun A => h A.1 A.2

theorem abs_sub_one_le_of_abs_log_le {θ E : ℝ} (hθ : 0 < θ) (h : |Real.log θ| ≤ E) :
    |θ - 1| ≤ Real.exp E - 1 := by
  have h1 : θ ≤ Real.exp E := by
    have := (abs_le.1 h).2
    calc θ = Real.exp (Real.log θ) := (Real.exp_log hθ).symm
      _ ≤ _ := Real.exp_le_exp.2 this
  have h2 : Real.exp (-E) ≤ θ := by
    have := (abs_le.1 h).1
    calc Real.exp (-E) ≤ Real.exp (Real.log θ) := Real.exp_le_exp.2 this
      _ = θ := Real.exp_log hθ
  have h3 : 2 ≤ Real.exp E + Real.exp (-E) := by
    have := sq_nonneg (Real.exp (E / 2) - Real.exp (-(E / 2)))
    have e1 : Real.exp (E / 2) * Real.exp (-(E / 2)) = 1 := by rw [← Real.exp_add]; simp
    have e2 : Real.exp (E / 2) ^ 2 = Real.exp E := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : Real.exp (-(E / 2)) ^ 2 = Real.exp (-E) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    nlinarith [e1, e2, e3]
  rw [abs_le]
  constructor <;> linarith

end Aux3

section CoreUnif

variable {d M : ℕ}

set_option maxHeartbeats 1600000 in
theorem core_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 < β)
    {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {c : ℝ} (hc0 : 0 ≤ c)
    (hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q gL Ψ (Λ * c))
    (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqe : ∀ z, q (-z) = q z)
    (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c)
    {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s))))
    (hκ : KappaSmall β (Λ * c))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, N₀ ≤ N → ∀ x : Torus d,
        |inner ℝ (tN q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ ε)
    {ε₀ : ℕ → ℝ} (hε₀ : Tendsto ε₀ atTop (𝓝 0)) {N₃ : ℕ}
    (hTV0 : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, N₃ ≤ n + 1 → 1 ≤ n →
      HRS.External.Entropy.tvDist ((R0 q (withDensityReal ρ) β (n + 1)).map
        (fun X => X ⟨0, Nat.succ_pos n⟩)) (withDensityReal ρ) ≤ ε₀ (n + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₁ : ℕ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₁ ≤ N →
      firstMarginal (RN q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ), |((firstMarginal (RN q (withDensityReal ρ) Ψ β N)).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ≤ ε := by
  intro ε hε
  set γ : ℝ := Λ * c with hγ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hγ0 : 0 ≤ γ := mul_nonneg hΛ0 hc0
  set Cν : ℝ := Real.exp ((β * γ + 1) + 0 + β * γ) with hCν
  have hCν1 : 1 ≤ Cν := Real.one_le_exp (by positivity)
  have hCν0 : 0 ≤ Cν := by linarith
  have hp := one_lt_pOf hd hs0 hsd
  set p : ℝ := pOf d s with hpdef
  have hpp : 0 < p - 1 := by linarith
  obtain ⟨CD, ND, hCD0, hD⟩ := cavD_torus hd hs0 hsd hΛ1 hqm hq0 hqe hc0 hqc hK0 hw hβ hCν1
  set κ₀ : ℝ := 4 * Cν * (β * γ) with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by positivity
  -- the constants
  set Es : ℝ := Real.log (1 + ε) / 2 with hEs
  have hEs0 : 0 < Es := by
    have : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    positivity
  set ε' : ℝ := Es / 5 with hε'
  have hε'0 : 0 < ε' := by positivity
  set Tf : ℝ → ℝ := fun K => K0 * K ^ (1 - p) * (p / (p - 1)) with hTf
  have hTf0 : ∀ K, 0 < K → 0 ≤ Tf K := fun K hK => by
    have := Real.rpow_pos_of_pos hK (1 - p); simp only [hTf]; positivity
  -- choose the truncation level `K`
  have hKex : ∃ K : ℝ, 1 ≤ K ∧ 2 * (β * (Cν * (Λ * Tf K))) ≤ ε' := by
    have hlim : Tendsto (fun K : ℝ => K ^ (-(p - 1))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hpp
    have hlim2 : Tendsto (fun K : ℝ => 2 * (β * (Cν * (Λ * (K0 * K ^ (-(p - 1)) * (p / (p - 1))))))) atTop
        (𝓝 0) := by
      have := ((hlim.const_mul K0).mul_const (p / (p - 1))).const_mul (Λ)
      have := (this.const_mul Cν).const_mul β
      have := this.const_mul 2
      simpa using this
    obtain ⟨K, hK⟩ := (eventually_ge_atTop (1 : ℝ)).and (hlim2.eventually (gt_mem_nhds hε'0)) |>.exists
    refine ⟨K, hK.1, ?_⟩
    have e : Tf K = K0 * K ^ (-(p - 1)) * (p / (p - 1)) := by
      simp only [hTf]; congr 2; ring_nf
    rw [e]; exact hK.2.le
  obtain ⟨K, hK1, hKT⟩ := hKex
  have hKpos : 0 < K := by linarith
  set τ : ℝ := ε' / (β * K) with hτ
  have hτ0 : 0 < τ := by positivity
  set εh : ℝ := min 1 (min ε' (τ / (12 * Cν))) with hεh
  have hεh0 : 0 < εh := by
    refine lt_min one_pos (lt_min hε'0 ?_)
    positivity
  have hεh1 : εh ≤ 1 := min_le_left _ _
  have hεh2 : εh ≤ ε' := (min_le_right _ _).trans (min_le_left _ _)
  have hεh3 : 4 * Cν * εh ≤ τ / 3 := by
    have : εh ≤ τ / (12 * Cν) := (min_le_right _ _).trans (min_le_right _ _)
    have h12 : 0 < 12 * Cν := by positivity
    calc 4 * Cν * εh ≤ 4 * Cν * (τ / (12 * Cν)) := by gcongr
      _ = τ / 3 := by field_simp; ring
  obtain ⟨Nh, hNh⟩ := hsmall εh hεh0
  -- the large-`N` conditions
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ N : ℕ in atTop, κ₀ / (N : ℝ) ≤ τ / 3 := by
    have : Tendsto (fun N : ℕ => κ₀ / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat κ₀
    exact this.eventually (ge_mem_nhds (by positivity))
  have hc' : ∀ᶠ N : ℕ in atTop, ε₀ N ≤ τ / 3 := hε₀.eventually (ge_mem_nhds (by positivity))
  have hd' : ∀ᶠ N : ℕ in atTop, β * (Cν * (Λ * c)) / (N : ℝ) ≤ ε' := by
    have : Tendsto (fun N : ℕ => β * (Cν * (Λ * c)) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    exact this.eventually (ge_mem_nhds hε'0)
  have he : ∀ᶠ N : ℕ in atTop, CD * deltaN d s N ≤ ε' := by
    have := (tendsto_deltaN hd hs0 hsd).const_mul CD
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds hε'0)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hb.and (hc'.and (hd'.and he)))
  refine ⟨max (max (max Nh ND) (max N₂ 2)) N₃, fun ρ hρ hΛρ N hN0' => ?_⟩
  have hN : max (max Nh ND) (max N₂ 2) ≤ N := le_trans (le_max_left _ _) hN0'
  have hN3 : N₃ ≤ N := le_trans (le_max_right _ _) hN0'
  have hNh' : Nh ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hND' : ND ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hNb, hNc, hNd, hNe⟩ := hN₂ N hN₂'
  have hεhN := hNh ρ hρ hΛρ N hNh'
  have ht : ∀ x, |inner ℝ (tN q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ 1 :=
    fun x => (hεhN x).trans hεh1
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have h := hRef ρ hρ hΛρ
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := theta V lam n with hθdef
  have hθ0 : ∀ x, 0 < θ x := theta_pos V hlam0 n
  have hθm : Measurable θ := measurable_theta V hlam0 n
  have hVq : ∀ x y, V.q x y = q (x - y) := fun _ _ => rfl
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cν := le_of_eq rfl
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le h hβ.le ht hκ
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  set ν := cavMarg V lam n with hν
  haveI hνp : IsProbabilityMeasure ν := by
    haveI := isProb_pinnedLaw V hlam0 n (fun e : Empty => e.elim)
    have : IsProbabilityMeasure (cavMarg V lam n) := by unfold cavMarg; infer_instance
    exact this
  have hπle : firstMarginal (RN q μ Ψ β (n + 1)) ≤ ENNReal.ofReal Cν • μ :=
    firstMarginal_RN_leK h hβ hN0 ht
  have hπeq := firstMarginal_RN_eq h hβ ht (n := n)
  rw [← hV] at hπeq
  have hνle : ν ≤ ENNReal.ofReal Cν • μ := by
    have := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simp) (fun e : Empty => e.elim) 0
    exact this
  haveI : IsFiniteMeasure (firstMarginal (RN q μ Ψ β (n + 1))) :=
    ⟨lt_of_le_of_lt (hπle Set.univ) (by simp [Measure.smul_apply])⟩
  have hπ_ac := PoleCavityAux.rnDeriv_le_of_le_withDensity μ (firstMarginal (RN q μ Ψ β (n + 1)))
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hπle)
  refine ⟨hπ_ac.1, ?_⟩
  have hrn : (firstMarginal (RN q μ Ψ β (n + 1))).rnDeriv μ =ᵐ[μ] fun y => ENNReal.ofReal (θ y) := by
    rw [hπeq]; exact Measure.rnDeriv_withDensity μ (ENNReal.measurable_ofReal.comp hθm)
  -- the total-variation distance of `μ` and `ν`
  haveI : IsProbabilityMeasure (R0 q μ β (n + 1)) := h.isProb_R0 hβ.le (n + 1)
  have hTVμν : HRS.External.Entropy.tvDist μ ν ≤ τ := by
    refine tvDist_le_of_forall μ ν fun A hA => ?_
    have h1 := hTV0 ρ hρ hΛρ n hN3 hn
    have h1' := HRS.External.Entropy.abs_le_tvDist ((R0 q μ β (n + 1)).map
      (fun X => X ⟨0, Nat.succ_pos n⟩)) μ hA
    have h2 := tv_RN_R0 h hβ ht hκV hεhN hA
    have h3 := event_pi_nu h hβ ht hκV hA
    have hκeq : weakKappa V β = κ₀ := rfl
    rw [hκeq] at h3
    have hεn : ε₀ (n + 1) ≤ τ / 3 := hNc
    have hκn : κ₀ / ((n + 1 : ℕ) : ℝ) ≤ τ / 3 := hNb
    have hA1 : |((R0 q μ β (n + 1)).map (fun X => X ⟨0, Nat.succ_pos n⟩)).real A - μ.real A| ≤ τ / 3 :=
      h1'.trans (h1.trans hεn)
    have hA2 : |(firstMarginal (RN q μ Ψ β (n + 1))).real A -
        ((R0 q μ β (n + 1)).map (fun X => X ⟨0, Nat.succ_pos n⟩)).real A| ≤ τ / 3 :=
      h2.trans (by exact hεh3)
    have hA3 : |(firstMarginal (RN q μ Ψ β (n + 1))).real A - ν.real A| ≤ τ / 3 := h3.trans hκn
    rw [abs_le] at hA1 hA2 hA3 ⊢
    constructor <;> linarith [hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2]
  -- the pointwise bound of `φ + log u`
  have hμle : μ ≤ ENNReal.ofReal Cν • μ := by
    intro A
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hCν1)
  have hT : ∫⁻ z, ENNReal.ofReal (q z - K) ≤ ENNReal.ofReal (Tf K) :=
    lintegral_tail_le hqm hq0 hKpos hp hK0 hw
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set a0 : Empty → Torus d := fun e => e.elim with ha0
  set Dfun : Torus d → ℝ := fun x => Real.log (cavU V lam n a0 x) + lam * n * ∫ y, V.q y x ∂ν with hDfun
  set Qν : Torus d → ℝ := fun x => ∫ y, q (x - y) ∂ν with hQν
  have hVqx : ∀ x, (∫ y, V.q y x ∂ν) = Qν x := fun x => by
    simp only [hQν]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show q (y - x) = q (x - y)
    rw [← hqe (x - y), neg_sub]
  set gfun : Torus d → ℝ := fun x => V.φ x + Real.log (cavU V lam n a0 x) with hgfun
  have hQb : ∀ x, 0 ≤ Qν x ∧ Qν x ≤ Cν * (Λ * c) := fun x =>
    ⟨integral_nonneg fun y => hq0 _, integral_kernel_le hΛρ hΛ0 hνle hCν0 hqm hq0 hc0 hqc x⟩
  have hn1 : lam * n = β - lam := by
    have : lam * ((n : ℝ) + 1) = β := by rw [hlam]; push_cast; field_simp
    linarith
  have hDb : ∀ x, 0 ≤ Dfun x ∧ Dfun x ≤ CD * deltaN d s (n + 1) := fun x =>
    hD ρ hρ hΛρ V hVq hVC hκV (n + 1) n (by omega) (Nat.le_succ n) x
  have hgb : ∀ x, |gfun x| ≤ Es := by
    intro x
    have hdiff := conv_diff_le hΛρ hΛ0 hqm hq0 (P := μ) (Q := ν) hCν0 hμle hνle hc0 hqc hKpos.le
      (hTf0 K hKpos) hT x
    have hd1 : |convMeasure q μ x - Qν x| ≤ K * τ + 2 * (Cν * (Λ * Tf K)) := by
      refine hdiff.trans ?_
      have : K * HRS.External.Entropy.tvDist μ ν ≤ K * τ := mul_le_mul_of_nonneg_left hTVμν hKpos.le
      linarith
    have e : gfun x = β * (convMeasure q μ x - Qν x) + lam * Qν x +
        inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x) + Dfun x := by
      have e1 : V.φ x = β * convMeasure q μ x + inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x) := rfl
      have e2 : Real.log (cavU V lam n a0 x) = Dfun x - lam * n * Qν x := by
        simp only [hDfun]; rw [hVqx x]; ring
      simp only [hgfun]
      rw [e1, e2, hn1]
      ring
    have h1 : |β * (convMeasure q μ x - Qν x)| ≤ ε' + ε' := by
      rw [abs_mul, abs_of_pos hβ]
      calc β * |convMeasure q μ x - Qν x| ≤ β * (K * τ + 2 * (Cν * (Λ * Tf K))) :=
            mul_le_mul_of_nonneg_left hd1 hβ.le
        _ = β * K * τ + 2 * (β * (Cν * (Λ * Tf K))) := by ring
        _ ≤ ε' + ε' := by
            have : β * K * τ = ε' := by rw [hτ]; field_simp
            linarith
    have h2 : |lam * Qν x| ≤ ε' := by
      rw [abs_of_nonneg (mul_nonneg hlam0 (hQb x).1)]
      calc lam * Qν x ≤ lam * (Cν * (Λ * c)) := mul_le_mul_of_nonneg_left (hQb x).2 hlam0
        _ = β * (Cν * (Λ * c)) / ((n + 1 : ℕ) : ℝ) := by rw [hlam]; ring
        _ ≤ ε' := hNd
    have h3 : |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ ε' := (hεhN x).trans hεh2
    have h4 : |Dfun x| ≤ ε' := by
      rw [abs_of_nonneg (hDb x).1]; exact (hDb x).2.trans hNe
    rw [e]
    have := abs_add_le (β * (convMeasure q μ x - Qν x) + lam * Qν x + inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)) (Dfun x)
    have := abs_add_le (β * (convMeasure q μ x - Qν x) + lam * Qν x) (inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x))
    have := abs_add_le (β * (convMeasure q μ x - Qν x)) (lam * Qν x)
    have hEs5 : Es = 5 * ε' := by rw [hε']; ring
    linarith
  -- normalisation: `Z = ∫ exp(gfun)`
  have hZeq : ∫ x, cavTheta V lam n a0 x ∂μ = ∫ x, Real.exp (gfun x) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Real.exp (pinField V lam a0 x) * cavU V lam n a0 x = Real.exp (V.φ x + Real.log (cavU V lam n a0 x))
    rw [Real.exp_add, Real.exp_log (cavU_pos V hlam0 a0 n x), pinField_empty]
  have hZi : Integrable (fun x => Real.exp (gfun x)) μ := by
    rw [← funext fun x => show cavTheta V lam n a0 x = Real.exp (gfun x) from by
      show Real.exp (pinField V lam a0 x) * cavU V lam n a0 x = Real.exp (V.φ x + Real.log (cavU V lam n a0 x))
      rw [Real.exp_add, Real.exp_log (cavU_pos V hlam0 a0 n x), pinField_empty]]
    exact integrable_cavTheta V hlam0 a0 n
  have hZhi : ∫ x, Real.exp (gfun x) ∂μ ≤ Real.exp Es := by
    calc ∫ x, Real.exp (gfun x) ∂μ ≤ ∫ _x, Real.exp Es ∂μ :=
          integral_mono hZi (integrable_const _) fun x => Real.exp_le_exp.2 ((abs_le.1 (hgb x)).2)
      _ = Real.exp Es := by simp
  have hZlo : Real.exp (-Es) ≤ ∫ x, Real.exp (gfun x) ∂μ := by
    calc Real.exp (-Es) = ∫ _x, Real.exp (-Es) ∂μ := by simp
      _ ≤ _ := integral_mono (integrable_const _) hZi fun x => Real.exp_le_exp.2 ((abs_le.1 (hgb x)).1)
  have hlogZ : |Real.log (∫ x, cavTheta V lam n a0 x ∂μ)| ≤ Es := by
    rw [hZeq]
    have hZpos : 0 < ∫ x, Real.exp (gfun x) ∂μ := lt_of_lt_of_le (Real.exp_pos _) hZlo
    rw [abs_le]
    constructor
    · calc -Es = Real.log (Real.exp (-Es)) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) hZlo
    · calc Real.log (∫ x, Real.exp (gfun x) ∂μ) ≤ Real.log (Real.exp Es) := Real.log_le_log hZpos hZhi
        _ = Es := Real.log_exp _
  have hlogθ : ∀ x, |Real.log (θ x)| ≤ 2 * Es := by
    intro x
    have := log_theta_eq V hlam0 n x
    have e : Real.log (θ x) = gfun x - Real.log (∫ x', cavTheta V lam n a0 x' ∂μ) := by
      rw [this]
    rw [e]
    have h1 := hgb x
    calc |gfun x - Real.log (∫ x', cavTheta V lam n a0 x' ∂μ)| ≤
        |gfun x| + |Real.log (∫ x', cavTheta V lam n a0 x' ∂μ)| := abs_sub _ _
      _ ≤ 2 * Es := by linarith
  have hε2 : Real.exp (2 * Es) - 1 = ε := by
    rw [hEs, show 2 * (Real.log (1 + ε) / 2) = Real.log (1 + ε) by ring, Real.exp_log (by linarith)]
    ring
  filter_upwards [hrn] with y h1
  rw [h1, ENNReal.toReal_ofReal (hθ0 y).le]
  have := abs_sub_one_le_of_abs_log_le (hθ0 y) (hlogθ y)
  rw [hε2] at this
  exact this

end CoreUnif

section Final3

variable {d : ℕ}

/-- **`Q:eq:reference-input`, last bound** (`‖dπ_N/dμ - 1‖_∞ → 0`). -/
theorem reference_marginal_density_uniform (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {β : ℝ} (hβ : 0 < β)
    (hκ : KappaSmall β (Λ * (weakSplit d s τ L).c))
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, N₀ ≤ N →
      firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          |((firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ ε := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, -, -, h13, -, h15, -, -⟩ :=
    weakSplit_spec hd hs0 hsd hτ hτ1 L
  set c : ℝ := (weakSplit d s τ L).c with hc
  set q : Torus d → ℝ := (weakSplit d s τ L).q with hq
  obtain ⟨B, hB0, hB⟩ := h15
  obtain ⟨K0, hK0, hw⟩ := weakLp_of_envelope hd hs0 hsd hB0 hB
  have hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c := by
    have := ofReal_integral_eq_lintegral_ofReal h7 (Filter.Eventually.of_forall h6)
    rw [h8] at this
    exact le_of_eq this.symm
  have hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q (weakSplit d s τ L).gL Ψ (Λ * c) := fun ρ hρ hΛρ =>
    refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  obtain ⟨C₃, N₃, hC₃0, hTV3⟩ := tv_R0_mu hd hs0 hsd hτ hτ1 L hΛ1 hβ Ψ hΨ
  have hε₀ : Tendsto (fun N : ℕ => Real.sqrt (β * C₃ * aN d s N / 2)) atTop (𝓝 0) := by
    have h1 := (RefSmall.tendsto_aN (by omega : 1 ≤ d) hs0 hsd)
    have h2 : Tendsto (fun N : ℕ => β * C₃ * aN d s N / 2) atTop (𝓝 0) := by
      simpa using (h1.const_mul (β * C₃)).div_const 2
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at this
    exact this
  exact core_unif hd hs0 hsd hΛ1 hβ h10 hRef h5 h6 (hQ_even hd hs0 hsd τ L) hqc hK0 hw hκ
    (small_field hd hs0 hsd hτ hτ1 L hΛ1 hβ Ψ hΨ) hε₀ (N₃ := N₃)
    (fun ρ hρ hΛρ n hN3 _ => hTV3 ρ hρ hΛρ n hN3)

end Final3

end HRS.External.RefMarg

end
