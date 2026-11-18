import HRS.MS.SA16Y6Tc2

/-!
# S.A.16 (SA16Y6) Tc3: convolution of an integrable kernel with a smooth function with bounded jets (boundary `s = d-1`)

For `k ∈ L¹` and `V` smooth with all jets bounded (`sa16y6_BS`): `k ⋆ V` is smooth, `∂(k ⋆ V) = k ⋆ ∂V`
(`sa16y6_cv_fderiv`, `sa16y6_cv_pd`), and for the heat kernel `g_a ⋆ ∂_jV = (∂_j g_a) ⋆ V` (`sa16y6_cv_ibp`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.MS.ToriCoefA

section Tc3
variable {d : ℕ}

lemma sa16y6_BS_fderiv_vec {V : Euc d → ℝ} (hV : sa16y6_BS V) (v : Euc d) :
    sa16y6_BS (fun y => fderiv ℝ V y v) := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ V) := hV.1.fderiv_right (m := ∞) (by simp)
  refine ⟨hf.clm_apply contDiff_const, fun n => ?_⟩
  obtain ⟨B, hB⟩ := hV.2 (n + 1)
  refine ⟨‖v‖ * B, fun x => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ V) (c := v) (x := x) (N := ∞)
    (n := n) hf.contDiffAt (by exact_mod_cast le_top)
  refine h1.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)

lemma sa16y6_BS_pd {V : Euc d → ℝ} (hV : sa16y6_BS V) :
    ∀ (j : ℕ) (idx : Fin j → Fin d), sa16y6_BS (partialDeriv idx V) := by
  intro j
  induction j with
  | zero =>
    intro idx
    have : partialDeriv idx V = V := funext fun x => sa16j_pd_zero idx V x
    rw [this]; exact hV
  | succ j ih =>
    intro idx
    obtain ⟨i, idx', rfl⟩ : ∃ (i : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons i idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have : partialDeriv (Fin.cons i idx' : Fin (j + 1) → Fin d) V =
        fun y => fderiv ℝ (partialDeriv idx' V) y (sa16z_e i) :=
      funext fun y => sa16s_pd_cons hV.1 i idx' y
    rw [this]
    exact sa16y6_BS_fderiv_vec (ih idx') _

lemma sa16y6_BS_bounds {V : Euc d → ℝ} (hV : sa16y6_BS V) :
    (∃ B0 : ℝ, ∀ x, ‖V x‖ ≤ B0) ∧ ∃ B1 : ℝ, ∀ x, ‖fderiv ℝ V x‖ ≤ B1 := by
  obtain ⟨B0, h0⟩ := hV.2 0
  obtain ⟨B1, h1⟩ := hV.2 1
  exact ⟨⟨B0, fun x => by simpa [norm_iteratedFDeriv_zero] using h0 x⟩,
    ⟨B1, fun x => by simpa [norm_iteratedFDeriv_one] using h1 x⟩⟩

lemma sa16y6_cv_hasFDerivAt {k V : Euc d → ℝ} (hkm : Measurable k) (hk : Integrable k) (hV : sa16y6_BS V)
    (x₀ : Euc d) :
    HasFDerivAt (sa16r_cv k V) (∫ z, k z • fderiv ℝ V (x₀ - z)) x₀ := by
  obtain ⟨⟨B0, h0⟩, ⟨B1, h1⟩⟩ := sa16y6_BS_bounds hV
  have hV1 : ContDiff ℝ 1 V := hV.1.of_le (by exact_mod_cast le_top)
  have hVc : Continuous V := hV1.continuous
  have hVd : ∀ y, HasFDerivAt V (fderiv ℝ V y) y := fun y => ((hV1.differentiable (by simp)) y).hasFDerivAt
  have hVf : Continuous (fderiv ℝ V) := hV1.continuous_fderiv (by simp)
  have hmeas : ∀ x, AEStronglyMeasurable (fun z => k z * V (x - z)) volume := fun x =>
    hkm.aestronglyMeasurable.mul ((hVc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hint : ∀ x, Integrable (fun z => k z * V (x - z)) volume := fun x => by
    refine Integrable.mono' (hk.norm.mul_const B0) (hmeas x) (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h0 _) (norm_nonneg _)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := (volume : Measure (Euc d)))
    (F := fun x z => k z * V (x - z)) (F' := fun x z => k z • fderiv ℝ V (x - z)) (x₀ := x₀)
    (bound := fun z => ‖k z‖ * B1) (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos) (Eventually.of_forall hmeas) (hint x₀)
    (hkm.aestronglyMeasurable.smul ((hVf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
    (Eventually.of_forall fun z x _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (h1 _) (norm_nonneg _))
    (hk.norm.mul_const B1)
    (Eventually.of_forall fun z x _ => by
      have h2 := (hVd (x - z)).comp x ((hasFDerivAt_id x).sub_const z)
      have h3 := h2.const_mul (k z)
      exact h3.congr_fderiv (by ext v; simp))
  exact key

lemma sa16y6_cv_fderiv {k V : Euc d → ℝ} (hkm : Measurable k) (hk : Integrable k) (hV : sa16y6_BS V)
    (x v : Euc d) : fderiv ℝ (sa16r_cv k V) x v = sa16r_cv k (fun y => fderiv ℝ V y v) x := by
  obtain ⟨⟨B0, h0⟩, ⟨B1, h1⟩⟩ := sa16y6_BS_bounds hV
  have hV1 : ContDiff ℝ 1 V := hV.1.of_le (by exact_mod_cast le_top)
  have hVf : Continuous (fderiv ℝ V) := hV1.continuous_fderiv (by simp)
  rw [(sa16y6_cv_hasFDerivAt hkm hk hV x).fderiv]
  have hint : Integrable (fun z => k z • fderiv ℝ V (x - z)) volume := by
    refine Integrable.mono' (hk.norm.mul_const B1)
      (hkm.aestronglyMeasurable.smul ((hVf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
      (Eventually.of_forall fun z => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h1 _) (norm_nonneg _)
  rw [ContinuousLinearMap.integral_apply hint v]
  unfold sa16r_cv
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [smul_eq_mul]

lemma sa16y6_cv_contDiff_nat {k : Euc d → ℝ} (hkm : Measurable k) (hk : Integrable k) :
    ∀ n : ℕ, ∀ V : Euc d → ℝ, sa16y6_BS V → ContDiff ℝ n (sa16r_cv k V) := by
  intro n
  induction n with
  | zero =>
    intro V hV
    refine contDiff_zero.2 ?_
    exact continuous_iff_continuousAt.2 fun x => (sa16y6_cv_hasFDerivAt hkm hk hV x).continuousAt
  | succ n ih =>
    intro V hV
    have hdiff : Differentiable ℝ (sa16r_cv k V) := fun x => (sa16y6_cv_hasFDerivAt hkm hk hV x).differentiableAt
    have := (contDiff_succ_iff_fderiv_apply (𝕜 := ℝ) (n := (n : WithTop ℕ∞)) (f := sa16r_cv k V)).2
      ⟨hdiff, fun h => absurd h (by simp), fun y => ?_⟩
    · exact_mod_cast this
    · have e : (fun x => fderiv ℝ (sa16r_cv k V) x y) = sa16r_cv k (fun z => fderiv ℝ V z y) :=
        funext fun x => sa16y6_cv_fderiv hkm hk hV x y
      rw [e]
      exact ih _ (sa16y6_BS_fderiv_vec hV y)

lemma sa16y6_cv_contDiff {k V : Euc d → ℝ} (hkm : Measurable k) (hk : Integrable k) (hV : sa16y6_BS V) :
    ContDiff ℝ ∞ (sa16r_cv k V) :=
  contDiff_infty.2 fun n => sa16y6_cv_contDiff_nat hkm hk n V hV

lemma sa16y6_cv_pd {k V : Euc d → ℝ} (hkm : Measurable k) (hk : Integrable k) (hV : sa16y6_BS V) :
    ∀ (j : ℕ) (idx : Fin j → Fin d), partialDeriv idx (sa16r_cv k V) = sa16r_cv k (partialDeriv idx V) := by
  intro j
  induction j with
  | zero =>
    intro idx
    funext x
    rw [sa16j_pd_zero]
    unfold sa16r_cv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16j_pd_zero]
  | succ j ih =>
    intro idx
    obtain ⟨i, idx', rfl⟩ : ∃ (i : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons i idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    funext x
    rw [sa16s_pd_cons (sa16y6_cv_contDiff hkm hk hV) i idx' x, ih idx',
      sa16y6_cv_fderiv hkm hk (sa16y6_BS_pd hV j idx') x]
    unfold sa16r_cv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16s_pd_cons hV.1 i idx']

lemma sa16y6_cv_ibp {a : ℝ} (ha : 0 < a) {V : Euc d → ℝ} (hV : sa16y6_BS V) (j : Fin d) (x : Euc d) :
    sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ V y (sa16z_e j)) x = sa16r_cv (sa16r_dg d a j) V x := by
  obtain ⟨⟨B0, h0⟩, ⟨B1, h1⟩⟩ := sa16y6_BS_bounds hV
  have hV1 : ContDiff ℝ 1 V := hV.1.of_le (by exact_mod_cast le_top)
  have hVc : Continuous V := hV1.continuous
  have hVf : Continuous (fderiv ℝ V) := hV1.continuous_fderiv (by simp)
  have hVd : ∀ y, HasFDerivAt V (fderiv ℝ V y) y := fun y => ((hV1.differentiable (by simp)) y).hasFDerivAt
  set g : Euc d → ℝ := fun z => V (x - z) with hg
  have hgd : ∀ z, HasFDerivAt g (-(fderiv ℝ V (x - z))) z := fun z => by
    have := (hVd (x - z)).comp z ((hasFDerivAt_id z).const_sub x)
    exact this.congr_fderiv (by ext v; simp)
  have hgv : ∀ z, fderiv ℝ g z (sa16z_e j) = -fderiv ℝ V (x - z) (sa16z_e j) := fun z => by
    rw [(hgd z).fderiv]; simp
  have hfv : ∀ z, fderiv ℝ (sa16r_g d a) z (sa16z_e j) = sa16r_dg d a j z := fun z =>
    sa16r_g_fderiv ha z j
  have hgi := sa16r_g_int (d := d) ha
  have hdgi := sa16r_dg_int (d := d) ha j
  have hgc : Continuous g := hVc.comp (continuous_const.sub continuous_id)
  have hI1 : Integrable (fun z => fderiv ℝ (sa16r_g d a) z (sa16z_e j) * g z) volume := by
    simp_rw [hfv]
    refine Integrable.mono' (hdgi.norm.mul_const B0) ((sa16r_dg_cont a j).aestronglyMeasurable.mul hgc.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h0 _) (norm_nonneg _)
  have hDc : Continuous (fun z => fderiv ℝ V (x - z) (sa16z_e j)) :=
    (hVf.comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  have hI2 : Integrable (fun z => sa16r_g d a z * fderiv ℝ g z (sa16z_e j)) volume := by
    simp_rw [hgv]
    refine Integrable.mono' (hgi.norm.mul_const B1) ((sa16r_g_contDiff (a := a)).continuous.aestronglyMeasurable.mul
      hDc.neg.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_neg]
    exact ((ContinuousLinearMap.le_opNorm _ _).trans (by simp [EuclideanSpace.norm_single] ; exact h1 _))
  have hI3 : Integrable (fun z => sa16r_g d a z * g z) volume := by
    refine Integrable.mono' (hgi.norm.mul_const B0) ((sa16r_g_contDiff (a := a)).continuous.aestronglyMeasurable.mul
      hgc.aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h0 _) (norm_nonneg _)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := sa16r_g d a) (g := g) (v := sa16z_e j) hI1 hI2 hI3
    (fun z _ => ((sa16r_g_contDiff (a := a)).differentiable (by simp)) z)
    (fun z _ => (hgd z).differentiableAt)
  unfold sa16r_cv
  simp_rw [hgv, hfv] at hibp
  simp only [mul_neg, integral_neg, neg_inj] at hibp
  exact hibp

end Tc3

end HRS.Whole.AppendixA.Phase2SA16R
