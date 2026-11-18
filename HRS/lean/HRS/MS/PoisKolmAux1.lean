import HRS.MS.PoisSgAux1
import HRS.MS.PoisFlowAux2

/-!
# POIS-KOLM, part 1: joint regularity of the pathwise flow in `(t, x)`

Pathwise, deterministic input for the Kolmogorov backward equation.  For a fixed continuous noise
path the flow `φ_t(x) = flowMap q B w t x` solves `φ_t(x) = x + ∫_0^t b(φ_s(x)) ds + c_t` with
`b = -q • id + B` and `c_t = ∑_k w^k_t σ_k` independent of `x`.  From the `x`-regularity of each
time slice (`pois_flow`) we derive, by differentiating the integral equation under the integral sign
(`kl_hasFDerivAt_intervalIntegral`), the first and second variational equations, hence the
time-Lipschitz continuity of `Dφ_t(x)` and `D²φ_t(x)` uniformly in `x`, hence joint continuity of
`(t, x) ↦ φ_t(x), Dφ_t(x), D²φ_t(x)` on `[0,T] × ℝ^d` (`kl_path_cont_*`).

Helper lemmas carry the prefix `kl_`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal Interval
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace HRS.MS.PoisKolm

variable {d : ℕ}

/-! ### Generic lemmas -/


theorem kl_intervalIntegrable_of_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {T K : ℝ} (f : ℝ → V) (hm : AEStronglyMeasurable f (volume.restrict (Icc 0 T)))
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ‖f s‖ ≤ K) :
    ∀ u ∈ Icc (0 : ℝ) T, IntervalIntegrable f volume 0 u := by
  have hint : IntegrableOn f (Icc 0 T) volume := by
    refine (integrable_const K).mono' hm ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => hb s hs)
  intro u hu
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu.1]
  exact hint.mono_set (fun s hs => ⟨hs.1.le, hs.2.trans hu.2⟩)

/-- `F t = a + ∫_0^t f` with `f` bounded and measurable on `[0,T]` is Lipschitz on `[0,T]`. -/
theorem kl_lip_of_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {T K : ℝ} (f F : ℝ → V) (a : V)
    (hm : AEStronglyMeasurable f (volume.restrict (Icc 0 T)))
    (hb : ∀ s ∈ Icc (0 : ℝ) T, ‖f s‖ ≤ K)
    (hF : ∀ t ∈ Icc (0 : ℝ) T, F t = a + ∫ s in (0 : ℝ)..t, f s) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, ‖F t - F t'‖ ≤ K * |t - t'| := by
  have hii := kl_intervalIntegrable_of_bound f hm hb
  have key : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, t' ≤ t →
      ‖F t - F t'‖ ≤ K * |t - t'| := by
    intro t ht t' ht' htt
    rw [hF t ht, hF t' ht']
    have : (a + ∫ s in (0 : ℝ)..t, f s) - (a + ∫ s in (0 : ℝ)..t', f s) = ∫ s in t'..t, f s := by
      rw [← intervalIntegral.integral_interval_sub_left (hii t ht) (hii t' ht')]
      simp only [add_sub_add_left_eq_sub]
    rw [this]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := t') (b := t) (f := f) (C := K)
      (fun s hs => by
        rw [uIoc_of_le htt] at hs
        exact hb s ⟨ht'.1.trans hs.1.le, hs.2.trans ht.2⟩)
    exact h1
  intro t ht t' ht'
  rcases le_total t' t with h | h
  · exact key t ht t' ht' h
  · rw [norm_sub_rev, abs_sub_comm]; exact key t' ht' t ht h

/-- Joint continuity from continuity in `x` for fixed `t` and `x`-uniform Lipschitz continuity in `t`. -/
theorem kl_joint_cont_of_time_lip {V : Type*} [NormedAddCommGroup V] {T K : ℝ}
    (F : ℝ → Euc d → V) (hc : ∀ t ∈ Icc (0 : ℝ) T, Continuous (F t))
    (hL : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, ∀ x, ‖F t x - F t' x‖ ≤ K * |t - t'|) :
    ContinuousOn (fun p : ℝ × Euc d => F p.1 p.2) (Icc 0 T ×ˢ univ) := by
  intro p hp
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun q : ℝ × Euc d => K * |q.1 - p.1| + ‖F p.1 q.2 - F p.1 p.2‖)
      (𝓝[Icc 0 T ×ˢ univ] p) (𝓝 0) := by
    have a1 : Tendsto (fun q : ℝ × Euc d => q.1) (𝓝[Icc 0 T ×ˢ univ] p) (𝓝 p.1) :=
      (continuous_fst.tendsto p).mono_left nhdsWithin_le_nhds
    have a2 : Tendsto (fun q : ℝ × Euc d => q.2) (𝓝[Icc 0 T ×ˢ univ] p) (𝓝 p.2) :=
      (continuous_snd.tendsto p).mono_left nhdsWithin_le_nhds
    have b1 : Tendsto (fun q : ℝ × Euc d => K * |q.1 - p.1|) (𝓝[Icc 0 T ×ˢ univ] p) (𝓝 0) := by
      have := ((a1.sub_const p.1).abs).const_mul K
      simpa using this
    have b2 : Tendsto (fun q : ℝ × Euc d => ‖F p.1 q.2 - F p.1 p.2‖) (𝓝[Icc 0 T ×ˢ univ] p)
        (𝓝 0) := by
      have := (((hc p.1 hp.1).tendsto p.2).comp a2).sub_const (F p.1 p.2)
      simpa using this.norm
    simpa using b1.add b2
  refine squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) ?_ h1
  filter_upwards [self_mem_nhdsWithin] with q hq
  calc ‖F q.1 q.2 - F p.1 p.2‖ ≤ ‖F q.1 q.2 - F p.1 q.2‖ + ‖F p.1 q.2 - F p.1 p.2‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by gcongr; exact hL q.1 hq.1 p.1 hp.1 q.2

/-- Joint continuity from `x`-uniform Lipschitz continuity and continuity in `t`. -/
theorem kl_joint_cont_of_x_lip {V : Type*} [NormedAddCommGroup V] {T K : ℝ}
    (F : ℝ → Euc d → V)
    (hx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x y, ‖F t x - F t y‖ ≤ K * ‖x - y‖)
    (ht : ∀ x, ContinuousOn (fun s => F s x) (Icc 0 T)) :
    ContinuousOn (fun p : ℝ × Euc d => F p.1 p.2) (Icc 0 T ×ˢ univ) := by
  intro p hp
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have a1 : Tendsto (fun q : ℝ × Euc d => q.1) (𝓝[Icc 0 T ×ˢ univ] p) (𝓝[Icc 0 T] p.1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto p).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq using hq.1
  have a2 : Tendsto (fun q : ℝ × Euc d => q.2) (𝓝[Icc 0 T ×ˢ univ] p) (𝓝 p.2) :=
    (continuous_snd.tendsto p).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun q : ℝ × Euc d => K * ‖q.2 - p.2‖ + ‖F q.1 p.2 - F p.1 p.2‖)
      (𝓝[Icc 0 T ×ˢ univ] p) (𝓝 0) := by
    have b1 : Tendsto (fun q : ℝ × Euc d => K * ‖q.2 - p.2‖) (𝓝[Icc 0 T ×ˢ univ] p) (𝓝 0) := by
      have := (a2.sub_const p.2).norm.const_mul K
      simpa using this
    have b2 : Tendsto (fun q : ℝ × Euc d => ‖F q.1 p.2 - F p.1 p.2‖) (𝓝[Icc 0 T ×ˢ univ] p)
        (𝓝 0) := by
      have := (((ht p.2 p.1 hp.1).tendsto).comp a1).sub_const (F p.1 p.2)
      simpa using this.norm
    simpa using b1.add b2
  refine squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) ?_ h1
  filter_upwards [self_mem_nhdsWithin] with q hq
  calc ‖F q.1 q.2 - F p.1 p.2‖ ≤ ‖F q.1 q.2 - F q.1 p.2‖ + ‖F q.1 p.2 - F p.1 p.2‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by gcongr; exact hx q.1 hq.1 q.2 p.2

/-- Measurability in the time variable of the `x`-derivative of a jointly continuous family. -/
theorem kl_aesm_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T : ℝ} (hT : 0 ≤ T)
    (g : ℝ → Euc d → V) (hg : ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (Icc 0 T ×ˢ univ))
    (hd : ∀ s ∈ Icc (0 : ℝ) T, Differentiable ℝ (g s)) (x : Euc d) :
    AEStronglyMeasurable (fun s => fderiv ℝ (g s) x) (volume.restrict (Icc 0 T)) := by
  set c : ℝ → ℝ := fun s => max 0 (min s T) with hc
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcm : ∀ s, c s ∈ Icc (0 : ℝ) T := fun s => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcs : ∀ s ∈ Icc (0 : ℝ) T, c s = s := fun s hs => by
    simp [hc, min_eq_left hs.2, max_eq_right hs.1]
  have hG : Continuous (fun p : ℝ × Euc d => g (c p.1) p.2) :=
    hg.comp_continuous ((hcc.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨hcm p.1, mem_univ _⟩)
  have hS := sg_stronglyMeasurable_fderiv (Ω := ℝ) (fun s => g (c s)) hG.stronglyMeasurable
    (fun s => hd _ (hcm s))
  have h2 : StronglyMeasurable (fun s : ℝ => fderiv ℝ (g (c s)) x) :=
    hS.comp_measurable (measurable_id.prodMk measurable_const)
  refine h2.aestronglyMeasurable.congr ?_
  exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => by simp [hcs s hs])

/-- Differentiation under the integral sign for `x ↦ ∫_0^t g s x ds`. -/
theorem kl_hasFDerivAt_intervalIntegral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {T K : ℝ} (hT : 0 ≤ T) (g : ℝ → Euc d → V)
    (hg : ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (Icc 0 T ×ˢ univ))
    (hd : ∀ s ∈ Icc (0 : ℝ) T, Differentiable ℝ (g s))
    (hK : ∀ s ∈ Icc (0 : ℝ) T, ∀ x, ‖fderiv ℝ (g s) x‖ ≤ K) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (x : Euc d) :
    HasFDerivAt (fun x => ∫ s in (0 : ℝ)..t, g s x) (∫ s in (0 : ℝ)..t, fderiv ℝ (g s) x) x := by
  have hsub : Ι (0 : ℝ) t ⊆ Icc 0 T := by
    rw [uIoc_of_le ht.1]; exact fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hcx : ∀ y, ContinuousOn (fun s => g s y) (Icc 0 T) := fun y =>
    hg.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, mem_univ _⟩)
  have hmeas : ∀ y, AEStronglyMeasurable (fun s => g s y) (volume.restrict (Ι (0 : ℝ) t)) := fun y =>
    ((hcx y).aestronglyMeasurable measurableSet_Icc).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (s := univ)
    (F := fun y s => g s y) (F' := fun y s => fderiv ℝ (g s) y) (a := 0) (b := t) (x₀ := x)
    (bound := fun _ => K) Filter.univ_mem (Eventually.of_forall hmeas) ?_ ?_ ?_ ?_ ?_
  · exact ((hcx x).mono (by rw [uIcc_of_le ht.1]; exact fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)).intervalIntegrable
  · exact ((kl_aesm_fderiv hT g hg hd x).mono_measure (Measure.restrict_mono hsub le_rfl))
  · exact (ae_restrict_iff' measurableSet_uIoc).2
      (Eventually.of_forall fun s hs y _ => hK s (hsub hs) y)
  · exact intervalIntegrable_const
  · exact (ae_restrict_iff' measurableSet_uIoc).2
      (Eventually.of_forall fun s hs y _ => (hd s (hsub hs) y).hasFDerivAt)

/-! ### The abstract pathwise setting -/

/-- Hypotheses of the abstract pathwise setting: `φ_t(x) = x + ∫_0^t b(φ_s x) ds + c_t`,
each slice `φ_t` is `C²` with `‖Dφ_t‖ ≤ C1`, `‖D²φ_t‖ ≤ C2`, `t ↦ φ_t(x)` continuous, and
`b` is `C²` with `‖Db‖ ≤ Λ1`, `‖D²b‖ ≤ Λ2`. -/
structure KlPath (T : ℝ) (b : Euc d → Euc d) (c : ℝ → Euc d) (φ : ℝ → Euc d → Euc d)
    (C1 C2 Λ1 Λ2 : ℝ) : Prop where
  hT : 0 ≤ T
  b2 : ContDiff ℝ 2 b
  hb1 : ∀ y, ‖fderiv ℝ b y‖ ≤ Λ1
  hb2 : ∀ y, ‖fderiv ℝ (fderiv ℝ b) y‖ ≤ Λ2
  eq : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, φ t x = x + (∫ s in (0 : ℝ)..t, b (φ s x)) + c t
  cont_t : ∀ x, ContinuousOn (fun s => φ s x) (Icc 0 T)
  c2 : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (φ t)
  bd1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖fderiv ℝ (φ t) x‖ ≤ C1
  bd2 : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖fderiv ℝ (fderiv ℝ (φ t)) x‖ ≤ C2

namespace KlPath

variable {T : ℝ} {b : Euc d → Euc d} {c : ℝ → Euc d} {φ : ℝ → Euc d → Euc d} {C1 C2 Λ1 Λ2 : ℝ}

theorem lip1 (H : KlPath T b c φ C1 C2 Λ1 Λ2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x y : Euc d) :
    ‖φ t x - φ t y‖ ≤ C1 * ‖x - y‖ := by
  have hd : Differentiable ℝ (φ t) := (H.c2 t ht).differentiable (by norm_num)
  exact (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := φ t) (C := C1) (fun x _ => hd x) (fun x _ => H.bd1 t ht x) (mem_univ y) (mem_univ x)

theorem cont_phi (H : KlPath T b c φ C1 C2 Λ1 Λ2) :
    ContinuousOn (fun p : ℝ × Euc d => φ p.1 p.2) (Icc 0 T ×ˢ univ) :=
  kl_joint_cont_of_x_lip φ (fun t ht x y => H.lip1 ht x y) H.cont_t

theorem bd1_nonneg (H : KlPath T b c φ C1 C2 Λ1 Λ2) : 0 ≤ C1 :=
  (norm_nonneg _).trans (H.bd1 0 ⟨le_rfl, H.hT⟩ 0)

theorem bd2_nonneg (H : KlPath T b c φ C1 C2 Λ1 Λ2) : 0 ≤ C2 :=
  (norm_nonneg (fderiv ℝ (fderiv ℝ (φ 0)) 0)).trans (H.bd2 0 ⟨le_rfl, H.hT⟩ 0)

theorem hb1_nonneg (H : KlPath T b c φ C1 C2 Λ1 Λ2) : 0 ≤ Λ1 :=
  (norm_nonneg _).trans (H.hb1 0)

theorem hb2_nonneg (H : KlPath T b c φ C1 C2 Λ1 Λ2) : 0 ≤ Λ2 :=
  (norm_nonneg (fderiv ℝ (fderiv ℝ b) 0)).trans (H.hb2 0)

/-- The integrand `s, x ↦ b (φ s x)`. -/
theorem g1_cont (H : KlPath T b c φ C1 C2 Λ1 Λ2) :
    ContinuousOn (fun p : ℝ × Euc d => b (φ p.1 p.2)) (Icc 0 T ×ˢ univ) :=
  (H.b2.continuous).comp_continuousOn H.cont_phi

theorem g1_fderiv (H : KlPath T b c φ C1 C2 Λ1 Λ2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (x : Euc d) :
    fderiv ℝ (fun y => b (φ s y)) x = (fderiv ℝ b (φ s x)).comp (fderiv ℝ (φ s) x) :=
  fderiv_comp x ((H.b2.differentiable (by norm_num)) _) (((H.c2 s hs).differentiable (by norm_num)) x)

theorem g1_bound (H : KlPath T b c φ C1 C2 Λ1 Λ2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (x : Euc d) :
    ‖fderiv ℝ (fun y => b (φ s y)) x‖ ≤ Λ1 * C1 := by
  rw [H.g1_fderiv hs]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (H.hb1 _) (H.bd1 s hs x) (norm_nonneg _) H.hb1_nonneg)

/-- First variational equation (integral form, operator valued). -/
theorem fderiv_eq (H : KlPath T b c φ C1 C2 Λ1 Λ2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Euc d) :
    fderiv ℝ (φ t) x = ContinuousLinearMap.id ℝ _ +
      ∫ s in (0 : ℝ)..t, fderiv ℝ (fun y => b (φ s y)) x := by
  have h1 := kl_hasFDerivAt_intervalIntegral H.hT (fun s y => b (φ s y)) H.g1_cont
    (fun s hs => ((H.b2.differentiable (by norm_num)).comp ((H.c2 s hs).differentiable (by norm_num))))
    (fun s hs y => H.g1_bound hs y) ht x
  have h2 : HasFDerivAt (φ t) (ContinuousLinearMap.id ℝ _ +
      ∫ s in (0 : ℝ)..t, fderiv ℝ (fun y => b (φ s y)) x) x := by
    have h3 := ((hasFDerivAt_id x).add h1).add_const (c t)
    have e : φ t = fun y => y + (∫ s in (0 : ℝ)..t, b (φ s y)) + c t := funext (H.eq t ht)
    rw [e]; exact h3
  have h4 : HasFDerivAt (φ t) (fderiv ℝ (φ t) x) x :=
    (((H.c2 t ht).differentiable (by norm_num)) x).hasFDerivAt
  exact h4.unique h2

theorem fderiv_lip (H : KlPath T b c φ C1 C2 Λ1 Λ2) (x : Euc d) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (φ t) x - fderiv ℝ (φ t') x‖ ≤ (Λ1 * C1) * |t - t'| :=
  kl_lip_of_integral (fun s => fderiv ℝ (fun y => b (φ s y)) x) (fun t => fderiv ℝ (φ t) x)
    (ContinuousLinearMap.id ℝ _)
    (kl_aesm_fderiv H.hT _ H.g1_cont
      (fun s hs => ((H.b2.differentiable (by norm_num)).comp ((H.c2 s hs).differentiable (by norm_num)))) x)
    (fun s hs => H.g1_bound hs x) (fun t ht => H.fderiv_eq ht x)

theorem cont_fderiv (H : KlPath T b c φ C1 C2 Λ1 Λ2) :
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (φ p.1) p.2) (Icc 0 T ×ˢ univ) :=
  kl_joint_cont_of_time_lip (fun t x => fderiv ℝ (φ t) x)
    (fun t ht => (H.c2 t ht).continuous_fderiv (by norm_num)) (fun t ht t' ht' x => H.fderiv_lip x t ht t' ht')

/-! #### Second variational equation -/

theorem g2_cont (H : KlPath T b c φ C1 C2 Λ1 Λ2) (v : Euc d) :
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ b (φ p.1 p.2) (fderiv ℝ (φ p.1) p.2 v))
      (Icc 0 T ×ˢ univ) :=
  ((H.b2.continuous_fderiv (by norm_num)).comp_continuousOn H.cont_phi).clm_apply
    (H.cont_fderiv.clm_apply continuousOn_const)

theorem g2_hasFDerivAt (H : KlPath T b c φ C1 C2 Λ1 Λ2) (v : Euc d) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : Euc d) :
    HasFDerivAt (fun y => fderiv ℝ b (φ s y) (fderiv ℝ (φ s) y v))
      ((fderiv ℝ b (φ s x)).comp ((ContinuousLinearMap.apply ℝ (Euc d) v).comp
          (fderiv ℝ (fderiv ℝ (φ s)) x)) +
        ((fderiv ℝ (fderiv ℝ b) (φ s x)).comp (fderiv ℝ (φ s) x)).flip (fderiv ℝ (φ s) x v)) x := by
  have hφ : HasFDerivAt (φ s) (fderiv ℝ (φ s) x) x :=
    (((H.c2 s hs).differentiable (by norm_num)) x).hasFDerivAt
  have hb' : HasFDerivAt (fderiv ℝ b) (fderiv ℝ (fderiv ℝ b) (φ s x)) (φ s x) :=
    ((H.b2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _).hasFDerivAt
  have hc : HasFDerivAt (fun y => fderiv ℝ b (φ s y))
      ((fderiv ℝ (fderiv ℝ b) (φ s x)).comp (fderiv ℝ (φ s) x)) x := hb'.comp x hφ
  have hd : HasFDerivAt (fderiv ℝ (φ s)) (fderiv ℝ (fderiv ℝ (φ s)) x) x :=
    (((H.c2 s hs).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have hu : HasFDerivAt (fun y => fderiv ℝ (φ s) y v)
      ((ContinuousLinearMap.apply ℝ (Euc d) v).comp (fderiv ℝ (fderiv ℝ (φ s)) x)) x :=
    (ContinuousLinearMap.apply ℝ (Euc d) v).hasFDerivAt.comp x hd
  exact hc.clm_apply hu

theorem g2_bound (H : KlPath T b c φ C1 C2 Λ1 Λ2) (v : Euc d) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : Euc d) :
    ‖fderiv ℝ (fun y => fderiv ℝ b (φ s y) (fderiv ℝ (φ s) y v)) x‖ ≤
      (Λ1 * C2 + Λ2 * C1 ^ 2) * ‖v‖ := by
  rw [(H.g2_hasFDerivAt v hs x).fderiv]
  have hK : 0 ≤ (Λ1 * C2 + Λ2 * C1 ^ 2) * ‖v‖ := by
    have := H.bd1_nonneg; have := H.bd2_nonneg; have := H.hb1_nonneg; have := H.hb2_nonneg
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun w => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply]
  have e1 : ‖fderiv ℝ b (φ s x) (fderiv ℝ (fderiv ℝ (φ s)) x w v)‖ ≤ Λ1 * (C2 * ‖w‖ * ‖v‖) := by
    refine ((fderiv ℝ b (φ s x)).le_opNorm _).trans ?_
    refine mul_le_mul (H.hb1 _) ?_ (norm_nonneg _) H.hb1_nonneg
    calc ‖fderiv ℝ (fderiv ℝ (φ s)) x w v‖ ≤ ‖fderiv ℝ (fderiv ℝ (φ s)) x‖ * ‖w‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ C2 * ‖w‖ * ‖v‖ := by
          gcongr; exact H.bd2 s hs x
  have e2 : ‖fderiv ℝ (fderiv ℝ b) (φ s x) (fderiv ℝ (φ s) x w) (fderiv ℝ (φ s) x v)‖ ≤
      Λ2 * (C1 * ‖w‖) * (C1 * ‖v‖) := by
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ b) (φ s x)‖ * ‖fderiv ℝ (φ s) x w‖ * ‖fderiv ℝ (φ s) x v‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ Λ2 * (C1 * ‖w‖) * (C1 * ‖v‖) := by
          have h1 : ‖fderiv ℝ (φ s) x w‖ ≤ C1 * ‖w‖ :=
            ((fderiv ℝ (φ s) x).le_opNorm w).trans (mul_le_mul_of_nonneg_right (H.bd1 s hs x) (norm_nonneg _))
          have h2 : ‖fderiv ℝ (φ s) x v‖ ≤ C1 * ‖v‖ :=
            ((fderiv ℝ (φ s) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (H.bd1 s hs x) (norm_nonneg _))
          have := H.hb2 (φ s x)
          have := H.hb2_nonneg; have := H.bd1_nonneg
          gcongr
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ Λ1 * (C2 * ‖w‖ * ‖v‖) + Λ2 * (C1 * ‖w‖) * (C1 * ‖v‖) := add_le_add e1 e2
    _ = (Λ1 * C2 + Λ2 * C1 ^ 2) * ‖v‖ * ‖w‖ := by ring

theorem g2_diff (H : KlPath T b c φ C1 C2 Λ1 Λ2) (v : Euc d) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    Differentiable ℝ (fun y => fderiv ℝ b (φ s y) (fderiv ℝ (φ s) y v)) :=
  fun x => (H.g2_hasFDerivAt v hs x).differentiableAt

theorem g1_aesm (H : KlPath T b c φ C1 C2 Λ1 Λ2) (x : Euc d) :
    AEStronglyMeasurable (fun s => fderiv ℝ (fun y => b (φ s y)) x) (volume.restrict (Icc 0 T)) :=
  kl_aesm_fderiv H.hT _ H.g1_cont
    (fun s hs => ((H.b2.differentiable (by norm_num)).comp ((H.c2 s hs).differentiable (by norm_num)))) x

theorem fderiv_eq_v (H : KlPath T b c φ C1 C2 Λ1 Λ2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (v x : Euc d) :
    fderiv ℝ (φ t) x v = v + ∫ s in (0 : ℝ)..t, fderiv ℝ b (φ s x) (fderiv ℝ (φ s) x v) := by
  have hint := kl_intervalIntegrable_of_bound _ (H.g1_aesm x) (fun s hs => H.g1_bound hs x) t ht
  rw [H.fderiv_eq ht x, ContinuousLinearMap.add_apply, ContinuousLinearMap.intervalIntegral_apply hint]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  rw [H.g1_fderiv ⟨hs.1, hs.2.trans ht.2⟩]
  rfl

theorem d2_eq (H : KlPath T b c φ C1 C2 Λ1 Λ2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (v x : Euc d) :
    (ContinuousLinearMap.apply ℝ (Euc d) v).comp (fderiv ℝ (fderiv ℝ (φ t)) x) =
      ∫ s in (0 : ℝ)..t, fderiv ℝ (fun y => fderiv ℝ b (φ s y) (fderiv ℝ (φ s) y v)) x := by
  have h1 := kl_hasFDerivAt_intervalIntegral H.hT
    (fun s y => fderiv ℝ b (φ s y) (fderiv ℝ (φ s) y v)) (H.g2_cont v) (fun s hs => H.g2_diff v hs)
    (fun s hs y => H.g2_bound v hs y) ht x
  have h2 : HasFDerivAt (fun y => fderiv ℝ (φ t) y v)
      (∫ s in (0 : ℝ)..t, fderiv ℝ (fun y => fderiv ℝ b (φ s y) (fderiv ℝ (φ s) y v)) x) x := by
    have e : (fun y => fderiv ℝ (φ t) y v) = fun y =>
        v + ∫ s in (0 : ℝ)..t, fderiv ℝ b (φ s y) (fderiv ℝ (φ s) y v) :=
      funext fun y => H.fderiv_eq_v ht v y
    rw [e]; exact h1.const_add v
  have hd : HasFDerivAt (fderiv ℝ (φ t)) (fderiv ℝ (fderiv ℝ (φ t)) x) x :=
    (((H.c2 t ht).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  exact ((ContinuousLinearMap.apply ℝ (Euc d) v).hasFDerivAt.comp x hd).unique h2

theorem fderiv2_lip (H : KlPath T b c φ C1 C2 Λ1 Λ2) (x : Euc d) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T,
      ‖fderiv ℝ (fderiv ℝ (φ t)) x - fderiv ℝ (fderiv ℝ (φ t')) x‖ ≤
        (Λ1 * C2 + Λ2 * C1 ^ 2) * |t - t'| := by
  have hK : 0 ≤ Λ1 * C2 + Λ2 * C1 ^ 2 := by
    have := H.bd1_nonneg; have := H.bd2_nonneg; have := H.hb1_nonneg; have := H.hb2_nonneg
    positivity
  have hv : ∀ v : Euc d, ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T,
      ‖(ContinuousLinearMap.apply ℝ (Euc d) v).comp (fderiv ℝ (fderiv ℝ (φ t)) x) -
        (ContinuousLinearMap.apply ℝ (Euc d) v).comp (fderiv ℝ (fderiv ℝ (φ t')) x)‖ ≤
        ((Λ1 * C2 + Λ2 * C1 ^ 2) * ‖v‖) * |t - t'| := by
    intro v
    refine kl_lip_of_integral (fun s => fderiv ℝ (fun y => fderiv ℝ b (φ s y) (fderiv ℝ (φ s) y v)) x)
      (fun t => (ContinuousLinearMap.apply ℝ (Euc d) v).comp (fderiv ℝ (fderiv ℝ (φ t)) x)) 0
      (kl_aesm_fderiv H.hT _ (H.g2_cont v) (fun s hs => H.g2_diff v hs) x)
      (fun s hs => H.g2_bound v hs x) (fun t ht => ?_)
    rw [zero_add]; exact H.d2_eq ht v x
  intro t ht t' ht'
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (abs_nonneg _)) fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hK (abs_nonneg _)) (norm_nonneg _))
    fun v => ?_
  have h1 := (ContinuousLinearMap.le_opNorm _ w).trans
    (mul_le_mul_of_nonneg_right (hv v t ht t' ht') (norm_nonneg w))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] at h1 ⊢
  calc _ ≤ _ := h1
    _ = _ := by ring

theorem cont_fderiv2 (H : KlPath T b c φ C1 C2 Λ1 Λ2) :
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ (φ p.1)) p.2) (Icc 0 T ×ˢ univ) :=
  kl_joint_cont_of_time_lip (fun t x => fderiv ℝ (fderiv ℝ (φ t)) x)
    (fun t ht => ((H.c2 t ht).fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num))
    (fun t ht t' ht' x => H.fderiv2_lip x t ht t' ht')

end KlPath

/-! ### Instantiation to `flowMap` -/

theorem kl_norm_fderiv_fderiv' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Euc d → V} (x : Euc d) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

/-- The drift `b y = -q y + B y` has `‖Db‖ ≤ q + Mb`, `‖D²b‖ ≤ Mb`. -/
theorem kl_drift_bounds {q Mb : ℝ} (hq : 0 ≤ q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) :
    ContDiff ℝ 2 (fun y : Euc d => -q • y + B y) ∧
    (∀ y, ‖fderiv ℝ (fun y : Euc d => -q • y + B y) y‖ ≤ q + Mb) ∧
    (∀ y, ‖fderiv ℝ (fderiv ℝ (fun y : Euc d => -q • y + B y)) y‖ ≤ Mb) := by
  have hm2 : ((2 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hm
  have hB2 : ContDiff ℝ 2 B := hB.1.of_le (by exact_mod_cast hm2)
  have hBd : Differentiable ℝ B := hB.1.differentiable (by exact_mod_cast (by omega : m ≠ 0))
  have hfd : ∀ y, fderiv ℝ (fun y : Euc d => -q • y + B y) y =
      -q • ContinuousLinearMap.id ℝ (Euc d) + fderiv ℝ B y := fun y => by
    exact (((hasFDerivAt_id y).const_smul (-q)).add (hBd y).hasFDerivAt).fderiv
  refine ⟨(contDiff_id.const_smul (-q)).add hB2, fun y => ?_, fun y => ?_⟩
  · rw [hfd]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖-q • ContinuousLinearMap.id ℝ (Euc d)‖ = |q| * ‖ContinuousLinearMap.id ℝ (Euc d)‖ := by
            rw [norm_smul, norm_neg, Real.norm_eq_abs]
        _ ≤ |q| * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)
        _ = q := by rw [mul_one, abs_of_nonneg hq]
    · rw [← norm_iteratedFDeriv_one]; exact hB.2 1 (by omega) y
  · have : fderiv ℝ (fderiv ℝ (fun y : Euc d => -q • y + B y)) y = fderiv ℝ (fderiv ℝ B) y := by
      rw [show fderiv ℝ (fun y : Euc d => -q • y + B y) = fun y =>
        -q • ContinuousLinearMap.id ℝ (Euc d) + fderiv ℝ B y from funext hfd]
      exact fderiv_const_add _
    rw [this, kl_norm_fderiv_fderiv']
    exact hB.2 2 hm y

/-- **Pathwise regularity of the flow.**  For `T ≥ 0` there are constants (depending only on
`(d, q, Mb, m, T)`) such that for every `B` with `HasCbBound m Mb B` and every continuous noise path
`w` with `w 0 = 0`, the flow `flowMap q B w` is in the abstract setting `KlPath`. -/
theorem kl_flow_path (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Euc d → Euc d, HasCbBound m Mb B → ∀ w : ℝ≥0 → Fin d → ℝ,
      Continuous w → w 0 = 0 →
      KlPath T (fun y => -q • y + B y) (fun t => ∑ k, w (Real.toNNReal t) k • pfSigma d k)
        (flowMap q B w) C C (q + Mb) Mb := by
  obtain ⟨C, hC, hflow⟩ := pois_flow (d := d) q Mb hq m hm T hT
  refine ⟨C, hC, fun B hB w hw hw0 => ?_⟩
  obtain ⟨hps, hreg⟩ := hflow B hB w hw hw0
  obtain ⟨hb2, hb1, hb2'⟩ := kl_drift_bounds hq.le hm hB
  have hm2 : ((2 : ℕ) : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hm
  refine ⟨hT, hb2, hb1, hb2', fun t ht x => ?_, fun x => ?_, fun t ht => ?_, fun t ht x => ?_,
    fun t ht x => ?_⟩
  · have h := ((hps x).2 t ht.1 (WithTop.coe_lt_top t)).2.2
    rw [setIntegral_Icc_eq_interval ht.1] at h
    exact h
  · exact ((hps x).2 T hT (WithTop.coe_lt_top T)).1
  · exact (hreg t ht).1.of_le (by exact_mod_cast hm2)
  · have := (hreg t ht).2 1 le_rfl (by omega) x
    rwa [norm_iteratedFDeriv_one] at this
  · have := (hreg t ht).2 2 (by omega) hm x
    rwa [← kl_norm_fderiv_fderiv'] at this

end HRS.MS.PoisKolm
