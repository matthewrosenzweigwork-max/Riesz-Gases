import HRS.MS.SA16EvolDefs

/-!
# S.A.16 E5: `volterra_bounded_perturbation`

Elementary bounded perturbation of a strongly continuous propagator.  The solution is the Neumann series
`u = ∑ vₙ`, `v₀ t = S t 0 x₀ + ∫₀ᵗ S t r f r dr`, `vₙ₊₁ t = ∫₀ᵗ S t r (A r (vₙ r)) dr`, with
`‖vₙ t‖ ≤ a(t) (M K t)ⁿ / n!`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA

/-! ### measurability of `r ↦ F r (g r)` for a strongly measurable family of bounded operators -/

lemma sa16e_aesm_simple {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {μ : Measure ℝ} (F : ℝ → X →L[ℝ] Y)
    (hF : ∀ y, AEStronglyMeasurable (fun r => F r y) μ) (s : SimpleFunc ℝ X) :
    AEStronglyMeasurable (fun r => F r (s r)) μ := by
  induction s using SimpleFunc.induction with
  | @const c S hS =>
    have : (fun r => F r ((SimpleFunc.piecewise S hS (SimpleFunc.const ℝ c)
        (SimpleFunc.const ℝ 0)) r)) = Set.indicator S (fun r => F r c) := by
      funext r
      by_cases h : r ∈ S
      · simp [SimpleFunc.coe_piecewise, Set.piecewise, Set.indicator, h]
      · simp [SimpleFunc.coe_piecewise, Set.piecewise, Set.indicator, h]
    rw [this]
    exact (hF c).indicator hS
  | @add f g hdisj hf hg =>
    have : (fun r => F r ((f + g : SimpleFunc ℝ X) r)) = fun r => F r (f r) + F r (g r) := by
      funext r
      simp
    rw [this]
    exact hf.add hg

lemma sa16e_aesm_apply {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {μ : Measure ℝ} (F : ℝ → X →L[ℝ] Y)
    (hF : ∀ y, AEStronglyMeasurable (fun r => F r y) μ) {g : ℝ → X}
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (fun r => F r (g r)) μ := by
  have h1 : AEStronglyMeasurable (fun r => F r (hg.mk g r)) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => sa16e_aesm_simple F hF (hg.stronglyMeasurable_mk.approx n))
      (Eventually.of_forall fun r => ((F r).continuous.tendsto _).comp
        (hg.stronglyMeasurable_mk.tendsto_approx r))
  refine h1.congr ?_
  filter_upwards [hg.ae_eq_mk] with r hr
  rw [hr]


section Volterra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- the propagator applied to a strongly measurable integrand is strongly measurable on `[0,t]` -/
lemma sa16e_S_aesm {T : ℝ} (S : ℝ → ℝ → X →L[ℝ] X)
    (hS : ∀ x, ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 x)
      {q | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}) {t : ℝ} (ht : t ≤ T) {g : ℝ → X}
    (hg : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) t))) :
    AEStronglyMeasurable (fun r => S t r (g r)) (volume.restrict (Icc (0 : ℝ) t)) := by
  refine sa16e_aesm_apply (S t) (fun y => ?_) hg
  have h1 : ContinuousOn (fun r : ℝ => S t r y) (Icc (0 : ℝ) t) :=
    (hS y).comp (continuousOn_const.prodMk continuousOn_id) (fun r hr => ⟨hr.1, hr.2, ht⟩)
  exact h1.aestronglyMeasurable measurableSet_Icc

/-- the Volterra operator -/
def sa16e_V (S : ℝ → ℝ → X →L[ℝ] X) (g : ℝ → X) (t : ℝ) : X :=
  ∫ r in Icc (0 : ℝ) t, S t r (g r)

lemma sa16e_int {T M : ℝ} (S : ℝ → ℝ → X →L[ℝ] X)
    (hS : ∀ x, ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 x)
      {q | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T})
    (hSb : ∀ r t, 0 ≤ r → r ≤ t → t ≤ T → ‖S t r‖ ≤ M) {g : ℝ → X}
    (hg : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) T))) {Cg : ℝ}
    (hgb : ∀ r ∈ Icc (0 : ℝ) T, ‖g r‖ ≤ Cg) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Integrable (fun r => S t r (g r)) (volume.restrict (Icc (0 : ℝ) t)) := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl ht.2
  have hgt : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) t)) :=
    hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hm := sa16e_S_aesm S hS ht.2 hgt
  refine Integrable.mono' (g := fun _ => M * |Cg|) (integrable_const _) hm ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hSb 0 0 le_rfl le_rfl (ht.1.trans ht.2))
  exact ((S t r).le_opNorm _).trans ((mul_le_mul_of_nonneg_right
    (hSb r t hr.1 hr.2 ht.2) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((hgb r (hsub hr)).trans (le_abs_self Cg)) hM))

lemma sa16e_V_norm_le {T M : ℝ} (S : ℝ → ℝ → X →L[ℝ] X)
    (hS : ∀ x, ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 x)
      {q | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T})
    (hSb : ∀ r t, 0 ≤ r → r ≤ t → t ≤ T → ‖S t r‖ ≤ M) {g : ℝ → X}
    (hg : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) T))) {Cg : ℝ}
    (hgb : ∀ r ∈ Icc (0 : ℝ) T, ‖g r‖ ≤ Cg) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (h : ℝ → ℝ) (hh : IntegrableOn h (Icc (0 : ℝ) t))
    (hgh : ∀ r ∈ Icc (0 : ℝ) t, ‖g r‖ ≤ h r) :
    ‖sa16e_V S g t‖ ≤ ∫ r in Icc (0 : ℝ) t, M * h r := by
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl ht.2
  unfold sa16e_V
  refine norm_integral_le_of_norm_le (hh.const_mul M) ((ae_restrict_iff' measurableSet_Icc).2
    (Eventually.of_forall fun r hr => ?_))
  exact ((S t r).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (hSb r t hr.1 hr.2 ht.2) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hgh r hr)
        (le_trans (norm_nonneg _) (hSb 0 0 le_rfl le_rfl (ht.1.trans ht.2)))))

lemma sa16e_V_cont {T M : ℝ} (S : ℝ → ℝ → X →L[ℝ] X)
    (hS : ∀ x, ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 x)
      {q | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T})
    (hSb : ∀ r t, 0 ≤ r → r ≤ t → t ≤ T → ‖S t r‖ ≤ M) {g : ℝ → X}
    (hg : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) T))) {Cg : ℝ}
    (hgb : ∀ r ∈ Icc (0 : ℝ) T, ‖g r‖ ≤ Cg) :
    ContinuousOn (sa16e_V S g) (Icc (0 : ℝ) T) := by
  intro t₀ ht₀
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hSb 0 0 le_rfl le_rfl (ht₀.1.trans ht₀.2))
  set μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hμ
  set F : ℝ → ℝ → X := fun t r => (Icc (0 : ℝ) t).indicator (fun r => S t r (g r)) r with hF
  have hV : ∀ t ∈ Icc (0 : ℝ) T, sa16e_V S g t = ∫ r, F t r ∂μ := by
    intro t ht
    unfold sa16e_V
    rw [hμ, hF, setIntegral_indicator measurableSet_Icc,
      inter_eq_right.2 (Icc_subset_Icc le_rfl ht.2)]
  have hlim : Tendsto (fun t => ∫ r, F t r ∂μ) (𝓝[Icc (0 : ℝ) T] t₀)
      (𝓝 (∫ r, F t₀ r ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => M * |Cg|) ?_ ?_
      (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hF]
      refine (aestronglyMeasurable_indicator_iff measurableSet_Icc).2 ?_
      rw [hμ, Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.2 (Icc_subset_Icc le_rfl ht.2)]
      exact sa16e_S_aesm S hS ht.2 (hg.mono_measure (Measure.restrict_mono
        (Icc_subset_Icc le_rfl ht.2) le_rfl))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
      show ‖(Icc (0 : ℝ) t).indicator (fun r => S t r (g r)) r‖ ≤ M * |Cg|
      by_cases hrt : r ∈ Icc (0 : ℝ) t
      · rw [Set.indicator_of_mem hrt]
        exact ((S t r).le_opNorm _).trans ((mul_le_mul_of_nonneg_right
          (hSb r t hrt.1 hrt.2 ht.2) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left ((hgb r hr).trans (le_abs_self Cg)) hM))
      · rw [Set.indicator_of_notMem hrt]
        simp only [norm_zero]
        exact mul_nonneg hM (abs_nonneg _)
    · have hae1 : ∀ᵐ r ∂μ, r ∈ Icc (0 : ℝ) T := ae_restrict_mem measurableSet_Icc
      have hae2 : ∀ᵐ r ∂μ, r ∉ ({t₀} : Set ℝ) :=
        ae_restrict_of_ae ((Set.countable_singleton t₀).ae_notMem volume)
      filter_upwards [hae1, hae2] with r hr hne
      have hne' : r ≠ t₀ := fun h => hne (by simp [h])
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · -- r < t₀
        have hev : ∀ᶠ t in 𝓝[Icc (0 : ℝ) T] t₀, r < t :=
          nhdsWithin_le_nhds (Ioi_mem_nhds hlt)
        have hmem : ∀ᶠ t in 𝓝[Icc (0 : ℝ) T] t₀, (t, r) ∈ {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} := by
          filter_upwards [hev, self_mem_nhdsWithin] with t h1 h2
          exact ⟨hr.1, h1.le, h2.2⟩
        have ht1 : Tendsto (fun t : ℝ => (t, r)) (𝓝[Icc (0 : ℝ) T] t₀)
            (𝓝[{q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}] (t₀, r)) :=
          tendsto_nhdsWithin_iff.2 ⟨((continuous_id.prodMk continuous_const).tendsto t₀).mono_left
            nhdsWithin_le_nhds, hmem⟩
        have ht2 := (hS (g r) (t₀, r) (show (t₀, r) ∈ {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}
          from ⟨hr.1, hlt.le, ht₀.2⟩)).tendsto.comp ht1
        have hF0 : F t₀ r = S t₀ r (g r) := by
          have hm : r ∈ Icc (0 : ℝ) t₀ := ⟨hr.1, hlt.le⟩
          rw [hF]; exact Set.indicator_of_mem hm (fun r => S t₀ r (g r))
        rw [hF0]
        refine ht2.congr' ?_
        filter_upwards [hev] with t h1
        show S t r (g r) = (Icc (0 : ℝ) t).indicator (fun r => S t r (g r)) r
        have hm : r ∈ Icc (0 : ℝ) t := ⟨hr.1, h1.le⟩
        exact (Set.indicator_of_mem hm (fun r => S t r (g r))).symm
      · -- r > t₀
        have hev : ∀ᶠ t in 𝓝[Icc (0 : ℝ) T] t₀, t < r :=
          nhdsWithin_le_nhds (Iio_mem_nhds hgt)
        have hF0 : F t₀ r = 0 := by
          rw [hF]; exact Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 hgt)) _
        rw [hF0]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with t h1
        show (0 : X) = (Icc (0 : ℝ) t).indicator (fun r => S t r (g r)) r
        exact (Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 h1)) _).symm
  show Tendsto (sa16e_V S g) (𝓝[Icc (0 : ℝ) T] t₀) (𝓝 (sa16e_V S g t₀))
  rw [hV t₀ ht₀]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hV t ht).symm



lemma sa16e_int_pow (t : ℝ) (ht : 0 ≤ t) (c : ℝ) (n : ℕ) :
    ∫ r in Icc (0 : ℝ) t, c * r ^ n = c * t ^ (n + 1) / (n + 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_const_mul, integral_pow]
  simp
  ring

end Volterra

theorem volterra_bounded_perturbation {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T M K : ℝ) (hT : 0 ≤ T) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (S : ℝ → ℝ → X →L[ℝ] X)
    (hS : ∀ x, ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 x)
      {q | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T})
    (hSb : ∀ r t, 0 ≤ r → r ≤ t → t ≤ T → ‖S t r‖ ≤ M)
    (A : ℝ → X →L[ℝ] X)
    (hA : ∀ x : X, AEStronglyMeasurable (fun r => A r x)
      (volume.restrict (Icc (0 : ℝ) T)))
    (hAb : ∀ t ∈ Icc (0 : ℝ) T, ‖A t‖ ≤ K)
    (f : ℝ → X) (hf : ContinuousOn f (Icc (0 : ℝ) T)) (x₀ : X) :
    ∃ u : ℝ → X, ContinuousOn u (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        u t=S t 0 x₀+∫ r in Icc (0 : ℝ) t, S t r (A r (u r)+f r)) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖u t‖ ≤ M*Real.exp (M*K*t)*(‖x₀‖+∫ r in Icc (0 : ℝ) t, ‖f r‖) := by
  classical
  have hM0 : 0 ≤ M := by linarith
  set I : Set ℝ := Icc (0 : ℝ) T with hI
  set a : ℝ → ℝ := fun t => M * (‖x₀‖ + ∫ r in Icc (0 : ℝ) t, ‖f r‖) with ha
  have hfn_int : ∀ t ∈ I, IntegrableOn (fun r => ‖f r‖) (Icc (0 : ℝ) t) := fun t ht =>
    (hf.norm.integrableOn_Icc).mono_set (Icc_subset_Icc le_rfl ht.2)
  have hint_nonneg : ∀ t, 0 ≤ ∫ r in Icc (0 : ℝ) t, ‖f r‖ := fun t =>
    setIntegral_nonneg measurableSet_Icc fun r _ => norm_nonneg _
  have ha_nonneg : ∀ t, 0 ≤ a t := fun t =>
    mul_nonneg hM0 (add_nonneg (norm_nonneg _) (hint_nonneg t))
  have ha_mono : ∀ s t, s ≤ t → t ∈ I → a s ≤ a t := by
    intro s t hst ht
    simp only [ha]
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hM0
    exact setIntegral_mono_set (hfn_int t ht) (Eventually.of_forall fun r => norm_nonneg _)
      (Icc_subset_Icc le_rfl hst).eventuallyLE
  have hf_aesm : AEStronglyMeasurable f (volume.restrict I) :=
    hf.aestronglyMeasurable measurableSet_Icc
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  -- the iterates
  let v : ℕ → ℝ → X := fun n => Nat.rec (motive := fun _ => ℝ → X)
    (fun t => S t 0 x₀ + sa16e_V S f t)
    (fun _ vn t => sa16e_V S (fun r => A r (vn r)) t) n
  have hv0 : v 0 = fun t => S t 0 x₀ + sa16e_V S f t := rfl
  have hvs : ∀ n, v (n + 1) = fun t => sa16e_V S (fun r => A r (v n r)) t := fun n => rfl
  have key : ∀ n : ℕ, ContinuousOn (v n) I ∧
      ∀ t ∈ I, ‖v n t‖ ≤ a t * (M * K * t) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, fun t ht => ?_⟩
      · rw [hv0]
        have h1 : ContinuousOn (fun t => S t 0 x₀) I :=
          (hS x₀).comp (continuousOn_id.prodMk continuousOn_const)
            (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)
        exact h1.add (sa16e_V_cont S hS hSb hf_aesm hCf)
      · rw [hv0]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
        refine (norm_add_le _ _).trans ?_
        have e1 : ‖S t 0 x₀‖ ≤ M * ‖x₀‖ := ((S t 0).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hSb 0 t le_rfl ht.1 ht.2) (norm_nonneg _))
        have e2 := sa16e_V_norm_le S hS hSb hf_aesm hCf ht (fun r => ‖f r‖) (hfn_int t ht)
          (fun r _ => le_rfl)
        rw [integral_const_mul] at e2
        simp only [ha]
        nlinarith
    | succ n ih =>
      obtain ⟨hc, hb⟩ := ih
      have hv_aesm : AEStronglyMeasurable (v n) (volume.restrict I) :=
        hc.aestronglyMeasurable measurableSet_Icc
      have hg_aesm : AEStronglyMeasurable (fun r => A r (v n r)) (volume.restrict I) :=
        sa16e_aesm_apply A hA hv_aesm
      obtain ⟨Cn, hCn⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
      have hgb : ∀ r ∈ I, ‖A r (v n r)‖ ≤ K * Cn := fun r hr =>
        ((A r).le_opNorm _).trans (mul_le_mul (hAb r hr) (hCn r hr) (norm_nonneg _) hK)
      rw [hvs n]
      refine ⟨sa16e_V_cont S hS hSb hg_aesm hgb, fun t ht => ?_⟩
      have hbd : ∀ r ∈ Icc (0 : ℝ) t, ‖A r (v n r)‖ ≤
          K * (a t * (M * K * r) ^ n / (n.factorial : ℝ)) := by
        intro r hr
        have hrI : r ∈ I := ⟨hr.1, hr.2.trans ht.2⟩
        have h1 := hb r hrI
        have h2 : a r * (M * K * r) ^ n / (n.factorial : ℝ) ≤
            a t * (M * K * r) ^ n / (n.factorial : ℝ) := by
          have : 0 ≤ (M * K * r) ^ n / (n.factorial : ℝ) := by
            have : 0 ≤ M * K * r := mul_nonneg (mul_nonneg hM0 hK) hr.1
            positivity
          calc a r * (M * K * r) ^ n / (n.factorial : ℝ)
              = a r * ((M * K * r) ^ n / (n.factorial : ℝ)) := by ring
            _ ≤ a t * ((M * K * r) ^ n / (n.factorial : ℝ)) :=
                mul_le_mul_of_nonneg_right (ha_mono r t hr.2 ht) this
            _ = a t * (M * K * r) ^ n / (n.factorial : ℝ) := by ring
        exact ((A r).le_opNorm _).trans (mul_le_mul (hAb r hrI) (h1.trans h2) (norm_nonneg _) hK)
      have hcont : Continuous (fun r : ℝ => K * (a t * (M * K * r) ^ n / (n.factorial : ℝ))) := by
        fun_prop
      have := sa16e_V_norm_le S hS hSb hg_aesm hgb ht
        (fun r => K * (a t * (M * K * r) ^ n / (n.factorial : ℝ)))
        (hcont.continuousOn.integrableOn_Icc) hbd
      refine this.trans (le_of_eq ?_)
      have e : ∀ r : ℝ, M * (K * (a t * (M * K * r) ^ n / (n.factorial : ℝ))) =
          (M * (K * (a t * (M * K) ^ n / (n.factorial : ℝ)))) * r ^ n := by
        intro r
        rw [mul_pow]
        ring
      simp_rw [e]
      rw [sa16e_int_pow t ht.1]
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
  have hcont : ∀ n, ContinuousOn (v n) I := fun n => (key n).1
  have hnorm : ∀ n, ∀ t ∈ I, ‖v n t‖ ≤ a t * (M * K * t) ^ n / (n.factorial : ℝ) :=
    fun n => (key n).2
  set B : ℕ → ℝ := fun n => a T * (M * K * T) ^ n / (n.factorial : ℝ) with hB
  have hMK0 : 0 ≤ M * K := mul_nonneg hM0 hK
  have hBsum : Summable B := by
    have := (Real.summable_pow_div_factorial (M * K * T)).mul_left (a T)
    refine this.congr fun n => ?_
    simp only [hB]
    ring
  have hBb : ∀ n, ∀ t ∈ I, ‖v n t‖ ≤ B n := by
    intro n t ht
    refine (hnorm n t ht).trans ?_
    have h1 : a t ≤ a T := ha_mono t T ht.2 ⟨hT, le_rfl⟩
    have h2 : (M * K * t) ^ n ≤ (M * K * T) ^ n :=
      pow_le_pow_left₀ (mul_nonneg hMK0 ht.1) (mul_le_mul_of_nonneg_left ht.2 hMK0) n
    have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.2 (Nat.factorial_pos n)
    simp only [hB]
    rw [div_le_div_iff_of_pos_right hfac]
    exact mul_le_mul h1 h2 (pow_nonneg (mul_nonneg hMK0 ht.1) n) (ha_nonneg T)
  set u : ℝ → X := fun t => ∑' n, v n t with hu
  have hsum : ∀ t ∈ I, HasSum (fun n => v n t) (u t) := fun t ht =>
    (Summable.of_norm_bounded hBsum (fun n => hBb n t ht)).hasSum
  have hu_cont : ContinuousOn u I := continuousOn_tsum hcont hBsum hBb
  refine ⟨u, hu_cont, ?_, ?_⟩
  · intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ I := Icc_subset_Icc le_rfl ht.2
    have hu_aesm : AEStronglyMeasurable u (volume.restrict I) :=
      hu_cont.aestronglyMeasurable measurableSet_Icc
    obtain ⟨Cu, hCu⟩ := isCompact_Icc.exists_bound_of_continuousOn hu_cont
    have hAu_aesm : AEStronglyMeasurable (fun r => A r (u r)) (volume.restrict I) :=
      sa16e_aesm_apply A hA hu_aesm
    have hAub : ∀ r ∈ I, ‖A r (u r)‖ ≤ K * Cu := fun r hr =>
      ((A r).le_opNorm _).trans (mul_le_mul (hAb r hr) (hCu r hr) (norm_nonneg _) hK)
    have hmain : HasSum (fun n => ∫ r in Icc (0 : ℝ) t, S t r (A r (v n r)))
        (∫ r in Icc (0 : ℝ) t, S t r (A r (u r))) := by
      refine hasSum_integral_of_dominated_convergence (fun n _ => M * K * B n)
        (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
      · have hvn_aesm : AEStronglyMeasurable (v n) (volume.restrict I) :=
          (hcont n).aestronglyMeasurable measurableSet_Icc
        have hg : AEStronglyMeasurable (fun r => A r (v n r)) (volume.restrict (Icc (0 : ℝ) t)) :=
          (sa16e_aesm_apply A hA hvn_aesm).mono_measure (Measure.restrict_mono hsub le_rfl)
        exact sa16e_S_aesm S hS ht.2 hg
      · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
        have h1 : ‖A r (v n r)‖ ≤ K * B n :=
          ((A r).le_opNorm _).trans (mul_le_mul (hAb r (hsub hr)) (hBb n r (hsub hr))
            (norm_nonneg _) hK)
        calc ‖S t r (A r (v n r))‖ ≤ ‖S t r‖ * ‖A r (v n r)‖ := (S t r).le_opNorm _
          _ ≤ M * (K * B n) := mul_le_mul (hSb r t hr.1 hr.2 ht.2) h1 (norm_nonneg _) hM0
          _ = M * K * B n := by ring
      · exact Eventually.of_forall fun r => hBsum.mul_left (M * K)
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact ((S t r).comp (A r)).hasSum (hsum r (hsub hr))
    have hv_eq : ∀ n, ∫ r in Icc (0 : ℝ) t, S t r (A r (v n r)) = v (n + 1) t := fun n => by
      rw [hvs n]; rfl
    have h1 : ∑' n, v (n + 1) t = ∫ r in Icc (0 : ℝ) t, S t r (A r (u r)) := by
      have := hmain.tsum_eq
      simpa only [hv_eq] using this
    have h2 : u t = v 0 t + ∑' n, v (n + 1) t := (hsum t ht).summable.tsum_eq_zero_add
    have hiA := sa16e_int S hS hSb hAu_aesm hAub ht
    have hif := sa16e_int S hS hSb hf_aesm hCf ht
    have hsplit : (∫ r in Icc (0 : ℝ) t, S t r (A r (u r) + f r)) =
        (∫ r in Icc (0 : ℝ) t, S t r (A r (u r))) + ∫ r in Icc (0 : ℝ) t, S t r (f r) := by
      rw [← integral_add hiA hif]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp
    rw [hsplit, h2, h1, hv0]
    simp only [sa16e_V]
    abel
  · intro t ht
    have hg : HasSum (fun n => a t * (M * K * t) ^ n / (n.factorial : ℝ))
        (a t * Real.exp (M * K * t)) := by
      have h0 := (NormedSpace.expSeries_div_hasSum_exp (M * K * t)).mul_left (a t)
      rw [← Real.exp_eq_exp_ℝ] at h0
      refine h0.congr_fun fun n => ?_
      ring
    have := tsum_of_norm_bounded hg (fun n => hnorm n t ht)
    calc ‖u t‖ ≤ a t * Real.exp (M * K * t) := this
      _ = M * Real.exp (M * K * t) * (‖x₀‖ + ∫ r in Icc (0 : ℝ) t, ‖f r‖) := by
          simp only [ha]; ring

end HRS.Whole.AppendixA.Phase2SA16Evolution
