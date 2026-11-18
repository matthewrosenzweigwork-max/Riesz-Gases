import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Positive
import HRS.PDE.ToolboxRd.Fourier

/-!
# Sub-Coulomb commutator on `ℝ^d`: control by the modulated energy (Section 2.2 of the note)

Source `[N]`: Section 2.2 (L324-374), Lemma 2.2 `lem:energy-control` (L327-342), proof (L344-374);
the coercivity (3.Scoercive) (L395-407) and `(1.intro-control)` (L177-184).  Packet `CMX-EN`.

Throughout (L325): `μ = ρ` is bounded, compactly supported, of mass one, of either sign
(`BddCptDensity`); `p > d/(d-s)`; `ν = μ_N - μ` is `chargeOf X ρ`; `Ec = F_N + C_p(1/N + ‖μ‖_{L^p})`
(`(1.intro-control)`, L182).  Quantifiers (L239: "Unless indicated otherwise, the implicit constants
depend only on `d, s`; dependence on the density exponent is indicated by `C_p`"): the constant
`C_b` of `≲` is chosen before `p`; `C_p` ("sufficiently large", L328) is chosen after `p` and is any
number above a threshold `C_{p,0}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem energyAux_bddCpt_integrable (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) : Integrable ρ ∧
    ∃ R₀ : ℝ, ∀ x, R₀ < ‖x‖ → ρ x = 0 := by
  obtain ⟨B, hB⟩ := hρ.bdd
  obtain ⟨R₀, hR₀⟩ := (hρ.cpt.isCompact).isBounded.subset_closedBall (0 : Euc d)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hzero : ∀ x, R₀ < ‖x‖ → ρ x = 0 := by
    intro x hx
    by_contra hne
    have hxs : x ∈ tsupport ρ := subset_tsupport _ hne
    have := hR₀ hxs
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  refine ⟨?_, R₀, hzero⟩
  refine Integrable.mono' (g := (closedBall (0 : Euc d) R₀).indicator (fun _ => B))
    ?_ hρ.measurable.aestronglyMeasurable ?_
  · exact (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (measure_closedBall_lt_top).ne)
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Euc d) R₀
    · rw [Set.indicator_of_mem hx]
      simpa [Real.norm_eq_abs] using hB x
    · rw [Set.indicator_of_notMem hx]
      have : R₀ < ‖x‖ := by
        rw [mem_closedBall, dist_zero_right] at hx
        exact lt_of_not_ge hx
      simp [hzero x this,]

/-- For a measurable density `a`, the signed measure `a dx` integrates `g` as `∫ a g`
(only the integrability of `a g` is needed). -/
theorem energyAux_int_ofDensity {d : ℕ} (a g : Euc d → ℝ) (ha : Measurable a)
    (hag : Integrable (fun x => a x * g x)) :
    (SMeas.ofDensity a).int g = ∫ x, a x * g x := by
  have hm1 : Measurable fun x => ENNReal.ofReal (a x) := ha.ennreal_ofReal
  have hm2 : Measurable fun x => ENNReal.ofReal (-a x) := ha.neg.ennreal_ofReal
  have ht1 : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (a x) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have ht2 : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (-a x) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hI1 : Integrable (fun x => (ENNReal.ofReal (a x)).toReal • g x) := by
    have : (fun x => (ENNReal.ofReal (a x)).toReal • g x) =
        {x | 0 < a x}.indicator (fun x => a x * g x) := by
      funext x
      by_cases h : 0 < a x
      · rw [Set.indicator_of_mem (show x ∈ {x | 0 < a x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_left h.le]
      · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < a x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_right (not_lt.1 h), zero_mul]
    rw [this]
    exact hag.indicator (measurableSet_lt measurable_const ha)
  have hI2 : Integrable (fun x => (ENNReal.ofReal (-a x)).toReal • g x) := by
    have : (fun x => (ENNReal.ofReal (-a x)).toReal • g x) =
        {x | a x < 0}.indicator (fun x => -(a x * g x)) := by
      funext x
      by_cases h : a x < 0
      · rw [Set.indicator_of_mem (show x ∈ {x | a x < 0} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_left (by linarith), neg_mul]
      · rw [Set.indicator_of_notMem (show x ∉ {x | a x < 0} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_right (by linarith [not_lt.1 h]), zero_mul]
    rw [this]
    exact (hag.neg).indicator (measurableSet_lt ha measurable_const)
  unfold SMeas.int SMeas.ofDensity
  rw [integral_withDensity_eq_integral_toReal_smul hm1 ht1 g,
    integral_withDensity_eq_integral_toReal_smul hm2 ht2 g, ← integral_sub hI1 hI2]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

/-- Joint integrability of `(x,y) ↦ f_1(x-y) ρ(x) ρ(y)` for a bounded compactly supported density. -/
theorem energyAux_joint_fTrunc {d : ℕ} {s : ℝ} (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) :
    Integrable (fun p : Euc d × Euc d => fTrunc s 1 (p.1 - p.2) * ρ p.1 * ρ p.2) := by
  obtain ⟨hf1, _⟩ := fTrunc_integrable hd hs0 hsd
  obtain ⟨B, hB⟩ := hρ.bdd
  have hρint := (energyAux_bddCpt_integrable ρ hρ).1
  have hconv := MeasureTheory.Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hρint hf1
  have hb := hconv.bdd_mul (c := B) ((hρ.measurable.comp measurable_fst).aestronglyMeasurable)
    (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB p.1)
  refine hb.congr (ae_of_all _ fun p => ?_)
  simp only [ContinuousLinearMap.mul_apply', Function.comp_apply]
  ring

/-- The kernel energy of a density, as an iterated integral (Fubini-type unfolding). -/
theorem energyAux_kerEnergy_density {d : ℕ} (h : Euc d → ℝ) (ρ : Euc d → ℝ) (hρm : Measurable ρ)
    (hsec : ∀ x, Integrable (fun y => ρ y * h (x - y)))
    (hjoint : Integrable (fun p : Euc d × Euc d => h (p.1 - p.2) * ρ p.1 * ρ p.2)) :
    kerEnergy h (SMeas.ofDensity ρ) = ∫ x, ∫ y, h (x - y) * ρ x * ρ y := by
  have inner : ∀ x, (SMeas.ofDensity ρ).int (fun y => h (x - y)) = ∫ y, ρ y * h (x - y) :=
    fun x => energyAux_int_ofDensity ρ _ hρm (hsec x)
  unfold kerEnergy SMeas.pair2
  simp only [inner]
  rw [energyAux_int_ofDensity ρ _ hρm ?_]
  · refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · refine (hjoint.integral_prod_left).congr (ae_of_all _ fun x => ?_)
    simp only
    rw [← integral_const_mul]
    congr 1
    funext y
    ring

/-- `‖μ‖²_{f_1} = ∬ f_1(x-y) ρ(x) ρ(y)` for a bounded compactly supported density. -/
theorem energyAux_kerEnergy_fTrunc {d : ℕ} {s : ℝ} (hd : 3 ≤ d) (hs0 : 0 ≤ s)
    (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) :
    kerEnergy (fTrunc s 1) (SMeas.ofDensity ρ) = ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y := by
  obtain ⟨hf1, _⟩ := fTrunc_integrable hd hs0 hsd
  obtain ⟨B, hB⟩ := hρ.bdd
  refine energyAux_kerEnergy_density _ ρ hρ.measurable (fun x => ?_)
    (energyAux_joint_fTrunc hd hs0 hsd ρ hρ)
  exact (hf1.comp_sub_left x).bdd_mul (c := B) hρ.measurable.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hB y)

/-- `ν = μ_N - μ` is a finite, compactly supported signed measure of mass zero (for `μ` bounded,
compactly supported of mass one); the admissibility used in `(3.Scoercive)`. -/
theorem chargeOf_admissible (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : Fin N → Euc d) :
    (chargeOf X ρ).IsFinite ∧ (chargeOf X ρ).CompactSupp ∧ (chargeOf X ρ).mass = 0 := by
  obtain ⟨hint, R₀, hzero⟩ := energyAux_bddCpt_integrable ρ hρ
  have hsum0 : (0:ℝ) ≤ ∑ i, ‖X i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  set R : ℝ := max R₀ 0 + ∑ i, ‖X i‖ with hRdef
  have hXin : ∀ i, X i ∈ closedBall (0 : Euc d) R := by
    intro i
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖X i‖ ≤ ∑ j, ‖X j‖ :=
      Finset.single_le_sum (f := fun j => ‖X j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    have h2 : (0:ℝ) ≤ max R₀ 0 := le_max_right _ _
    linarith
  have hρout : ∀ x, x ∉ closedBall (0 : Euc d) R → ρ x = 0 := by
    intro x hx
    apply hzero
    rw [mem_closedBall, dist_zero_right] at hx
    have h2 : R₀ ≤ max R₀ 0 := le_max_left _ _
    linarith [not_le.1 hx]
  have hfinPos : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (-ρ x)) :=
    isFiniteMeasure_withDensity_ofReal (hint.neg).hasFiniteIntegral
  have hfinNeg : IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (ρ x)) :=
    isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have : IsProbabilityMeasure (HRS.Whole.empirical X) :=
    HRS.Whole.empirical_isProbabilityMeasure (by omega) X
  have := hfinPos
  have := hfinNeg
  have hemp0 : HRS.Whole.empirical X (closedBall (0 : Euc d) R)ᶜ = 0 := by
    unfold HRS.Whole.empirical
    simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
    refine mul_eq_zero.2 (Or.inr ?_)
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Measure.dirac_apply']
    · exact Set.indicator_of_notMem (show X i ∉ (closedBall (0 : Euc d) R)ᶜ from fun h => h (hXin i)) _
    · exact measurableSet_closedBall.compl
  have hW : ∀ g : Euc d → ℝ, (∀ x, x ∉ closedBall (0 : Euc d) R → g x = 0) →
      (volume.withDensity fun x => ENNReal.ofReal (g x)) (closedBall (0 : Euc d) R)ᶜ = 0 := by
    intro g hg
    rw [withDensity_apply _ measurableSet_closedBall.compl]
    rw [setLIntegral_congr_fun measurableSet_closedBall.compl (g := fun _ => 0)
      (fun x hx => by simp [hg x hx])]
    simp
  refine ⟨⟨by unfold chargeOf; exact inferInstance, by unfold chargeOf; exact inferInstance⟩,
    ⟨R, ?_, ?_⟩, ?_⟩
  · unfold chargeOf
    simp only [Measure.add_apply]
    rw [hemp0, hW _ (fun x hx => by simp [hρout x hx])]
    simp
  · unfold chargeOf
    exact hW _ hρout
  · have hreal : ∀ (μ ν : Measure (Euc d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
        (μ + ν).real Set.univ = μ.real Set.univ + ν.real Set.univ := by
      intro μ ν _ _
      rw [measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)]
    have hWreal : ∀ g : Euc d → ℝ, (∀ x, 0 ≤ g x) → Integrable g → True := fun _ _ _ => trivial
    have hint_eq := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
    have hW1 : (volume.withDensity fun x => ENNReal.ofReal (-ρ x)).real Set.univ =
        (∫⁻ x, ENNReal.ofReal (-ρ x)).toReal := by
      rw [measureReal_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hW2 : (volume.withDensity fun x => ENNReal.ofReal (ρ x)).real Set.univ =
        (∫⁻ x, ENNReal.ofReal (ρ x)).toReal := by
      rw [measureReal_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hEmp : (HRS.Whole.empirical X).real Set.univ = 1 := probReal_univ
    unfold SMeas.mass SMeas.int chargeOf
    simp only [integral_const, smul_eq_mul, mul_one]
    rw [hreal _ _, hEmp, hW1, hW2]
    have h1 : ∫ x, ρ x = 1 := hρ.mass
    rw [h1] at hint_eq
    linarith


/-- Integrability from a bound on a set of finite measure, vanishing off that set. -/
theorem energyAux_integrable_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} (hF : AEStronglyMeasurable F μ) {S : Set α} (hS : MeasurableSet S)
    (hSfin : μ S ≠ ⊤) {M : ℝ} (hbd : ∀ x ∈ S, ‖F x‖ ≤ M) (hzero : ∀ x ∉ S, F x = 0) :
    Integrable F μ := by
  refine Integrable.mono' (g := S.indicator (fun _ => M)) ?_ hF ?_
  · exact (integrable_indicator_iff hS).2 (integrableOn_const hSfin)
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact hbd x hx
    · rw [Set.indicator_of_notMem hx, hzero x hx, norm_zero]

/-- `y ↦ ρ(y) G(z - y)` is integrable for a continuous `G` and a bounded compactly supported `ρ`. -/
theorem energyAux_integrable_mul_cont {d : ℕ} (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ)
    {G : Euc d → ℝ} (hG : Continuous G) (z : Euc d) :
    Integrable (fun y => ρ y * G (z - y)) := by
  obtain ⟨B, hB⟩ := hρ.bdd
  obtain ⟨_, R₀, hzero⟩ := energyAux_bddCpt_integrable ρ hρ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) (‖z‖ + |R₀|)).exists_bound_of_continuousOn
    hG.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0 : Euc d)
    (by rw [mem_closedBall, dist_zero_right, norm_zero]; positivity))
  refine energyAux_integrable_of_bound (μ := volume) (S := closedBall (0 : Euc d) R₀) ?_
    measurableSet_closedBall measure_closedBall_lt_top.ne (M := B * C) ?_ ?_
  · exact (hρ.measurable.mul (hG.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · intro y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hyR : ‖y‖ ≤ |R₀| := by
      rw [mem_closedBall, dist_zero_right] at hy
      exact hy.trans (le_abs_self _)
    have h1 : |ρ y| ≤ B := hB y
    have h2 : ‖G (z - y)‖ ≤ C := by
      apply hC
      rw [mem_closedBall, dist_zero_right]
      have : ‖z - y‖ ≤ ‖z‖ + ‖y‖ := norm_sub_le _ _
      linarith
    exact mul_le_mul h1 (by simpa [Real.norm_eq_abs] using h2) (abs_nonneg _) hB0
  · intro y hy
    have : R₀ < ‖y‖ := by
      by_contra h
      exact hy (by rw [mem_closedBall, dist_zero_right]; exact not_lt.1 h)
    simp [hzero y this]

/-- The joint integrability of `(x,y) ↦ G(x-y) ρ(x) ρ(y)` for a continuous `G`. -/
theorem energyAux_joint_cont {d : ℕ} (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ)
    {G : Euc d → ℝ} (hG : Continuous G) :
    Integrable (fun p : Euc d × Euc d => G (p.1 - p.2) * ρ p.1 * ρ p.2) := by
  obtain ⟨B, hB⟩ := hρ.bdd
  obtain ⟨_, R₀, hzero⟩ := energyAux_bddCpt_integrable ρ hρ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) (2 * |R₀|)).exists_bound_of_continuousOn
    hG.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0 : Euc d)
    (by rw [mem_closedBall, dist_zero_right, norm_zero]; positivity))
  have hKK : (volume : Measure (Euc d × Euc d))
      (closedBall (0 : Euc d) R₀ ×ˢ closedBall (0 : Euc d) R₀) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_closedBall_lt_top.ne measure_closedBall_lt_top.ne
  refine energyAux_integrable_of_bound (μ := volume)
    (S := closedBall (0 : Euc d) R₀ ×ˢ closedBall (0 : Euc d) R₀) ?_
    (measurableSet_closedBall.prod measurableSet_closedBall) hKK (M := C * B * B) ?_ ?_
  · exact (((hG.measurable.comp (measurable_fst.sub measurable_snd)).mul
      (hρ.measurable.comp measurable_fst)).mul (hρ.measurable.comp measurable_snd)).aestronglyMeasurable
  · rintro ⟨x, y⟩ hp
    obtain ⟨hx, hy⟩ := hp
    rw [mem_closedBall, dist_zero_right] at hx hy
    have hxy : ‖x - y‖ ≤ 2 * |R₀| := by
      have : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      have : ‖x‖ ≤ |R₀| := hx.trans (le_abs_self _)
      have : ‖y‖ ≤ |R₀| := hy.trans (le_abs_self _)
      linarith
    have hG' : ‖G (x - y)‖ ≤ C := hC _ (by rw [mem_closedBall, dist_zero_right]; exact hxy)
    have h1 : |ρ x| ≤ B := hB x
    have h2 : |ρ y| ≤ B := hB y
    have h3 : |G (x - y)| ≤ C := by simpa [Real.norm_eq_abs] using hG'
    simp only [Real.norm_eq_abs, abs_mul]
    calc |G (x - y)| * |ρ x| * |ρ y| ≤ C * B * B :=
          mul_le_mul (mul_le_mul h3 h1 (abs_nonneg _) hC0) h2 (abs_nonneg _) (mul_nonneg hC0 hB0)
      _ = C * B * B := rfl
  · rintro ⟨x, y⟩ hp
    by_cases hx : x ∈ closedBall (0 : Euc d) R₀
    · have hy : y ∉ closedBall (0 : Euc d) R₀ := fun hy => hp ⟨hx, hy⟩
      have : R₀ < ‖y‖ := by
        rw [mem_closedBall, dist_zero_right] at hy
        exact lt_of_not_ge hy
      simp [hzero y this]
    · have : R₀ < ‖x‖ := by
        rw [mem_closedBall, dist_zero_right] at hx
        exact lt_of_not_ge hx
      simp [hzero x this]

/-- Almost every point differs from a fixed point (no atoms in `ℝ^d`, `d ≥ 1`). -/
theorem energyAux_ae_ne {d : ℕ} (hd : 3 ≤ d) (x : Euc d) :
    ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x := by
  have : Nontrivial (Euc d) := by
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  have : NullSingletonClass (volume : Measure (Euc d)) := by infer_instance
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton x)] with y hy
  exact fun h => hy (by rw [h]; exact Set.mem_singleton _)

/-- Evenness of `f_1`. -/
theorem energyAux_fTrunc_neg (s : ℝ) (x : Euc d) : fTrunc s 1 (-x) = fTrunc s 1 x := by
  simp only [fTrunc, phiT, phi, smul_neg, norm_neg]

/-- Evenness of `g_1` (with the value `g_1(0)` at the origin). -/
theorem energyAux_g1_neg (s : ℝ) (x : Euc d) : g1 s (-x) = g1 s x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hnx : -x ≠ 0 := neg_ne_zero.2 hx
    simp only [g1, hnx, hx, if_false, kern, norm_neg, energyAux_fTrunc_neg]

/-- The unit-mass empirical measure integrates a strongly measurable `f` as `N⁻¹ ∑ f(X_i)`. -/
theorem energyAux_empirical_int {d N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (f : Euc d → ℝ)
    (hf : StronglyMeasurable f) :
    ∫ x, f x ∂(HRS.Whole.empirical X) = (1 / (N : ℝ)) * ∑ i, f (X i) := by
  unfold HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => integrable_dirac' hf
    (by simp)), ]
  simp only [integral_dirac' f _ hf, smul_eq_mul]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

/-- Integrability of a strongly measurable `f` for the empirical measure. -/
theorem energyAux_integrable_empirical {d N : ℕ} (X : Fin N → Euc d) (f : Euc d → ℝ)
    (hf : StronglyMeasurable f) (hN : 1 ≤ N) :
    Integrable f (HRS.Whole.empirical X) := by
  unfold HRS.Whole.empirical
  refine Integrable.smul_measure ?_ ?_
  · exact integrable_finsetSum_measure.2 fun i _ => integrable_dirac' hf (by simp)
  · exact ENNReal.inv_ne_top.2 (by exact_mod_cast (by omega : N ≠ 0))

/-- The charge `ν = μ_N - μ` integrates a strongly measurable `f` as `N⁻¹ ∑ f(X_i) - ∫ ρ f`. -/
theorem energyAux_charge_int {d N : ℕ} (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) (hN : 1 ≤ N)
    (X : Fin N → Euc d) (f : Euc d → ℝ) (hf : StronglyMeasurable f)
    (hfρ : Integrable (fun x => ρ x * f x)) :
    (chargeOf X ρ).int f = (1 / (N : ℝ)) * ∑ i, f (X i) - ∫ x, ρ x * f x := by
  have hρm := hρ.measurable
  have hIE := energyAux_integrable_empirical X f hf hN
  have hW1 : Integrable f (volume.withDensity fun x => ENNReal.ofReal (-ρ x)) := by
    refine (integrable_withDensity_iff_integrable_smul' hρm.neg.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).2 ?_
    have hfa : Integrable (fun x => -ρ x * f x) :=
      hfρ.neg.congr (ae_of_all _ fun x => by simp only [Pi.neg_apply]; ring)
    show Integrable (fun x => (ENNReal.ofReal (-ρ x)).toReal • f x) volume
    have : (fun x => (ENNReal.ofReal (-ρ x)).toReal • f x) =
        {x | 0 < -ρ x}.indicator (fun x => -ρ x * f x) := by
      funext x
      by_cases h : 0 < -ρ x
      · rw [Set.indicator_of_mem (show x ∈ {x | 0 < -ρ x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_left h.le]
      · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < -ρ x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_right (not_lt.1 h), zero_mul]
    rw [this]
    exact hfa.indicator (measurableSet_lt measurable_const hρm.neg)
  have hW2 : Integrable f (volume.withDensity fun x => ENNReal.ofReal (ρ x)) := by
    refine (integrable_withDensity_iff_integrable_smul' hρm.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)).2 ?_
    have : (fun x => (ENNReal.ofReal (ρ x)).toReal • f x) =
        {x | 0 < ρ x}.indicator (fun x => ρ x * f x) := by
      funext x
      by_cases h : 0 < ρ x
      · rw [Set.indicator_of_mem (show x ∈ {x | 0 < ρ x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_left h.le]
      · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < ρ x} from h), ENNReal.toReal_ofReal', smul_eq_mul,
          max_eq_right (not_lt.1 h), zero_mul]
    rw [this]
    exact hfρ.indicator (measurableSet_lt measurable_const hρm)
  have hD := energyAux_int_ofDensity (fun x => -ρ x) f hρm.neg (by simpa using hfρ.neg)
  have hD' : ∫ x, f x ∂(volume.withDensity fun x => ENNReal.ofReal (-ρ x)) -
      ∫ x, f x ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x)) = -∫ x, ρ x * f x := by
    have h2 := hD
    unfold SMeas.int SMeas.ofDensity at h2
    simp only [neg_neg] at h2
    rw [h2, ← integral_neg]
    congr 1
    funext x
    ring
  simp only [SMeas.int, chargeOf]
  rw [integral_add_measure hIE hW1, energyAux_empirical_int hN X f hf]
  linarith [hD']

/-- The modulated-energy expansion of `‖ν‖²_G` for a continuous even kernel `G` and `ν = μ_N - μ`
(diagonal included, as `G(0)` is the value of `G` at the origin). -/
theorem energyAux_kerEnergy_charge {d N : ℕ} (G : Euc d → ℝ) (hG : Continuous G)
    (hGe : ∀ z, G (-z) = G z) (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) (hN : 1 ≤ N)
    (X : Fin N → Euc d) :
    kerEnergy G (chargeOf X ρ) =
      (1 / (N : ℝ) ^ 2) * (∑ i, ∑ j, G (X i - X j))
        - (2 / (N : ℝ)) * (∑ i, (∫ y, G (X i - y) * ρ y))
        + (∫ x, ∫ y, G (x - y) * ρ x * ρ y) := by
  have hρm := hρ.measurable
  have hGm : Measurable G := hG.measurable
  set Φ : Euc d → ℝ := fun x => (1 / (N : ℝ)) * ∑ j, G (x - X j) - ∫ y, ρ y * G (x - y) with hΦ
  have hΦm : StronglyMeasurable Φ := by
    have h1 : Continuous fun x => (1 / (N : ℝ)) * ∑ j, G (x - X j) := by fun_prop
    have hF : StronglyMeasurable (fun p : Euc d × Euc d => ρ p.2 * G (p.1 - p.2)) :=
      ((hρm.comp measurable_snd).mul (hGm.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
    exact h1.stronglyMeasurable.sub hF.integral_prod_right'
  have hinner : ∀ x, (chargeOf X ρ).int (fun y => G (x - y)) = Φ x := by
    intro x
    rw [energyAux_charge_int ρ hρ hN X (fun y => G (x - y))
      ((hG.comp (continuous_const.sub continuous_id)).stronglyMeasurable)
      (energyAux_integrable_mul_cont ρ hρ hG x)]
  have hsum : ∀ x, ∑ j, ρ x * G (X j - x) = ρ x * ∑ j, G (x - X j) := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← neg_sub, hGe]
  have hpt : ∀ x, ρ x * Φ x = (1 / (N : ℝ)) * ∑ j, ρ x * G (X j - x)
      - ∫ y, G (x - y) * ρ x * ρ y := by
    intro x
    have hint : ∫ y, G (x - y) * ρ x * ρ y = ρ x * ∫ y, ρ y * G (x - y) := by
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    rw [hint, hsum x, hΦ]
    ring
  have hρΦ : Integrable (fun x => ρ x * Φ x) := by
    have heq : (fun x => ρ x * Φ x) = fun x => (1 / (N : ℝ)) * ∑ j, ρ x * G (X j - x)
        - ∫ y, G (x - y) * ρ x * ρ y := funext hpt
    rw [heq]
    refine Integrable.sub ?_ (energyAux_joint_cont ρ hρ hG).integral_prod_left
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun j _ => energyAux_integrable_mul_cont ρ hρ hG (X j)
  have hmain : kerEnergy G (chargeOf X ρ) = (chargeOf X ρ).int Φ := by
    unfold kerEnergy SMeas.pair2
    simp only [hinner]
  rw [hmain, energyAux_charge_int ρ hρ hN X Φ hΦm hρΦ]
  have hc : ∀ i, ∫ y, ρ y * G (X i - y) = ∫ y, G (X i - y) * ρ y :=
    fun i => integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
  have h1 : ∀ j, Integrable (fun x => ρ x * G (X j - x)) := fun j =>
    energyAux_integrable_mul_cont ρ hρ hG (X j)
  have hint2 : ∫ x, ρ x * Φ x = (1 / (N : ℝ)) * (∑ j, ∫ y, G (X j - y) * ρ y)
      - (∫ x, ∫ y, G (x - y) * ρ x * ρ y) := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_sub
      ((integrable_finsetSum _ fun j _ => h1 j).const_mul _) (energyAux_joint_cont ρ hρ hG).integral_prod_left,
      integral_const_mul, integral_finsetSum _ (fun j _ => h1 j)]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun j _ => integral_congr_ae (ae_of_all _ fun x => mul_comm (ρ x) (G (X j - x)))
  have hPhi : ∀ i, Φ (X i) = (1 / (N : ℝ)) * (∑ j, G (X i - X j))
      - (∫ y, G (X i - y) * ρ y) := fun i => by
    simp only [hΦ]
    rw [hc i]
  rw [hint2]
  simp only [hPhi, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The signed measure `a dx` integrates a vector-valued `g` as `∫ a • g` (any normed real space). -/
theorem energyAux_int_ofDensity_gen {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : Euc d → ℝ) (g : Euc d → E) (ha : Measurable a)
    (hag : Integrable (fun x => a x • g x)) :
    (∫ x, g x ∂(SMeas.ofDensity a).pos) - (∫ x, g x ∂(SMeas.ofDensity a).neg) =
      ∫ x, a x • g x := by
  have hm1 : Measurable fun x => ENNReal.ofReal (a x) := ha.ennreal_ofReal
  have hm2 : Measurable fun x => ENNReal.ofReal (-a x) := ha.neg.ennreal_ofReal
  have ht1 : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (a x) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have ht2 : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (-a x) < ⊤ :=
    ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hI1 : Integrable (fun x => (ENNReal.ofReal (a x)).toReal • g x) := by
    have : (fun x => (ENNReal.ofReal (a x)).toReal • g x) =
        {x | 0 < a x}.indicator (fun x => a x • g x) := by
      funext x
      by_cases h : 0 < a x
      · rw [Set.indicator_of_mem (show x ∈ {x | 0 < a x} from h), ENNReal.toReal_ofReal', max_eq_left h.le]
      · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < a x} from h), ENNReal.toReal_ofReal',
          max_eq_right (not_lt.1 h), zero_smul]
    rw [this]
    exact hag.indicator (measurableSet_lt measurable_const ha)
  have hI2 : Integrable (fun x => (ENNReal.ofReal (-a x)).toReal • g x) := by
    have : (fun x => (ENNReal.ofReal (-a x)).toReal • g x) =
        {x | a x < 0}.indicator (fun x => -(a x • g x)) := by
      funext x
      by_cases h : a x < 0
      · rw [Set.indicator_of_mem (show x ∈ {x | a x < 0} from h), ENNReal.toReal_ofReal',
          max_eq_left (by linarith), neg_smul]
      · rw [Set.indicator_of_notMem (show x ∉ {x | a x < 0} from h), ENNReal.toReal_ofReal',
          max_eq_right (by linarith [not_lt.1 h]), zero_smul]
    rw [this]
    exact (hag.neg).indicator (measurableSet_lt ha measurable_const)
  unfold SMeas.ofDensity
  simp only
  rw [integral_withDensity_eq_integral_toReal_smul hm1 ht1 g,
    integral_withDensity_eq_integral_toReal_smul hm2 ht2 g, ← integral_sub hI1 hI2]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal']
  rw [← sub_smul, max_zero_sub_max_neg_zero_eq_self]

/-- The Fourier transform of the signed measure `ρ dx`, as the pointwise Fourier integral. -/
theorem energyAux_fourier_ofDensity {d : ℕ} (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) (ξ : Euc d) :
    (SMeas.ofDensity ρ).fourier ξ = 𝓕 (fun x : Euc d => ((ρ x : ℝ) : ℂ)) ξ := by
  have hint : Integrable (fun x : Euc d => ρ x • (Complex.exp (-(2 * Real.pi * Complex.I *
      (inner ℝ x ξ : ℝ))) : ℂ)) := by
    have hρi := (energyAux_bddCpt_integrable ρ hρ).1
    have hc : Continuous fun x : Euc d => (Complex.exp (-(2 * Real.pi * Complex.I *
        (inner ℝ x ξ : ℝ))) : ℂ) := by fun_prop
    obtain ⟨C, hC⟩ : ∃ C, ∀ x : Euc d, ‖(Complex.exp (-(2 * Real.pi * Complex.I *
        (inner ℝ x ξ : ℝ))) : ℂ)‖ ≤ C := ⟨1, fun x => by
          rw [Complex.norm_exp]; simp⟩
    refine Integrable.mono' (g := fun x => C * ‖ρ x‖) (hρi.norm.const_mul C) ?_ ?_
    · exact (hρ.measurable.smul (by fun_prop : Continuous fun x : Euc d =>
        (Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))) : ℂ)).measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _) |>.trans_eq' (by ring)
  have hgen := energyAux_int_ofDensity_gen ρ (fun x : Euc d => (Complex.exp (-(2 * Real.pi * Complex.I *
      (inner ℝ x ξ : ℝ))) : ℂ)) hρ.measurable hint
  have e1 : (SMeas.ofDensity ρ).fourier ξ = ∫ x, ρ x • (Complex.exp (-(2 * Real.pi * Complex.I *
      (inner ℝ x ξ : ℝ))) : ℂ) := by
    unfold SMeas.fourier
    exact hgen
  rw [e1, Real.fourier_eq']
  congr 1
  funext x
  rw [Complex.real_smul, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- The `L²` Fourier transform of a real `L¹ ∩ L²` function is its pointwise Fourier integral. -/
theorem energyAux_fourierL2_eq {d : ℕ} (u : Euc d → ℝ) (hu1 : Integrable u) (hu2 : MemLp u 2 volume) :
    HRS.PDE.ToolboxRd.fourierL2 u =ᵐ[volume] 𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) := by
  set G : Euc d → ℂ := 𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) with hGdef
  have hGc : Continuous G := by
    have hi : Integrable (fun x : Euc d => ((u x : ℝ) : ℂ)) := hu1.ofReal
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi
  have hFloc : LocallyIntegrable (HRS.PDE.ToolboxRd.fourierL2 u) volume :=
    (HRS.PDE.ToolboxRd.FourierAux.memLp_fourierL2 hu2).locallyIntegrable (by norm_num)
  have hGloc : LocallyIntegrable G volume := hGc.locallyIntegrable
  have hFl := HRS.PDE.ToolboxRd.FourierAux.fourierL2_eq hu2
  have key : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (HRS.PDE.ToolboxRd.fourierL2 u x - G x) = 0 := by
    intro g hg hsupp
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hsC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
      hsupp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    set φ : SchwartzMap (Euc d) ℂ := hsC.toSchwartzMap hgC with hφdef
    have hφ : ⇑φ = fun x => ((g x : ℝ) : ℂ) := rfl
    set Fl := HRS.PDE.ToolboxRd.FourierAux.ofRealLp hu2 with hFldef
    -- the `L²` side: `∫ φ · 𝓕u = ∫ (𝓕φ) · u`
    have hL2side : ∫ x, φ x • (HRS.PDE.ToolboxRd.fourierL2 u x) =
        ∫ x, (𝓕 φ) x • ((u x : ℝ) : ℂ) := by
      have h1 : ∫ x, φ x • (HRS.PDE.ToolboxRd.fourierL2 u x) =
          ∫ x, φ x • ((HRS.PDE.ToolboxRd.FourierAux.FT d Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [congrFun hFl x]
      have h2 : (𝓕 (MeasureTheory.Lp.toTemperedDistribution Fl)) φ =
          ∫ x, φ x • ((𝓕 Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := by
        rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
          MeasureTheory.Lp.toTemperedDistribution_apply]
      have h3 : (𝓕 (MeasureTheory.Lp.toTemperedDistribution Fl)) φ =
          (MeasureTheory.Lp.toTemperedDistribution Fl) (𝓕 φ) := rfl
      have h4 : (MeasureTheory.Lp.toTemperedDistribution Fl) (𝓕 φ) = ∫ x, (𝓕 φ) x • Fl x :=
        MeasureTheory.Lp.toTemperedDistribution_apply _ _
      have h5 : ∫ x, φ x • ((HRS.PDE.ToolboxRd.FourierAux.FT d Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x =
          ∫ x, φ x • ((𝓕 Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := rfl
      rw [h1, h5, ← h2, h3, h4]
      refine integral_congr_ae ?_
      filter_upwards [HRS.PDE.ToolboxRd.FourierAux.ofRealLp_coe hu2] with x hx
      rw [hx]
    -- the `L¹` side: `∫ φ · 𝓕u = ∫ u · 𝓕φ`
    have hL1side : ∫ x, φ x • G x = ∫ x, ((u x : ℝ) : ℂ) • (𝓕 φ) x := by
      have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
        (L := innerₗ (Euc d)) (f := fun x : Euc d => ((u x : ℝ) : ℂ)) (g := φ)
        Real.continuous_fourierChar continuous_inner hu1.ofReal φ.integrable
      have hflip : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
        ext x y
        simp
      rw [hflip] at this
      have hc : ∫ x, φ x • G x = ∫ x, G x * φ x :=
        integral_congr_ae (ae_of_all _ fun x => by simp only [smul_eq_mul]; ring)
      rw [hc]
      simp only [smul_eq_mul]
      exact this
    have hintF : Integrable (fun x => φ x • HRS.PDE.ToolboxRd.fourierL2 u x) := by
      have hF2 := HRS.PDE.ToolboxRd.FourierAux.memLp_fourierL2 hu2
      have hφ2 : MemLp (fun x => φ x) 2 volume := φ.memLp 2 volume
      have := hφ2.integrable_mul hF2
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply, smul_eq_mul]
    have hφs : HasCompactSupport (fun x => φ x) := by
      show HasCompactSupport (⇑φ)
      rw [hφ]
      exact hsC
    have hintG : Integrable (fun x => φ x • G x) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact φ.continuous.smul hGc
      · exact hφs.smul_right
    have hsplit : ∫ x, g x • (HRS.PDE.ToolboxRd.fourierL2 u x - G x) =
        (∫ x, φ x • HRS.PDE.ToolboxRd.fourierL2 u x) - ∫ x, φ x • G x := by
      rw [← integral_sub hintF hintG]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hφ, Complex.real_smul, smul_eq_mul, mul_sub]
    have hc2 : ∫ x, ((u x : ℝ) : ℂ) * (𝓕 φ) x = ∫ x, (𝓕 φ) x * ((u x : ℝ) : ℂ) :=
      integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    rw [hsplit, hL2side, hL1side]
    simp only [smul_eq_mul]
    rw [hc2, sub_self]
  have hzero := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hFloc.sub hGloc) key
  filter_upwards [hzero] with x hx
  simpa [sub_eq_zero] using hx

/-- A bounded compactly supported density is in `L²`. -/
theorem energyAux_memLp_two {d : ℕ} (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) : MemLp ρ 2 volume := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hL1 := (energyAux_bddCpt_integrable ρ hρ).1
  refine (memLp_two_iff_integrable_sq hρ.measurable.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (g := fun x => B * ‖ρ x‖) (hL1.norm.const_mul B)
    (hρ.measurable.pow_const 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h2 : |ρ x| ≤ B := hB x
  have h3 : 0 ≤ |ρ x| := abs_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsq : ρ x ^ 2 = |ρ x| * |ρ x| := by rw [abs_mul_abs_self, sq]
  rw [hsq]
  exact mul_le_mul_of_nonneg_right h2 h3

/-- The `Ḣ`-type weighted bound for `‖μ‖_{H^{-α}}` by the energy `‖μ‖²_{f_1}`. -/
theorem energyAux_sob_bound {d : ℕ} {s : ℝ} (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (c : ℝ) (hc : 0 < c)
    (hsc : ∀ ξ : Euc d, c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(alphaE d s)) ≤ f1Hat s ξ)
    (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) :
    sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 ρ) ≤
      ENNReal.ofReal (c⁻¹ * ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y) := by
  obtain ⟨hint, hker⟩ := quadForm_f1 hd hs0 hsd ρ hρ
  have hL1 := (energyAux_bddCpt_integrable ρ hρ).1
  have hL2 := energyAux_memLp_two ρ hρ
  have hae := energyAux_fourierL2_eq ρ hL1 hL2
  have hnn : ∀ ξ : Euc d, 0 ≤ f1Hat s ξ := fun ξ => by
    have h1 := hsc ξ
    have h2 : (0 : ℝ) ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(alphaE d s)) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith
  have hsq : ∀ ξ : Euc d, ‖(SMeas.ofDensity ρ).fourier ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2) := by
    intro ξ
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hcalc : sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 ρ) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-alphaE d s)) *
        ‖(SMeas.ofDensity ρ).fourier ξ‖ₑ ^ 2 := by
    unfold sobSqE
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ, energyAux_fourier_ofDensity ρ hρ ξ]
  rw [hcalc]
  calc ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-alphaE d s)) *
          ‖(SMeas.ofDensity ρ).fourier ξ‖ₑ ^ 2
      ≤ ∫⁻ ξ, ENNReal.ofReal (c⁻¹ * (f1Hat s ξ * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2)) := by
        refine lintegral_mono fun ξ => ?_
        rw [hsq ξ, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hw : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-alphaE d s) ≤ c⁻¹ * f1Hat s ξ := by
          rw [inv_mul_eq_div, le_div_iff₀ hc]
          linarith [hsc ξ]
        calc (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-alphaE d s) * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2
            ≤ c⁻¹ * f1Hat s ξ * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hw (sq_nonneg _)
          _ = c⁻¹ * (f1Hat s ξ * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2) := by ring
      _ = ENNReal.ofReal (∫ ξ, c⁻¹ * (f1Hat s ξ * ‖(SMeas.ofDensity ρ).fourier ξ‖ ^ 2)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint.const_mul c⁻¹)
          (Filter.Eventually.of_forall fun ξ =>
            mul_nonneg (inv_nonneg.2 hc.le) (mul_nonneg (hnn ξ) (sq_nonneg _)))]
      _ = ENNReal.ofReal (c⁻¹ * ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y) := by
        rw [integral_const_mul, ← hker, energyAux_kerEnergy_fTrunc hd hs0 hsd ρ hρ]

/-- A bounded compactly supported density is in every `L^p`. -/
theorem energyAux_memLp_bdd {d : ℕ} (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) (p : ℝ≥0∞) :
    MemLp ρ p volume := by
  obtain ⟨_, R₀, hzero⟩ := energyAux_bddCpt_integrable ρ hρ
  obtain ⟨B, hB⟩ := hρ.bdd
  have hS : MeasurableSet (closedBall (0 : Euc d) R₀) := measurableSet_closedBall
  have hind : (closedBall (0 : Euc d) R₀).indicator ρ = ρ := by
    funext x
    by_cases hx : x ∈ closedBall (0 : Euc d) R₀
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have : R₀ < ‖x‖ := by
        rw [mem_closedBall, dist_zero_right] at hx
        exact lt_of_not_ge hx
      exact (hzero x this).symm
  rw [← hind, memLp_indicator_iff_restrict hS]
  haveI : IsFiniteMeasure (volume.restrict (closedBall (0 : Euc d) R₀)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  exact MemLp.of_bound hρ.measurable.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)

/-- Hölder's inequality for the one-point convolution `∫ f(z-y) ρ(y) dy`. -/
theorem energyAux_holder_bound {d : ℕ} {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1)
    (f ρ : Euc d → ℝ) (hfq : MemLp f q volume) (hρ : BddCptDensity ρ) (z : Euc d)
    (hI : Integrable (fun y => f (z - y) * ρ y)) :
    ∫ y, f (z - y) * ρ y ≤ (eLpNorm f q volume).toReal * (eLpNorm ρ p volume).toReal := by
  have hT1 : ENNReal.HolderTriple q p 1 := ENNReal.holderConjugate_iff.2 (by rw [add_comm]; exact hpq)
  have hρp : MemLp ρ p volume := energyAux_memLp_bdd ρ hρ p
  have hfz : eLpNorm (fun y => f (z - y)) q volume = eLpNorm f q volume :=
    eLpNorm_comp_measurePreserving hfq.aestronglyMeasurable ((volume : Measure (Euc d)).measurePreserving_sub_left z)
  have hH : eLpNorm (fun y => f (z - y) * ρ y) 1 volume ≤
      eLpNorm (fun y => f (z - y)) q volume * eLpNorm ρ p volume := by
    have hfzm : AEStronglyMeasurable (fun y => f (z - y)) volume := by
      have := (hfq.aestronglyMeasurable).comp_measurePreserving ((volume : Measure (Euc d)).measurePreserving_sub_left z)
      exact this
    have := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (p := q) (q := p) (r := 1)
      (fun a b : ℝ => a * b) (1 : ℝ≥0∞) (continuous_mul) hfzm hρp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simp [enorm_mul])
    simpa using this
  have hfin1 : eLpNorm (fun y => f (z - y)) q volume ≠ ⊤ := by
    rw [hfz]; exact (hfq.eLpNorm_lt_top).ne
  have hfin2 : eLpNorm ρ p volume ≠ ⊤ := (hρp.eLpNorm_lt_top).ne
  have hstep1 : ∫ y, f (z - y) * ρ y ≤ ∫ y, ‖f (z - y) * ρ y‖ :=
    integral_mono hI hI.norm fun y => Real.le_norm_self _
  have hstep2 : ∫ y, ‖f (z - y) * ρ y‖ = (eLpNorm (fun y => f (z - y) * ρ y) 1 volume).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hI.aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm hI.aestronglyMeasurable]
  have hstep3 : (eLpNorm (fun y => f (z - y) * ρ y) 1 volume).toReal ≤
      (eLpNorm (fun y => f (z - y)) q volume * eLpNorm ρ p volume).toReal := by
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hfin1 hfin2) ?_
    simpa using hH
  rw [hfz] at hstep3
  rw [ENNReal.toReal_mul] at hstep3
  linarith

/-- Membership in a unit cube is the equality of integer parts. -/
theorem energyAux_mem_cube_iff {d : ℕ} (x : Euc d) (j : Fin d → ℤ) :
    x ∈ cube j ↔ (fun k => ⌊x k⌋) = j := by
  unfold cube
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    funext k
    rw [Int.floor_eq_iff]
    exact h k
  · intro h k
    have := congrFun h k
    rw [Int.floor_eq_iff] at this
    exact this

/-- Points with the same integer parts are at distance at most `√d`. -/
theorem energyAux_norm_sub_le_sqrt {d : ℕ} (x y : Euc d) (h : (fun k => ⌊x k⌋) = (fun k => ⌊y k⌋)) :
    ‖x - y‖ ≤ Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖(x - y).ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk : |x k - y k| < 1 := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun h k)
        have hdiff : (x - y).ofLp k = x k - y k := rfl
        rw [hdiff, Real.norm_eq_abs]
        nlinarith [abs_nonneg (x k - y k)]
    _ = d := by simp

/-- The unit-cube occupation numbers as sums of indicators. -/
theorem energyAux_occ_eq {d N : ℕ} (X : Fin N → Euc d) (j : Fin d → ℤ) :
    occ X j = (1 / (N : ℝ)) * ∑ i, (if (fun k => ⌊X i k⌋) = j then (1 : ℝ) else 0) := by
  unfold occ
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [energyAux_mem_cube_iff]

/-- The `ℓ²` sum of the occupation numbers over all cubes, as a double sum over pairs. -/
theorem energyAux_occ_tsum {d N : ℕ} (X : Fin N → Euc d) :
    ∑' j : Fin d → ℤ, occ X j ^ 2 = (1 / (N : ℝ)) ^ 2 * ∑ i, ∑ l,
      (if (fun k => ⌊X i k⌋) = (fun k => ⌊X l k⌋) then (1 : ℝ) else 0) := by
  set ind : Fin N → (Fin d → ℤ) → ℝ := fun i j => if (fun k => ⌊X i k⌋) = j then (1 : ℝ) else 0
    with hind
  have hocc : ∀ j, occ X j = (1 / (N : ℝ)) * ∑ i, ind i j := fun j => energyAux_occ_eq X j
  have hsq : ∀ j, occ X j ^ 2 = ∑ i, ∑ l, (1 / (N : ℝ)) ^ 2 * (ind i j * ind l j) := by
    intro j
    have h1 : occ X j ^ 2 = (1 / (N : ℝ)) ^ 2 * ((∑ i, ind i j) * (∑ l, ind l j)) := by
      rw [hocc j]
      ring
    rw [h1, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hsum : ∀ i l, Summable (fun j => (1 / (N : ℝ)) ^ 2 * (ind i j * ind l j)) := by
    intro i l
    refine (summable_of_ne_finset_zero (s := {(fun k => ⌊X i k⌋)}) ?_).mul_left _
    intro j hj
    have : ind i j = 0 := by
      rw [hind]
      simp only
      rw [if_neg]
      intro h
      exact hj (by simp [h])
    simp [this]
  simp_rw [hsq]
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun l _ => hsum i l)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum (fun l _ => hsum i l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tsum_mul_left]
  congr 1
  rw [tsum_eq_single (fun k => ⌊X i k⌋)]
  · simp only [hind, if_pos rfl]
    by_cases h : (fun k => ⌊X i k⌋) = (fun k => ⌊X l k⌋)
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro j hj
    simp only [hind]
    rw [if_neg (Ne.symm hj)]
    simp

/-- The occupancy bound `∑_j n_j² ≲ 1/N + ∑_{i≠l} f_1(x_i - x_l)/N²`. -/
theorem energyAux_occ_bound {d N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (hX : Function.Injective X)
    (f : Euc d → ℝ) (c : ℝ) (hc : 0 < c)
    (hf0 : ∀ x : Euc d, x ≠ 0 → 0 ≤ f x)
    (hfc : ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ Real.sqrt d → c ≤ f x) :
    ∑' j : Fin d → ℤ, occ X j ^ 2 ≤
      1 / (N : ℝ) + (1 / c) * ((1 / (N : ℝ)) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, f (X i - X j)) := by
  rw [energyAux_occ_tsum]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpair : ∀ i, ∀ l ∈ Finset.univ.erase i,
      (if (fun k => ⌊X i k⌋) = (fun k => ⌊X l k⌋) then (1 : ℝ) else 0) ≤ (1 / c) * f (X i - X l) := by
    intro i l hl
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    have hne : X i - X l ≠ 0 := sub_ne_zero.2 (fun h => hli (hX h).symm)
    have hf_nn := hf0 _ hne
    by_cases h : (fun k => ⌊X i k⌋) = (fun k => ⌊X l k⌋)
    · rw [if_pos h]
      have hc' := hfc _ hne (energyAux_norm_sub_le_sqrt (X i) (X l) h)
      calc (1 : ℝ) = (1 / c) * c := by field_simp
        _ ≤ (1 / c) * f (X i - X l) := mul_le_mul_of_nonneg_left hc' (by positivity)
    · rw [if_neg h]
      exact mul_nonneg (by positivity) hf_nn
  have hdiag : ∑ i, ∑ l, (if (fun k => ⌊X i k⌋) = (fun k => ⌊X l k⌋) then (1 : ℝ) else 0) =
      (N : ℝ) + ∑ i, ∑ l ∈ Finset.univ.erase i,
        (if (fun k => ⌊X i k⌋) = (fun k => ⌊X l k⌋) then (1 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl fun i _ => (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm]
    rw [Finset.sum_add_distrib]
    congr 1
    simp
  rw [hdiag]
  have hsum_le : ∑ i, ∑ l ∈ Finset.univ.erase i,
        (if (fun k => ⌊X i k⌋) = (fun k => ⌊X l k⌋) then (1 : ℝ) else 0) ≤
      (1 / c) * ∑ i, ∑ j ∈ Finset.univ.erase i, f (X i - X j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l hl => hpair i l hl
  have hNsq : (1 / (N : ℝ)) ^ 2 * (N : ℝ) = 1 / (N : ℝ) := by
    field_simp
  calc (1 / (N : ℝ)) ^ 2 * ((N : ℝ) + ∑ i, ∑ l ∈ Finset.univ.erase i,
          (if (fun k => ⌊X i k⌋) = (fun k => ⌊X l k⌋) then (1 : ℝ) else 0))
      ≤ (1 / (N : ℝ)) ^ 2 * ((N : ℝ) + (1 / c) * ∑ i, ∑ j ∈ Finset.univ.erase i, f (X i - X j)) := by
        gcongr
    _ = 1 / (N : ℝ) + (1 / c) * ((1 / (N : ℝ)) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, f (X i - X j)) := by
        rw [mul_add, hNsq]
        ring

/-- The energy identity `[N] (2.energyidentity)` (L346-350; "the identity of `[HCRS25, (2.47)]`
specialised to `(2.positivecut)`"): inserting `g = g_1 + f_1`, restoring the diagonal only in the `g_1`
term,
`‖ν‖²_{g_1} + N⁻² ∑_{i≠j} f_1(x_i-x_j) + ‖μ‖²_{f_1} = 2F_N + g_1(0)/N + (2/N) ∑_i (f_1*μ)(x_i)`.
Unconditional for bounded compactly supported `ρ` (all integrals converge absolutely). -/
theorem energy_identity (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ)
    (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (hX : Function.Injective X) :
    kerEnergy (g1 s) (chargeOf X ρ) +
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) +
        ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y =
      2 * modEnergy s X ρ + g1Zero d s / (N : ℝ) +
        (2 / (N : ℝ)) * ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  have hg1c : Continuous (g1 s) := (g1_smooth hd hs0 hsd).continuous
  obtain ⟨hf1, _⟩ := fTrunc_integrable hd hs0 hsd
  obtain ⟨B, hB⟩ := hρ.bdd
  rw [energyAux_kerEnergy_charge (g1 s) hg1c (energyAux_g1_neg s) ρ hρ hN X]
  -- the kernel `g = g_1 + f_1` off the origin
  have hk_split : ∀ z : Euc d, z ≠ 0 → kern s z = g1 s z + fTrunc s 1 z := by
    intro z hz
    simp only [g1, if_neg hz]
    ring
  -- integrability of the one-variable and two-variable products
  have hIg : ∀ z : Euc d, Integrable (fun y => g1 s (z - y) * ρ y) := fun z =>
    (energyAux_integrable_mul_cont ρ hρ hg1c z).congr (ae_of_all _ fun y => mul_comm _ _)
  have hIf : ∀ z : Euc d, Integrable (fun y => fTrunc s 1 (z - y) * ρ y) := fun z =>
    ((hf1.comp_sub_left z).bdd_mul (c := B) hρ.measurable.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hB y)).congr
      (ae_of_all _ fun y => mul_comm _ _)
  have hJg : Integrable (fun p : Euc d × Euc d => g1 s (p.1 - p.2) * ρ p.1 * ρ p.2) :=
    energyAux_joint_cont ρ hρ hg1c
  have hJf : Integrable (fun p : Euc d × Euc d => fTrunc s 1 (p.1 - p.2) * ρ p.1 * ρ p.2) :=
    energyAux_joint_fTrunc hd hs0 hsd ρ hρ
  -- (A) the diagonal: `∑_j g_1(X_i - X_j) = g_1(0) + ∑_{j ≠ i}`
  have hG1zero : g1 s (0 : Euc d) = g1Zero d s := by simp [g1]
  have hdiag : ∀ i : Fin N, ∑ j, g1 s (X i - X j) =
      g1Zero d s + ∑ j ∈ Finset.univ.erase i, g1 s (X i - X j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), sub_self, hG1zero]
  have hG1sum : ∑ i, ∑ j, g1 s (X i - X j) =
      (N : ℝ) * g1Zero d s + ∑ i, ∑ j ∈ Finset.univ.erase i, g1 s (X i - X j) := by
    rw [Finset.sum_congr rfl fun i _ => hdiag i, Finset.sum_add_distrib]
    simp
  -- (B) particle sums: `kern = g_1 + f_1` on pairs with `i ≠ j`
  have hPk : ∑ i, ∑ j ∈ Finset.univ.erase i, kern s (X i - X j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, g1 s (X i - X j) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => hk_split _ ?_
    intro h
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    exact hji (hX (sub_eq_zero.1 h).symm)
  -- (C) one-variable integrals: `∫ kern(X_i - y) ρ(y) = ∫ g_1 ρ + ∫ f_1 ρ`
  have hKi : ∀ i : Fin N, ∫ y, kern s (X i - y) * ρ y =
      (∫ y, g1 s (X i - y) * ρ y) + ∫ y, fTrunc s 1 (X i - y) * ρ y := by
    intro i
    rw [← integral_add (hIg (X i)) (hIf (X i))]
    refine integral_congr_ae ?_
    filter_upwards [energyAux_ae_ne hd (X i)] with y hy
    rw [hk_split _ (sub_ne_zero.2 (Ne.symm hy))]
    ring
  -- (D) two-variable integrals
  have hKint : ∫ x, ∫ y, kern s (x - y) * ρ x * ρ y =
      (∫ x, ∫ y, g1 s (x - y) * ρ x * ρ y) + ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y := by
    have hinner : ∀ x : Euc d, ∫ y, kern s (x - y) * ρ x * ρ y =
        (∫ y, g1 s (x - y) * ρ x * ρ y) + ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y := by
      intro x
      have h1 : Integrable (fun y => g1 s (x - y) * ρ x * ρ y) :=
        ((hIg x).const_mul (ρ x)).congr (ae_of_all _ fun y => by ring)
      have h2 : Integrable (fun y => fTrunc s 1 (x - y) * ρ x * ρ y) :=
        ((hIf x).const_mul (ρ x)).congr (ae_of_all _ fun y => by ring)
      rw [← integral_add h1 h2]
      refine integral_congr_ae ?_
      filter_upwards [energyAux_ae_ne hd x] with y hy
      rw [hk_split _ (sub_ne_zero.2 (Ne.symm hy))]
      ring
    rw [integral_congr_ae (ae_of_all _ hinner), integral_add hJg.integral_prod_left hJf.integral_prod_left]
  -- (E) the right-hand side, unfolded
  have hSK : ∑ i, ∫ y, kern s (X i - y) * ρ y =
      (∑ i, ∫ y, g1 s (X i - y) * ρ y) + ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hKi i
  have hz : (1 / (N : ℝ) ^ 2) * ((N : ℝ) * g1Zero d s) = g1Zero d s / N := by
    field_simp
  unfold modEnergy pairGen
  beta_reduce
  rw [hG1sum, hSK, hPk, hKint]
  linear_combination hz

/-- Positivity of the three terms on the left of `(2.energyidentity)` (`[N] L351`: "All three terms on
the left are nonnegative. In particular, the positivity of `‖μ‖²_{f_1}` does not require `μ ≥ 0`"):
`‖ν‖²_{g_1} ≥ 0` (conditional positive definiteness, `ν` of mass zero), the particle sum `≥ 0`
(`f_1 > 0`), `‖μ‖²_{f_1} ≥ 0` (positive definiteness). -/
theorem energy_terms_nonneg (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ)
    (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d) (hX : Function.Injective X) :
    0 ≤ kerEnergy (g1 s) (chargeOf X ρ) ∧
      0 ≤ (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) ∧
      0 ≤ ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y := by
  obtain ⟨hfin, hcpt, hm⟩ := chargeOf_admissible ρ hρ hN X
  refine ⟨?_, ?_, ?_⟩
  · by_cases hs : s = 0
    · exact (posDef_g1 hd hs0 hsd (chargeOf X ρ) hfin hcpt).1 hs hm
    · exact (posDef_g1 hd hs0 hsd (chargeOf X ρ) hfin hcpt).2
        (lt_of_le_of_ne hs0 (Ne.symm hs))
  · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hne : X i - X j ≠ 0 := sub_ne_zero.2 (fun h => hji (hX h.symm))
    exact (fTrunc_pos hd hs0 hsd _ hne).le
  · rw [← energyAux_kerEnergy_fTrunc hd hs0 hsd ρ hρ]
    exact posDef_f1 hd hs0 hsd ρ hρ

/-- `y ↦ f_1(z - y) ρ(y)` is integrable. -/
theorem energyAux_integrable_fTrunc_mul {d : ℕ} {s : ℝ} (hd : 3 ≤ d) (hs0 : 0 ≤ s)
    (hsd : s < (d : ℝ) - 2) (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) (z : Euc d) :
    Integrable (fun y => fTrunc s 1 (z - y) * ρ y) := by
  obtain ⟨hf1, _⟩ := fTrunc_integrable hd hs0 hsd
  obtain ⟨B, hB⟩ := hρ.bdd
  exact ((hf1.comp_sub_left z).bdd_mul (c := B) hρ.measurable.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hB y)).congr
      (ae_of_all _ fun y => mul_comm _ _)

/-- Lemma 2.2 `lem:energy-control` (`[N] L327-342`, proof L344-374): for a sufficiently large
`C_p = C_p(d,s,p)`, with `Ec = F_N + C_p(1/N + ‖μ‖_{L^p})`:

* `(2.Ecoercive)` `Ec ≥ 1/N + (1+‖f_1‖_{L^{p'}})‖μ‖_{L^p}`;
* `(2.energy-control)` `‖ν‖²_{g_1} + N⁻² ∑_{i≠j} f_1(x_i-x_j) + ‖μ‖²_{f_1} ≤ 2 Ec`;
* `(2.backgroundH)` `‖μ‖²_{H^{-α}} ≲ ‖μ‖²_{f_1}` (Plancherel and `(2.shortcoercive)`) and
  `‖μ‖²_{f_1} ≲ Ec` (here with constant `1`, as the left side of `(2.energy-control)` dominates it);
* `(2.occupancy)` `∑_j n_j² ≲ Ec`, `n_j = μ_N(Q_j)`.

`p'` is the Hölder conjugate `q` of `p` (`p⁻¹ + q⁻¹ = 1`); `‖μ‖_{H^{-α}}` uses `fourierL2 ρ` (`ρ ∈ L²`).
The constant `C_b` is independent of `p` and of `C_p` (the proofs of `(2.backgroundH)` and
`(2.occupancy)` use only `(2.energy-control)`, `(2.Ecoercive)` and `(2.fcomparison)`). -/
theorem energy_control (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
        1 / (N : ℝ) + (1 + normE q (fTrunc s 1 : Euc d → ℝ)) * normE p ρ ≤
            modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ) ∧
        kerEnergy (g1 s) (chargeOf X ρ) +
            (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) +
            ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y ≤
          2 * (modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ)) ∧
        sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 ρ) ≤
          ENNReal.ofReal (Cb * ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y) ∧
        ∑' j : Fin d → ℤ, occ X j ^ 2 ≤
          Cb * (modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ)) := by
  obtain ⟨cf, hcf0, hcf⟩ := fTrunc_lower_near hd hs0 hsd
  obtain ⟨cs, hcs0, hcs⟩ := shortcoercive hd hs0 hsd
  have hcf_inv : 0 < cf⁻¹ := inv_pos.2 hcf0
  have hcs_inv : 0 < cs⁻¹ := inv_pos.2 hcs0
  refine ⟨cs⁻¹ + (1 + 2 * cf⁻¹), by linarith, fun p q hp hpq => ?_⟩
  have hMf : MemLp (fTrunc s 1 : Euc d → ℝ) q volume := fTrunc_Lq hd hs0 hsd p q hp hpq
  have hnq0 : 0 ≤ normE q (fTrunc s 1 : Euc d → ℝ) := ENNReal.toReal_nonneg
  refine ⟨|g1Zero d s| + 2 * normE q (fTrunc s 1 : Euc d → ℝ) + 1, by
    have := abs_nonneg (g1Zero d s); linarith, fun Cp hCp ρ hρ N X hN hX => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnp0 : 0 ≤ normE p ρ := ENNReal.toReal_nonneg
  set nq := normE q (fTrunc s 1 : Euc d → ℝ) with hnq
  set np := normE p ρ with hnp
  set I := ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y with hI
  set Ec := modEnergy s X ρ + Cp * (1 / (N : ℝ) + np) with hEc
  set g0 := |g1Zero d s| with hg0
  have hg0nn : 0 ≤ g0 := abs_nonneg _
  -- Hölder: each `∫ f_1(X_i - y) ρ(y) dy ≤ ‖f_1‖_q ‖ρ‖_p`
  have hHold : ∀ z : Euc d, ∫ y, fTrunc s 1 (z - y) * ρ y ≤ nq * np := fun z =>
    energyAux_holder_bound hpq (fTrunc s 1) ρ hMf hρ z (energyAux_integrable_fTrunc_mul hd hs0 hsd ρ hρ z)
  have hB : ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y ≤ (N : ℝ) * (nq * np) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hHold (X i)
    simpa using this
  -- the energy identity and the positivity of its left side
  have hid := energy_identity hd hs0 hsd ρ hρ hN X hX
  rw [← hI] at hid
  obtain ⟨hpos1, hpos2, hpos3⟩ := energy_terms_nonneg hd hs0 hsd ρ hρ hN X hX
  have hI0 : 0 ≤ I := hpos3
  have hK0 : 0 ≤ kerEnergy (g1 s) (chargeOf X ρ) := hpos1
  have hT0 : 0 ≤ (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) := hpos2
  -- the right side of the identity, bounded
  have hBN : (1 / (N : ℝ)) * ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y ≤ nq * np := by
    have : (1 / (N : ℝ)) * ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y ≤ (1 / (N : ℝ)) * ((N : ℝ) * (nq * np)) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    have hNe : (1 / (N : ℝ)) * ((N : ℝ) * (nq * np)) = nq * np := by field_simp
    linarith
  have hgZ : g1Zero d s / (N : ℝ) ≤ g0 / (N : ℝ) :=
    div_le_div_of_nonneg_right (le_abs_self _) hN0.le
  have hBN2 : (2 / (N : ℝ)) * ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y = 2 * ((1 / (N : ℝ)) *
      ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y) := by ring
  have hmodlow : -(g0 / (N : ℝ)) / 2 - nq * np ≤ modEnergy s X ρ := by
    have hsum0 : 0 ≤ (kerEnergy (g1 s) (chargeOf X ρ)) +
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) +
        ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y := by linarith
    rw [hid] at hsum0
    linarith
  -- claim (1): the lower bound `Ec ≥ 1/N + (1 + ‖f_1‖_q)‖μ‖_p`
  have hclaim1 : 1 / (N : ℝ) + (1 + nq) * np ≤ Ec := by
    have hCp' : g0 + 2 * nq + 1 ≤ Cp := hCp
    have h1 : 1 / (N : ℝ) ≤ (Cp - g0 / 2) * (1 / (N : ℝ)) := by
      have : 1 ≤ Cp - g0 / 2 := by linarith
      nlinarith [one_div_pos.2 hN0]
    have h2 : (2 * nq + 1) * np ≤ Cp * np := mul_le_mul_of_nonneg_right (by linarith) hnp0
    rw [hEc]
    have e1 : (Cp - g0 / 2) * (1 / (N : ℝ)) = Cp * (1 / (N : ℝ)) - g0 / (N : ℝ) / 2 := by ring
    have e2 : Cp * (1 / (N : ℝ) + np) = Cp * (1 / (N : ℝ)) + Cp * np := by ring
    have e3 : (2 * nq + 1) * np = 2 * (nq * np) + np := by ring
    have e4 : (1 + nq) * np = np + nq * np := by ring
    rw [e2]
    rw [e1] at h1
    rw [e3] at h2
    rw [e4]
    linarith [hmodlow, h1, h2]
  -- claim (2): the energy inequality
  have hcl2 : g1Zero d s / (N : ℝ) + 2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y)
      ≤ 2 * (Cp * (1 / (N : ℝ))) + 2 * (Cp * np) := by
    have hCp' : g0 + 2 * nq + 1 ≤ Cp := hCp
    have h1 : g1Zero d s / (N : ℝ) ≤ 2 * (Cp * (1 / (N : ℝ))) := by
      have : g0 ≤ 2 * Cp := by linarith
      have h3 : g0 / (N : ℝ) ≤ 2 * Cp / (N : ℝ) := div_le_div_of_nonneg_right this hN0.le
      have h4 : g1Zero d s / (N : ℝ) ≤ g0 / (N : ℝ) := hgZ
      have h5 : 2 * Cp / (N : ℝ) = 2 * (Cp * (1 / (N : ℝ))) := by ring
      linarith
    have h2 : 2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y) ≤ 2 * (Cp * np) := by
      have : (1 / (N : ℝ)) * ∑ i, ∫ y, fTrunc s 1 (X i - y) * ρ y ≤ Cp * np := by
        have : nq * np ≤ Cp * np := mul_le_mul_of_nonneg_right (by linarith) hnp0
        linarith [hBN]
      linarith
    linarith
  have hclaim2 : kerEnergy (g1 s) (chargeOf X ρ) +
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) + I ≤ 2 * Ec := by
    rw [hEc]
    have : (2:ℝ) * (modEnergy s X ρ + Cp * (1 / (N : ℝ) + np)) =
        2 * modEnergy s X ρ + 2 * (Cp * (1 / (N : ℝ))) + 2 * (Cp * np) := by ring
    rw [this]
    linarith [hcl2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (2.Ecoercive)
    exact hclaim1
  · -- (2.energy-control)
    exact hclaim2
  · -- (2.backgroundH)
    have h3 := energyAux_sob_bound hd hs0 hsd cs hcs0 hcs ρ hρ
    rw [← hI] at h3
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) hI0
  · -- (2.occupancy)
    have h4 := energyAux_occ_bound hN X hX (fTrunc s 1) cf hcf0
      (fun x hx => (fTrunc_pos hd hs0 hsd x hx).le) hcf
    rw [one_div_pow] at h4
    have hT : (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTrunc s 1 (X i - X j) ≤ 2 * Ec := by
      linarith [hclaim2]
    have hNEc : 1 / (N : ℝ) ≤ Ec := by
      have : 0 ≤ (1 + nq) * np := mul_nonneg (by linarith) hnp0
      linarith [hclaim1]
    have hEc0 : 0 ≤ Ec := le_trans (by positivity) hNEc
    have hcf_nn : 0 ≤ cf⁻¹ := hcf_inv.le
    calc ∑' j : Fin d → ℤ, occ X j ^ 2
        ≤ 1 / (N : ℝ) + (1 / cf) * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
            fTrunc s 1 (X i - X j)) := h4
      _ ≤ Ec + (1 / cf) * (2 * Ec) :=
          add_le_add hNEc (mul_le_mul_of_nonneg_left hT (by positivity))
      _ = Ec + cf⁻¹ * (2 * Ec) := by rw [one_div]
      _ ≤ (cs⁻¹ + (1 + 2 * cf⁻¹)) * Ec := by
          have hcsE : 0 ≤ cs⁻¹ * Ec := mul_nonneg hcs_inv.le hEc0
          have e : (cs⁻¹ + (1 + 2 * cf⁻¹)) * Ec = Ec + cf⁻¹ * (2 * Ec) + cs⁻¹ * Ec := by ring
          rw [e]
          linarith

/-- `(3.Scoercive)` (`[N] L395-400`, proof L401-407, from `(2.lowcoercive)` with `R = 8`): for a
compactly supported finite real measure `σ` (of mass zero when `s = 0`),
`‖P_{≤4}σ‖²_{Ḣ^{-α}} + ‖P_{≤4}σ‖²_{L²} ≲ ‖σ‖²_{g_1}`.  Here `\widehat{P_{≤4}σ} = χ(ξ/4) σ̂`
(`lowFreq 4 σ.fourier`). -/
theorem scoercive (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : SMeas d, σ.IsFinite → σ.CompactSupp → (s = 0 → σ.mass = 0) →
      homSqE (-alphaE d s) (lowFreq 4 σ.fourier) + sobSqE 0 (lowFreq 4 σ.fourier) ≤
        ENNReal.ofReal (C * kerEnergy (g1 s) σ) := by
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 < alphaE d s := by
    unfold alphaE
    apply div_pos _ two_pos
    linarith
  obtain ⟨c, hc, hcl⟩ := lowcoercive hd hs0 hsd 8 (by norm_num)
  have hpow8 : (0:ℝ) < 8 ^ (-(2 * alphaE d s)) := Real.rpow_pos_of_pos (by norm_num) _
  have hpi : (0:ℝ) < (2 * Real.pi) ^ (2 * (-alphaE d s)) :=
    Real.rpow_pos_of_pos (by positivity) _
  set C1 : ℝ := (2 * Real.pi) ^ (2 * (-alphaE d s)) / c with hC1
  set C2 : ℝ := 1 / (c * 8 ^ (-(2 * alphaE d s))) with hC2
  have hC1p : 0 < C1 := div_pos hpi hc
  have hC2p : 0 < C2 := div_pos one_pos (mul_pos hc hpow8)
  refine ⟨C1 + C2, add_pos hC1p hC2p, fun σ hfin hcpt hmass => ?_⟩
  obtain ⟨hint, hkey⟩ := quadForm_g1 hd hs0 hsd σ hfin hcpt hmass
  have hK : 0 ≤ kerEnergy (g1 s) σ := by
    rw [hkey]
    exact integral_nonneg fun ξ => mul_nonneg (g1Hat_nonneg hs0 hs2 ξ) (sq_nonneg _)
  -- the cutoff: values in [0,1], vanishing for `‖ξ‖ ≥ 8`
  have hchi0 : ∀ x : Euc d, 0 ≤ chi x := fun x => (chiBump d).nonneg
  have hchi1 : ∀ x : Euc d, chi x ≤ 1 := fun x => (chiBump d).le_one
  have hchi_zero : ∀ x : Euc d, 2 ≤ ‖x‖ → chi x = 0 := by
    intro x hx
    exact (chiBump d).zero_of_le_dist (by rw [dist_zero_right]; exact hx)
  have hFnorm : ∀ ξ : Euc d, ‖lowFreq 4 σ.fourier ξ‖ = chi ((4:ℝ)⁻¹ • ξ) * ‖σ.fourier ξ‖ := by
    intro ξ
    unfold lowFreq
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hchi0 _)]
  -- pointwise bounds for `ξ ≠ 0`
  have hreal1 : ∀ ξ : Euc d, ξ ≠ 0 →
      (2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s)) * ‖lowFreq 4 σ.fourier ξ‖ ^ 2 ≤
        C1 * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2) := by
    intro ξ hξ
    have ht : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hg0 : 0 ≤ g1Hat s ξ := g1Hat_nonneg hs0 hs2 ξ
    have hu : 0 ≤ ‖σ.fourier ξ‖ := norm_nonneg _
    rw [hFnorm ξ]
    by_cases h8 : ‖ξ‖ < 8
    · have hg : c * ‖ξ‖ ^ (-(2 * alphaE d s)) ≤ g1Hat s ξ := hcl ξ hξ h8.le
      have hχ : chi ((4:ℝ)⁻¹ • ξ) ^ 2 ≤ 1 := by
        have := hchi1 ((4:ℝ)⁻¹ • ξ); have := hchi0 ((4:ℝ)⁻¹ • ξ); nlinarith
      have hw : 0 ≤ ‖σ.fourier ξ‖ ^ 2 := sq_nonneg _
      have hrw : (2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s)) =
          (2 * Real.pi) ^ (2 * (-alphaE d s)) * ‖ξ‖ ^ (-(2 * alphaE d s)) := by
        rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
        congr 2
        ring
      have hle : ‖ξ‖ ^ (-(2 * alphaE d s)) ≤ g1Hat s ξ / c := by
        rw [le_div_iff₀ hc]; linarith
      have hpos : (0:ℝ) ≤ (2 * Real.pi) ^ (2 * (-alphaE d s)) := hpi.le
      calc (2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s)) * (chi ((4:ℝ)⁻¹ • ξ) * ‖σ.fourier ξ‖) ^ 2
          = (2 * Real.pi) ^ (2 * (-alphaE d s)) * ‖ξ‖ ^ (-(2 * alphaE d s)) *
              (chi ((4:ℝ)⁻¹ • ξ) ^ 2 * ‖σ.fourier ξ‖ ^ 2) := by rw [hrw]; ring
        _ ≤ (2 * Real.pi) ^ (2 * (-alphaE d s)) * ‖ξ‖ ^ (-(2 * alphaE d s)) *
              (1 * ‖σ.fourier ξ‖ ^ 2) := by
            gcongr
        _ ≤ (2 * Real.pi) ^ (2 * (-alphaE d s)) * (g1Hat s ξ / c) * (1 * ‖σ.fourier ξ‖ ^ 2) := by
            gcongr
        _ = C1 * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2) := by rw [hC1]; ring
    · have h2 : 2 ≤ ‖(4:ℝ)⁻¹ • ξ‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        linarith [not_lt.1 h8]
      rw [hchi_zero _ h2, zero_mul, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg hC1p.le (mul_nonneg hg0 (sq_nonneg _))
  have hreal2 : ∀ ξ : Euc d, ξ ≠ 0 →
      ‖lowFreq 4 σ.fourier ξ‖ ^ 2 ≤ C2 * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2) := by
    intro ξ hξ
    have ht : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hg0 : 0 ≤ g1Hat s ξ := g1Hat_nonneg hs0 hs2 ξ
    rw [hFnorm ξ]
    by_cases h8 : ‖ξ‖ < 8
    · have hg : c * ‖ξ‖ ^ (-(2 * alphaE d s)) ≤ g1Hat s ξ := hcl ξ hξ h8.le
      have hlow : c * 8 ^ (-(2 * alphaE d s)) ≤ g1Hat s ξ := by
        refine le_trans (mul_le_mul_of_nonneg_left ?_ hc.le) hg
        exact Real.rpow_le_rpow_of_nonpos ht h8.le (by linarith)
      have hinv : C2 * (c * 8 ^ (-(2 * alphaE d s))) = 1 := by
        rw [hC2]; field_simp
      have hle : 1 ≤ C2 * g1Hat s ξ :=
        calc (1 : ℝ) = C2 * (c * 8 ^ (-(2 * alphaE d s))) := hinv.symm
          _ ≤ C2 * g1Hat s ξ := mul_le_mul_of_nonneg_left hlow hC2p.le
      have hχ : chi ((4:ℝ)⁻¹ • ξ) ^ 2 ≤ 1 := by
        have := hchi1 ((4:ℝ)⁻¹ • ξ); have := hchi0 ((4:ℝ)⁻¹ • ξ); nlinarith
      have hw : 0 ≤ ‖σ.fourier ξ‖ ^ 2 := sq_nonneg _
      calc (chi ((4:ℝ)⁻¹ • ξ) * ‖σ.fourier ξ‖) ^ 2
          = chi ((4:ℝ)⁻¹ • ξ) ^ 2 * ‖σ.fourier ξ‖ ^ 2 := by ring
        _ ≤ 1 * ‖σ.fourier ξ‖ ^ 2 := by gcongr
        _ ≤ (C2 * g1Hat s ξ) * ‖σ.fourier ξ‖ ^ 2 := by gcongr
        _ = C2 * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2) := by ring
    · have h2 : 2 ≤ ‖(4:ℝ)⁻¹ • ξ‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        linarith [not_lt.1 h8]
      rw [hchi_zero _ h2, zero_mul, zero_pow two_ne_zero]
      exact mul_nonneg hC2p.le (mul_nonneg hg0 (sq_nonneg _))
  -- assembly in `ℝ≥0∞`
  have hsq : ∀ ξ : Euc d, ‖lowFreq 4 σ.fourier ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖lowFreq 4 σ.fourier ξ‖ ^ 2) := by
    intro ξ
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hnull : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ξ ≠ 0 := by
    have : Nontrivial (Euc d) := by
      have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      infer_instance
    have : NullSingletonClass (volume : Measure (Euc d)) := by infer_instance
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (0 : Euc d))] with ξ hξ
    exact fun h => hξ (by rw [h]; exact Set.mem_singleton _)
  have hnn : ∀ C : ℝ, 0 ≤ C → ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      0 ≤ C * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2) := fun C hC =>
    Filter.Eventually.of_forall fun ξ => mul_nonneg hC (mul_nonneg (g1Hat_nonneg hs0 hs2 ξ) (sq_nonneg _))
  have hH : homSqE (-alphaE d s) (lowFreq 4 σ.fourier) ≤
      ENNReal.ofReal (C1 * kerEnergy (g1 s) σ) := by
    unfold homSqE
    calc ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s))) *
            ‖lowFreq 4 σ.fourier ξ‖ₑ ^ 2
        ≤ ∫⁻ ξ, ENNReal.ofReal (C1 * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hnull] with ξ hξ
          rw [hsq ξ, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
          exact ENNReal.ofReal_le_ofReal (hreal1 ξ hξ)
      _ = ENNReal.ofReal (∫ ξ, C1 * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul C1) (hnn C1 hC1p.le)).symm
      _ = ENNReal.ofReal (C1 * kerEnergy (g1 s) σ) := by rw [integral_const_mul, hkey]
  have hS : sobSqE 0 (lowFreq 4 σ.fourier) ≤ ENNReal.ofReal (C2 * kerEnergy (g1 s) σ) := by
    unfold sobSqE
    calc ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (0:ℝ)) *
            ‖lowFreq 4 σ.fourier ξ‖ₑ ^ 2
        ≤ ∫⁻ ξ, ENNReal.ofReal (C2 * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hnull] with ξ hξ
          rw [Real.rpow_zero, ENNReal.ofReal_one, one_mul, hsq ξ]
          exact ENNReal.ofReal_le_ofReal (hreal2 ξ hξ)
      _ = ENNReal.ofReal (∫ ξ, C2 * (g1Hat s ξ * ‖σ.fourier ξ‖ ^ 2)) :=
          (ofReal_integral_eq_lintegral_ofReal (hint.const_mul C2) (hnn C2 hC2p.le)).symm
      _ = ENNReal.ofReal (C2 * kerEnergy (g1 s) σ) := by rw [integral_const_mul, hkey]
  calc homSqE (-alphaE d s) (lowFreq 4 σ.fourier) + sobSqE 0 (lowFreq 4 σ.fourier)
      ≤ ENNReal.ofReal (C1 * kerEnergy (g1 s) σ) + ENNReal.ofReal (C2 * kerEnergy (g1 s) σ) :=
        add_le_add hH hS
    _ = ENNReal.ofReal ((C1 + C2) * kerEnergy (g1 s) σ) := by
        rw [add_mul, ENNReal.ofReal_add (mul_nonneg hC1p.le hK) (mul_nonneg hC2p.le hK)]

/-- `(1.intro-control)` (`[N] L177-184`; "Combining `(3.Scoercive)` for `σ = ν` with Lemma 2.2 proves
`(1.intro-control)`", L407): `‖P_{≤4}ν‖²_{Ḣ^{-α}} + ‖μ‖²_{H^{-α}} + ∑_j n_j² ≲ Ec`. -/
theorem intro_control (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p → p⁻¹ + q⁻¹ = 1 →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp →
      ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
        homSqE (-alphaE d s) (lowFreq 4 (chargeOf X ρ).fourier) +
            sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 ρ) +
            ENNReal.ofReal (∑' j : Fin d → ℤ, occ X j ^ 2) ≤
          ENNReal.ofReal (C * (modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ))) := by
  obtain ⟨Cb, hCb, hEC⟩ := energy_control hd hs0 hsd
  obtain ⟨Cs, hCs, hSc⟩ := scoercive hd hs0 hsd
  refine ⟨2 * Cs + 3 * Cb, by linarith, fun p q hp hpq => ?_⟩
  obtain ⟨Cp0, hCp0, hCP⟩ := hEC p q hp hpq
  refine ⟨Cp0, hCp0, fun Cp hCp ρ hρ N X hN hX => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hCP Cp hCp ρ hρ N X hN hX
  obtain ⟨hK0, hT0, hI0⟩ := energy_terms_nonneg hd hs0 hsd ρ hρ hN X hX
  have hcharge := chargeOf_admissible ρ hρ hN X
  have hS := hSc (chargeOf X ρ) hcharge.1 hcharge.2.1 (fun _ => hcharge.2.2)
  set K := kerEnergy (g1 s) (chargeOf X ρ) with hKdef
  set I := ∫ x, ∫ y, fTrunc s 1 (x - y) * ρ x * ρ y with hIdef
  set Ec := modEnergy s X ρ + Cp * (1 / (N : ℝ) + normE p ρ) with hEcdef
  have hK2 : K ≤ 2 * Ec := by linarith
  have hI2 : I ≤ 2 * Ec := by linarith
  have hEc0 : 0 ≤ Ec := by linarith
  have hA := le_trans le_self_add hS
  have hB := h3
  have hC : ENNReal.ofReal (∑' j : Fin d → ℤ, occ X j ^ 2) ≤ ENNReal.ofReal (Cb * Ec) :=
    ENNReal.ofReal_le_ofReal h4
  have e1 := mul_le_mul_of_nonneg_left hK2 hCs.le
  have e2 := mul_le_mul_of_nonneg_left hI2 hCb.le
  have e3 : (2 * Cs + 3 * Cb) * Ec = Cs * (2 * Ec) + Cb * (2 * Ec) + Cb * Ec := by ring
  calc homSqE (-alphaE d s) (lowFreq 4 (chargeOf X ρ).fourier) + sobSqE (-alphaE d s)
        (HRS.PDE.ToolboxRd.fourierL2 ρ) + ENNReal.ofReal (∑' j : Fin d → ℤ, occ X j ^ 2)
      ≤ ENNReal.ofReal (Cs * K) + ENNReal.ofReal (Cb * I) + ENNReal.ofReal (Cb * Ec) :=
        add_le_add (add_le_add hA hB) hC
    _ = ENNReal.ofReal (Cs * K + Cb * I + Cb * Ec) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hCs.le hK0) (mul_nonneg hCb.le hI0),
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hCs.le hK0) (mul_nonneg hCb.le hI0))
            (mul_nonneg hCb.le hEc0)]
    _ ≤ ENNReal.ofReal ((2 * Cs + 3 * Cb) * Ec) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith

end HRS.Commutator.Whole
