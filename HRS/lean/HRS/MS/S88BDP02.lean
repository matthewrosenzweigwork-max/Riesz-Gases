import HRS.MS.S88BDP01
import HRS.MS.S88BDDefs

/-!
# S8.8.P02: centered particle variance and increment bounds

`s88_particle_second_moments`: for bounded `C²` tests the centered particle observable
`√N (μ_N(f) - ∫ f d m_N)` (`m_N` the first marginal of the law) is in `L²(P)`; its second moment is at most
`max(Cin,0) ‖P_μ f‖²_{L²(μ)}` (the variance input applied to `P_μ f`; by exchangeability `E μ_N(f) = ∫ f dm_N`), and the same
holds for the difference of two such observables, which is the observable of `f - g`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

section Particle

variable {d N : ℕ}

lemma s88_pair_empirical (hN : 1 ≤ N) {ψ : Euc d → ℝ} (hψ : Continuous ψ) (Y : EucConfig d N) :
    HRS.Whole.pair (HRS.Whole.empirical Y) ψ = (1 / (N : ℝ)) * ∑ i, ψ (Y i) := by
  unfold HRS.Whole.pair HRS.Whole.empirical
  rw [integral_smul_measure, integral_finset_sum_measure]
  · simp [ENNReal.toReal_inv, integral_dirac, Finset.sum_div, Finset.mul_sum]
  · intro i _
    exact integrable_dirac (by simp)

lemma s88_pair_empirical_bdd (hN : 1 ≤ N) {ψ : Euc d → ℝ} (hψ : Continuous ψ) {B : ℝ}
    (hB : ∀ x, |ψ x| ≤ B) (Y : EucConfig d N) :
    |HRS.Whole.pair (HRS.Whole.empirical Y) ψ| ≤ B := by
  rw [s88_pair_empirical hN hψ]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos (by positivity)]
  calc 1 / (N : ℝ) * |∑ i, ψ (Y i)| ≤ 1 / (N : ℝ) * ∑ i : Fin N, B :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => hB _)) (by positivity)
    _ = B := by simp; field_simp

/-- Exchangeability identifies the mean empirical functional with the first marginal. -/
lemma s88_mean_empirical {Ω : Type} [MeasurableSpace Ω] (hN : 1 ≤ N)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → EucConfig d N) (hX : AEMeasurable X P)
    (hex : HRS.Whole.IsExchangeable (law P X)) {ψ : Euc d → ℝ} (hψ : Continuous ψ) {B : ℝ}
    (hB : ∀ x, |ψ x| ≤ B) :
    ∫ z, HRS.Whole.pair (HRS.Whole.empirical (X z)) ψ ∂P =
      ∫ x, ψ x ∂(HRS.Whole.firstMarginal (law P X)) := by
  have hN' : 0 < N := hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set Q : Measure (EucConfig d N) := law P X with hQ
  have hevc : ∀ i : Fin N, Continuous fun Y : EucConfig d N => ψ (Y i) :=
    fun i => hψ.comp (continuous_apply i)
  -- each coordinate has the same mean
  have hcoord : ∀ i : Fin N, ∫ z, ψ (X z i) ∂P = ∫ x, ψ x ∂(HRS.Whole.firstMarginal Q) := by
    intro i
    have h1 : ∫ z, ψ (X z i) ∂P = ∫ Y, ψ (Y i) ∂Q :=
      (integral_map hX (hevc i).aestronglyMeasurable).symm
    have h2 : ∫ x, ψ x ∂(HRS.Whole.firstMarginal Q) = ∫ Y, ψ (Y ⟨0, hN'⟩) ∂Q := by
      unfold HRS.Whole.firstMarginal
      rw [dif_pos hN']
      exact integral_map (measurable_pi_apply (⟨0, hN'⟩ : Fin N)).aemeasurable hψ.aestronglyMeasurable
    have hT : Measurable fun Y : EucConfig d N => Y ∘ (Equiv.swap i ⟨0, hN'⟩) :=
      measurable_pi_iff.2 fun j => measurable_pi_apply _
    have h3 := hex (Equiv.swap i ⟨0, hN'⟩)
    have h4 : ∫ Y, ψ (Y ⟨0, hN'⟩) ∂(Q.map fun Y => Y ∘ (Equiv.swap i ⟨0, hN'⟩)) =
        ∫ Y, ψ (Y i) ∂Q := by
      rw [integral_map hT.aemeasurable (hevc ⟨0, hN'⟩).aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
      simp [Equiv.swap_apply_right]
    rw [h1, h2, ← h4, h3]
  have hint : ∀ i : Fin N, Integrable (fun z => ψ (X z i)) P := by
    intro i
    have hm : AEMeasurable (fun z => X z i) P := (measurable_pi_apply i).comp_aemeasurable hX
    refine Integrable.of_bound (C := B) (hψ.measurable.comp_aemeasurable hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using hB _
  calc ∫ z, HRS.Whole.pair (HRS.Whole.empirical (X z)) ψ ∂P
      = ∫ z, (1 / (N : ℝ)) * ∑ i, ψ (X z i) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => s88_pair_empirical hN hψ _)
    _ = (1 / (N : ℝ)) * ∑ i, ∫ z, ψ (X z i) ∂P := by
        rw [integral_const_mul, integral_finset_sum _ fun i _ => hint i]
    _ = _ := by
        simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

lemma s88_integrable_of_bdd {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] {ψ : α → ℝ} (hψ : Continuous ψ) {B : ℝ}
    (hB : ∀ x, |ψ x| ≤ B) : Integrable ψ ν :=
  Integrable.of_bound (C := B) hψ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)

lemma s88_particle_sub {Ω : Type} [MeasurableSpace Ω] (hN : 1 ≤ N)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → EucConfig d N) (hX : AEMeasurable X P)
    {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g) {Bf Bg : ℝ}
    (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) (z : Ω) :
    s88Particle P X (fun y => f y - g y) z = s88Particle P X f z - s88Particle P X g z := by
  haveI := s88_firstMarginal_prob hN P X hX
  unfold s88Particle
  rw [integral_sub (s88_integrable_of_bdd _ hf hBf) (s88_integrable_of_bdd _ hg hBg),
    s88_pair_empirical hN (show Continuous (fun y => f y - g y) from hf.sub hg),
    s88_pair_empirical hN hf, s88_pair_empirical hN hg]
  simp only [Finset.sum_sub_distrib]
  ring

lemma s88_particle_single {Ω : Type} [MeasurableSpace Ω] (hN : 1 ≤ N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (Cin : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → EucConfig d N) (hX : AEMeasurable X P)
    (hex : HRS.Whole.IsExchangeable (law P X))
    (hvar : ∀ f : Euc d → ℝ, MemLp f 2 μ →
      evariance (fun z => HRS.Whole.linStat f (X z)) P ≤
        ENNReal.ofReal (Cin / N * ∫ x, f x ^ 2 ∂μ))
    {h : Euc d → ℝ} (hc : Continuous h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) :
    MemLp (s88Particle P X h) 2 P ∧
      (∫⁻ z, ENNReal.ofReal ((s88Particle P X h z) ^ 2) ∂P) ≤
        ENNReal.ofReal (max Cin 0 * ∫ x, HRS.Whole.projMean μ h x ^ 2 ∂μ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set L : Ω → ℝ := fun z => HRS.Whole.pair (HRS.Whole.empirical (X z)) h with hL
  set m : ℝ := ∫ x, h x ∂(HRS.Whole.firstMarginal (law P X)) with hm
  have hLm : ∫ z, L z ∂P = m := s88_mean_empirical hN P X hX hex hc hB
  have hLaem : AEMeasurable L P := by
    have : L = fun z => (1 / (N : ℝ)) * ∑ i, h (X z i) := funext fun z => s88_pair_empirical hN hc _
    rw [this]
    have hs : AEMeasurable (fun z => ∑ i, h (X z i)) P :=
      Finset.aemeasurable_fun_sum _ fun i _ =>
        hc.measurable.comp_aemeasurable ((measurable_pi_apply i).comp_aemeasurable hX)
    exact hs.const_mul _
  have hLb : ∀ z, |L z| ≤ B := fun z => s88_pair_empirical_bdd hN hc hB _
  have hLmem : MemLp L 2 P := MemLp.of_bound hLaem.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hLb z)
  have hLint : Integrable L P := hLmem.integrable one_le_two
  have hpart : ∀ z, s88Particle P X h z = Real.sqrt N * (L z - m) := fun z => rfl
  have hmem : MemLp (s88Particle P X h) 2 P := by
    have : s88Particle P X h = fun z => Real.sqrt N * (L z - m) := funext hpart
    rw [this]
    exact (hLmem.sub (memLp_const m)).const_mul _
  refine ⟨hmem, ?_⟩
  -- the variance input applied to the centered test
  obtain ⟨⟨hmemh, -⟩, -⟩ := u11_projMean_bound μ hc hB
  set c : ℝ := HRS.Whole.pair μ h with hcdef
  have hcont' : Continuous (HRS.Whole.projMean μ h) := hc.sub continuous_const
  have hlin : ∀ z, HRS.Whole.linStat (HRS.Whole.projMean μ h) (X z) = L z - c := by
    intro z
    unfold HRS.Whole.linStat
    rw [s88_pair_empirical hN hcont']
    simp only [hL, HRS.Whole.projMean, ← hcdef]
    rw [s88_pair_empirical hN hc, Finset.sum_sub_distrib]
    simp
    field_simp
  have hv := hvar _ hmemh
  have hev : evariance (fun z => HRS.Whole.linStat (HRS.Whole.projMean μ h) (X z)) P =
      ∫⁻ z, ‖L z - m‖ₑ ^ 2 ∂P := by
    unfold evariance
    have : (fun z => HRS.Whole.linStat (HRS.Whole.projMean μ h) (X z)) = fun z => L z - c :=
      funext hlin
    rw [this]
    have hmean : ∫ z, (L z - c) ∂P = m - c := by
      rw [integral_sub hLint (integrable_const c), hLm]; simp
    simp only [hmean]
    refine lintegral_congr fun z => ?_
    rw [show L z - c - (m - c) = L z - m by ring]
  rw [hev] at hv
  have hE : ∀ x : ℝ, ENNReal.ofReal (x ^ 2) = ‖x‖ₑ ^ 2 := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]
  have hI : 0 ≤ ∫ x, HRS.Whole.projMean μ h x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  calc ∫⁻ z, ENNReal.ofReal ((s88Particle P X h z) ^ 2) ∂P
      = ∫⁻ z, ENNReal.ofReal (N : ℝ) * ‖L z - m‖ₑ ^ 2 ∂P := by
        refine lintegral_congr fun z => ?_
        rw [hpart, mul_pow, Real.sq_sqrt hN0.le, ENNReal.ofReal_mul hN0.le, hE]
    _ = ENNReal.ofReal (N : ℝ) * ∫⁻ z, ‖L z - m‖ₑ ^ 2 ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (N : ℝ) * ENNReal.ofReal (Cin / N * ∫ x, HRS.Whole.projMean μ h x ^ 2 ∂μ) :=
        by gcongr
    _ = ENNReal.ofReal (Cin * ∫ x, HRS.Whole.projMean μ h x ^ 2 ∂μ) := by
        rw [← ENNReal.ofReal_mul hN0.le]
        congr 1
        field_simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hI)

end Particle

theorem s88_particle_second_moments {d N : ℕ} (hN : 1 ≤ N)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (Cin : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → EucConfig d N) (hX : AEMeasurable X P)
    (hex : HRS.Whole.IsExchangeable (law P X))
    (hvar : ∀ f : Euc d → ℝ, MemLp f 2 μ →
      evariance (fun z => HRS.Whole.linStat f (X z)) P ≤
        ENNReal.ofReal (Cin / N * ∫ x, f x ^ 2 ∂μ))
    (f g : Euc d → ℝ) (hf : MemCb 2 f) (hg : MemCb 2 g) :
    MemLp (s88Particle P X f) 2 P ∧ MemLp (s88Particle P X g) 2 P ∧
      (∫⁻ z, ENNReal.ofReal ((s88Particle P X f z) ^ 2) ∂P) ≤
        ENNReal.ofReal (max Cin 0 * ∫ x, HRS.Whole.projMean μ f x ^ 2 ∂μ) ∧
      (∫⁻ z, ENNReal.ofReal ((s88Particle P X f z - s88Particle P X g z) ^ 2) ∂P) ≤
        ENNReal.ofReal (max Cin 0 * ∫ x, HRS.Whole.projMean μ (fun y => f y - g y) x ^ 2 ∂μ) := by
  have bf : Continuous f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B := by
    refine ⟨hf.1.continuous, ?_⟩
    obtain ⟨B, hB⟩ := hf.2 0 (by norm_num)
    refine ⟨B, fun x => ?_⟩
    have := hB ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this
  have bg : Continuous g ∧ ∃ B : ℝ, ∀ x, |g x| ≤ B := by
    refine ⟨hg.1.continuous, ?_⟩
    obtain ⟨B, hB⟩ := hg.2 0 (by norm_num)
    refine ⟨B, fun x => ?_⟩
    have := hB ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this
  obtain ⟨hfc, Bf, hBf⟩ := bf
  obtain ⟨hgc, Bg, hBg⟩ := bg
  obtain ⟨m1, b1⟩ := s88_particle_single hN μ Cin P X hX hex hvar hfc hBf
  obtain ⟨m2, -⟩ := s88_particle_single hN μ Cin P X hX hex hvar hgc hBg
  have hdc : Continuous (fun y => f y - g y) := hfc.sub hgc
  obtain ⟨-, b3⟩ := s88_particle_single hN μ Cin P X hX hex hvar hdc
    (B := Bf + Bg) (fun x => (abs_sub _ _).trans (add_le_add (hBf x) (hBg x)))
  refine ⟨m1, m2, b1, ?_⟩
  have : ∀ z, s88Particle P X f z - s88Particle P X g z =
      s88Particle P X (fun y => f y - g y) z := fun z =>
    (s88_particle_sub hN P X hX hfc hgc hBf hBg z).symm
  simp_rw [this]
  exact b3

end HRS.MS.S88Breakdown
