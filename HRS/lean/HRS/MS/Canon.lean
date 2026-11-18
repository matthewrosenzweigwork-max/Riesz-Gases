import HRS.Whole.Basic

/-!
# MS-CANON: the canonical Gibbs ensemble is the modulated Gibbs law at the thermal density

Proves the frozen statement `HRS.Whole.canonicalGibbs_eq_modulatedGibbs` (`HRS/Whole/Basic.lean`)
as `HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof`.

Route.  Write `μ = ρ dx` and `Z = ∫ exp(-β (V + g*μ))`, so `ρ x = exp(-β (V x + g*μ x)) / Z`
with `Z > 0`.  Since `g` is even, `N · F_N(X,μ) = N⁻¹ ∑_{i<j} g(x_i-x_j) - ∑_i g*μ(x_i) + (N/2) E`
with `E = ∬ g dμ dμ`, hence pointwise
`∏_i ρ(x_i) · exp(-β N F_N(X,μ)) = Z^{-N} exp(-(βN/2) E) · exp(-β H_N(X))`.
So the two densities are proportional, and so are the normalisers; the Gibbs laws agree.
No measurability of `g` is assumed: all `withDensity` and Bochner lemmas used accept arbitrary
integrands.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.MS.Canon

open HRS.Whole

variable {d N : ℕ}

/-- Symmetric double sum: for even `g`, `∑_i ∑_{j≠i} g(x_i-x_j) = 2 ∑_i ∑_{j>i} g(x_i-x_j)`. -/
lemma cn_sum_erase_eq (g : Euc d → ℝ) (hg : ∀ x, g (-x) = g x) (X : Fin N → Euc d) :
    ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
      = 2 * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j) := by
  have hsym : ∀ i j : Fin N, g (X j - X i) = g (X i - X j) := by
    intro i j
    have h := hg (X i - X j)
    rw [neg_sub] at h
    exact h
  have hA : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
      = ∑ i : Fin N, ∑ j : Fin N,
          ((if i < j then g (X i - X j) else 0) + (if j < i then g (X i - X j) else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp
    · simp [h, h.ne, not_lt.2 h.le]
  have hB : ∑ i : Fin N, ∑ j : Fin N, (if j < i then g (X i - X j) else 0)
      = ∑ i : Fin N, ∑ j : Fin N, (if i < j then g (X i - X j) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs with h
    · exact hsym a b
    · rfl
  rw [hA]
  simp only [Finset.sum_add_distrib]
  rw [hB]
  simp only [Finset.sum_filter]
  ring

/-- `N · F_N(X,μ)` in the form used for the pointwise identity (valid also for `N = 0`). -/
lemma cn_N_mul_modulatedEnergy (g : Euc d → ℝ) (hg : ∀ x, g (-x) = g x) (X : Fin N → Euc d)
    (μ : Measure (Euc d)) :
    (N : ℝ) * HRS.Whole.modulatedEnergy g X μ
      = (1 / (N : ℝ)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j)
        - ∑ i : Fin N, HRS.Whole.convMeasure g μ (X i) + ((N : ℝ) / 2) * HRS.Whole.energyPairing g μ μ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    unfold HRS.Whole.modulatedEnergy
    rw [cn_sum_erase_eq g hg X]
    field_simp

/-- The pointwise identity `∏ ρ(x_i) · exp(-β N F_N) = Z^{-N} exp(-(βN/2) E) exp(-β H_N)`
for `ρ = exp(-β(V + g*μ))/Z`. -/
lemma cn_pointwise (g V : Euc d → ℝ) (β : ℝ) (μ : Measure (Euc d)) (ρ : Euc d → ℝ) (Z : ℝ)
    (hg : ∀ x, g (-x) = g x)
    (hρ : ∀ x, ρ x = Real.exp (-β * (V x + HRS.Whole.convMeasure g μ x)) / Z) (X : Fin N → Euc d) :
    (∏ i, ρ (X i)) * Real.exp (-β * (N : ℝ) * HRS.Whole.modulatedEnergy g X μ)
      = Real.exp (-(β * (N : ℝ) / 2) * HRS.Whole.energyPairing g μ μ) / Z ^ N
        * Real.exp (-β * HRS.Whole.canonicalHamiltonian g V X) := by
  have hprod : ∏ i, ρ (X i)
      = Real.exp (∑ i, -β * (V (X i) + HRS.Whole.convMeasure g μ (X i))) / Z ^ N := by
    simp only [hρ]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Real.exp_sum]
  have hsum : ∑ i, -β * (V (X i) + HRS.Whole.convMeasure g μ (X i))
      = -β * ∑ i, V (X i) + -β * ∑ i, HRS.Whole.convMeasure g μ (X i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hK := cn_N_mul_modulatedEnergy g hg X μ
  have hexp : Real.exp (∑ i, -β * (V (X i) + HRS.Whole.convMeasure g μ (X i)))
      * Real.exp (-β * (N : ℝ) * HRS.Whole.modulatedEnergy g X μ)
      = Real.exp (-(β * (N : ℝ) / 2) * HRS.Whole.energyPairing g μ μ)
        * Real.exp (-β * HRS.Whole.canonicalHamiltonian g V X) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hsum]
    unfold HRS.Whole.canonicalHamiltonian
    linear_combination (-β) * hK
  rw [hprod, div_mul_eq_mul_div, div_mul_eq_mul_div, hexp]

/-- The thermal normaliser is positive. -/
lemma cn_Z_pos (g V : Euc d → ℝ) (β : ℝ) (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsThermalDensity g V β ρ) :
    0 < ∫ y, Real.exp (-β * (V y + HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) y)) := by
  unfold HRS.Whole.IsThermalDensity at hρ
  obtain ⟨hprob, hfix⟩ := hρ
  have hnn : 0 ≤ ∫ y, Real.exp (-β * (V y + HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) y)) :=
    integral_nonneg fun y => (Real.exp_pos _).le
  refine lt_of_le_of_ne hnn ?_
  intro h0
  have h1 : ∀ x, ρ x = 0 := fun x => by rw [hfix x, ← h0, div_zero]
  have h2 := hprob.integral_one
  simp [h1] at h2

lemma cn_integrable_of_prob (ρ : Euc d → ℝ) (hprob : HRS.Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have h1 := hprob.integral_one
  rw [integral_undef h] at h1
  norm_num at h1

lemma cn_withDensityReal_apply (ρ : Euc d → ℝ) (h0 : ∀ x, 0 ≤ ρ x) (hi : Integrable ρ)
    {S : Set (Euc d)} (hS : MeasurableSet S) :
    HRS.Whole.withDensityReal ρ S = ENNReal.ofReal (∫ x, S.indicator ρ x) := by
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  have hpt : ∀ x, S.indicator (fun x => ENNReal.ofReal (ρ x)) x
      = ENNReal.ofReal (S.indicator ρ x) := by
    intro x
    by_cases h : x ∈ S <;> simp [h]
  simp only [hpt]
  rw [ofReal_integral_eq_lintegral_ofReal (hi.indicator hS)
    (ae_of_all _ fun x => Set.indicator_nonneg (fun y _ => h0 y) x)]

/-- The product of one-dimensional densities is the density of the product measure. -/
lemma cn_pi_withDensityReal (ρ : Euc d → ℝ) (h0 : ∀ x, 0 ≤ ρ x) (hi : Integrable ρ) :
    Measure.pi (fun _ : Fin N => HRS.Whole.withDensityReal ρ)
      = (volume : Measure (Fin N → Euc d)).withDensity
          (fun X => ENNReal.ofReal (∏ i, ρ (X i))) := by
  haveI : IsFiniteMeasure (HRS.Whole.withDensityReal ρ) := by
    constructor
    rw [HRS.Whole.withDensityReal, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0)]
    exact ENNReal.ofReal_lt_top
  apply Measure.pi_eq
  intro s hs
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : ∀ X : Fin N → Euc d,
      (Set.univ.pi s).indicator (fun X => ENNReal.ofReal (∏ i, ρ (X i))) X
        = ∏ i, ENNReal.ofReal ((s i).indicator ρ (X i)) := by
    intro X
    by_cases hX : ∀ i, X i ∈ s i
    · rw [Set.indicator_of_mem (Set.mem_univ_pi.2 hX),
        ENNReal.ofReal_prod_of_nonneg (fun i _ => h0 (X i))]
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem (hX i)]
    · push_neg at hX
      obtain ⟨i, hi'⟩ := hX
      have h1 : (Set.univ.pi s).indicator (fun X => ENNReal.ofReal (∏ i, ρ (X i))) X = 0 :=
        Set.indicator_of_notMem (fun h => hi' (Set.mem_univ_pi.1 h i)) _
      have h2 : ∏ j, ENNReal.ofReal ((s j).indicator ρ (X j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Set.indicator_of_notMem hi']; simp)
      rw [h1, h2]
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  simp only [hind]
  have hfac : ∀ X : Fin N → Euc d, ∏ i, ENNReal.ofReal ((s i).indicator ρ (X i))
      = ENNReal.ofReal (∏ i, (s i).indicator ρ (X i)) := fun X =>
    (ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Set.indicator_nonneg (fun y _ => h0 y) (X i))).symm
  simp only [hfac]
  have hint : Integrable (fun X : Fin N → Euc d => ∏ i, (s i).indicator ρ (X i))
      (volume : Measure (Fin N → Euc d)) :=
    Integrable.fintype_prod (μ := fun _ => (volume : Measure (Euc d)))
      (fun i => hi.indicator (hs i))
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun X =>
    Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun y _ => h0 y) (X i))]
  rw [integral_fintype_prod_volume_eq_prod (fun i x => (s i).indicator ρ x)]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun x => Set.indicator_nonneg (fun y _ => h0 y) x)]
  apply Finset.prod_congr rfl
  intro i _
  rw [cn_withDensityReal_apply ρ h0 hi (hs i)]

lemma cn_withDensity_withDensity {α : Type*} [MeasurableSpace α] (L : Measure α)
    (p : α → ENNReal) (hp : Measurable p) (hpt : ∀ x, p x < ⊤) (f : α → ℝ) :
    (L.withDensity p).withDensity (fun x => ENNReal.ofReal (f x))
      = L.withDensity (fun x => p x * ENNReal.ofReal (f x)) := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, withDensity_apply _ hs]
  exact setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable L hp _ hs
    (ae_of_all _ fun x => hpt x)

lemma cn_withDensity_const_mul {α : Type*} [MeasurableSpace α] (L : Measure α) (c : ENNReal)
    (hc : c ≠ ⊤) (q : α → ENNReal) :
    L.withDensity (fun x => c * q x) = c • L.withDensity q := by
  refine Measure.ext fun s hs => ?_
  rw [withDensity_apply _ hs, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    lintegral_const_mul' c q hc]

lemma cn_ennreal_aux (a b : ENNReal) (ha0 : a ≠ 0) (ha : a ≠ ⊤) :
    (a * b)⁻¹ * a = b⁻¹ := by
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl ha), mul_comm (a⁻¹ * b⁻¹) a, ← mul_assoc,
    ENNReal.mul_inv_cancel ha0 ha, one_mul]

/-- `P_{N,β} = Q_{N,β}(μ_β)` exactly for the thermal equilibrium density (S lines 1375-1378;
package S-STAT-01).  Proof of the frozen statement `HRS.Whole.canonicalGibbs_eq_modulatedGibbs`. -/
theorem canonicalGibbs_eq_modulatedGibbs_proof (g V : Euc d → ℝ) (β : ℝ) (ρ : Euc d → ℝ)
    (hρ : HRS.Whole.IsThermalDensity g V β ρ) (hg : ∀ x, g (-x) = g x)
    (hint : ∀ x, Integrable (fun y => g (x - y)) (HRS.Whole.withDensityReal ρ)) :
    HRS.Whole.canonicalGibbs g V N β = HRS.Whole.modulatedGibbs g N β (HRS.Whole.withDensityReal ρ) := by
  have hZ := cn_Z_pos g V β ρ hρ
  unfold HRS.Whole.IsThermalDensity at hρ
  obtain ⟨hprob, hfix⟩ := hρ
  have hρ0 : ∀ x, 0 ≤ ρ x := hprob.nonneg
  have hρi : Integrable ρ := cn_integrable_of_prob ρ hprob
  have hP := cn_pi_withDensityReal (N := N) ρ hρ0 hρi
  generalize hZdef : (∫ y, Real.exp (-β * (V y + HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) y))) = Z
    at hZ hfix
  have hR : ∀ X : Fin N → Euc d,
      (∏ i, ρ (X i)) * Real.exp (-β * (N : ℝ) * HRS.Whole.modulatedEnergy g X (HRS.Whole.withDensityReal ρ))
        = Real.exp (-(β * (N : ℝ) / 2) * HRS.Whole.energyPairing g (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ))
          / Z ^ N * Real.exp (-β * HRS.Whole.canonicalHamiltonian g V X) :=
    fun X => cn_pointwise g V β (HRS.Whole.withDensityReal ρ) ρ Z hg hfix X
  have hkpos : 0 < Real.exp (-(β * (N : ℝ) / 2) * HRS.Whole.energyPairing g (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ))
      / Z ^ N :=
    div_pos (Real.exp_pos _) (pow_pos hZ N)
  generalize hk : Real.exp (-(β * (N : ℝ) / 2) * HRS.Whole.energyPairing g (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ))
      / Z ^ N = k at hR hkpos
  have hk0 : 0 < k := hkpos
  have hpm : Measurable (fun X : Fin N → Euc d => ENNReal.ofReal (∏ i, ρ (X i))) :=
    Measurable.ennreal_ofReal (Finset.measurable_prod _ fun i _ =>
      hprob.measurable.comp (measurable_pi_apply i))
  have hnorm : HRS.Whole.gibbsNormalizer g N β (HRS.Whole.withDensityReal ρ)
      = k * HRS.Whole.canonicalPartition g V N β := by
    unfold HRS.Whole.gibbsNormalizer HRS.Whole.canonicalPartition
    rw [hP, integral_withDensity_eq_integral_toReal_smul₀ hpm.aemeasurable
      (ae_of_all _ fun X => ENNReal.ofReal_lt_top), ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun X => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hρ0 (X i))]
    exact hR X
  have hfun : (fun X : Fin N → Euc d => ENNReal.ofReal (∏ i, ρ (X i))
        * ENNReal.ofReal (Real.exp (-β * (N : ℝ) * HRS.Whole.modulatedEnergy g X (HRS.Whole.withDensityReal ρ))))
      = fun X => ENNReal.ofReal k
        * ENNReal.ofReal (Real.exp (-β * HRS.Whole.canonicalHamiltonian g V X)) := by
    funext X
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hρ0 (X i)),
      ← ENNReal.ofReal_mul hk0.le, hR X]
  have hM : (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρ).withDensity
      (fun X => ENNReal.ofReal (Real.exp (-β * (N : ℝ) * HRS.Whole.modulatedEnergy g X (HRS.Whole.withDensityReal ρ))))
      = ENNReal.ofReal k • (volume : Measure (Fin N → Euc d)).withDensity
          (fun X => ENNReal.ofReal (Real.exp (-β * HRS.Whole.canonicalHamiltonian g V X))) := by
    rw [hP, cn_withDensity_withDensity _ _ hpm (fun _ => ENNReal.ofReal_lt_top) _, hfun,
      cn_withDensity_const_mul _ _ ENNReal.ofReal_ne_top]
  unfold HRS.Whole.canonicalGibbs HRS.Whole.modulatedGibbs
  rw [hM, hnorm]
  have ha0 : ENNReal.ofReal k ≠ 0 := (ENNReal.ofReal_pos.2 hk0).ne'
  rw [smul_smul, ENNReal.ofReal_mul hk0.le, cn_ennreal_aux _ _ ha0 ENNReal.ofReal_ne_top]

end HRS.MS.Canon

example := (@HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof :
  type_of% @HRS.Whole.canonicalGibbs_eq_modulatedGibbs)
