import HRS.Prob.Metrics

/-!
# Coupling lemmas for reweighted laws (work package STAT-4.21)

Total-variation style couplings: two laws sharing a common part are coupled by the diagonal on
the common part and the (normalised) product of the remainders.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.StaticLimitAux

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]

theorem inv_smul_smul_of_univ (θ : ℝ≥0∞) (σ : Measure B) (hσ : σ Set.univ = θ) (hθ : θ ≠ ∞) :
    θ⁻¹ • (θ • σ) = σ := by
  by_cases h0 : θ = 0
  · have : σ = 0 := Measure.measure_univ_eq_zero.mp (hσ.trans h0)
    simp [this]
  · rw [smul_smul, ENNReal.inv_mul_cancel h0 hθ, one_smul]

theorem wassersteinE_two_le_common (ρ₀ σ₁ σ₂ : Measure B) [IsFiniteMeasure σ₁]
    [IsFiniteMeasure σ₂] (θ : ℝ≥0∞) (h1 : σ₁ Set.univ = θ) (h2 : σ₂ Set.univ = θ) :
    wassersteinE 2 (ρ₀ + σ₁) (ρ₀ + σ₂) ≤
      (2 * ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂σ₁ + 2 * ∫⁻ v, ENNReal.ofReal (‖v‖ ^ 2) ∂σ₂) ^
        (1 / (2 : ℝ)) := by
  have hθfin : θ ≠ ∞ := h1 ▸ measure_ne_top σ₁ _
  have hdiag : Measurable (fun u : B => (u, u)) := measurable_id.prodMk measurable_id
  set κ : Measure (B × B) := ρ₀.map (fun u => (u, u)) + θ⁻¹ • σ₁.prod σ₂ with hκ
  have hcoup : IsCoupling κ (ρ₀ + σ₁) (ρ₀ + σ₂) := by
    constructor
    · rw [hκ, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_fst_prod,
        Measure.map_map measurable_fst hdiag, h2]
      have : (Prod.fst ∘ fun u : B => (u, u)) = id := rfl
      rw [this, Measure.map_id, inv_smul_smul_of_univ θ σ₁ h1 hθfin]
      exact measurable_fst.aemeasurable
    · rw [hκ, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_snd_prod,
        Measure.map_map measurable_snd hdiag, h1]
      have : (Prod.snd ∘ fun u : B => (u, u)) = id := rfl
      rw [this, Measure.map_id, inv_smul_smul_of_univ θ σ₂ h2 hθfin]
      exact measurable_snd.aemeasurable
  refine (wassersteinE_le_cost hcoup).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hpt : ∀ u v : B, ENNReal.ofReal (‖u - v‖ ^ (2 : ℝ)) ≤
      2 * ENNReal.ofReal (‖u‖ ^ 2) + 2 * ENNReal.ofReal (‖v‖ ^ 2) := by
    intro u v
    rw [Real.rpow_two]
    have h : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
      have h' : ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le u v) 2
      nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
    calc _ ≤ ENNReal.ofReal (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) := ENNReal.ofReal_le_ofReal h
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp
  have hmf : Measurable fun u : B => ENNReal.ofReal (‖u‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)
  have hcost : Measurable fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.pow_const _)
  rw [hκ, lintegral_add_measure, lintegral_map hcost hdiag, lintegral_smul_measure,
    lintegral_prod _ hcost.aemeasurable]
  have h0 : (∫⁻ u : B, ENNReal.ofReal (‖(u, u).1 - (u, u).2‖ ^ (2 : ℝ)) ∂ρ₀) = 0 := by
    simp
  rw [h0, zero_add]
  have hA : ∫⁻ u, ∫⁻ v, ENNReal.ofReal (‖(u, v).1 - (u, v).2‖ ^ (2 : ℝ)) ∂σ₂ ∂σ₁ ≤
      θ * (2 * ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂σ₁ + 2 * ∫⁻ v, ENNReal.ofReal (‖v‖ ^ 2) ∂σ₂) := by
    calc _ ≤ ∫⁻ u, ∫⁻ v, (2 * ENNReal.ofReal (‖u‖ ^ 2) + 2 * ENNReal.ofReal (‖v‖ ^ 2)) ∂σ₂ ∂σ₁ :=
          lintegral_mono fun u => lintegral_mono fun v => hpt u v
      _ = ∫⁻ u, (2 * ENNReal.ofReal (‖u‖ ^ 2) * θ + 2 * ∫⁻ v, ENNReal.ofReal (‖v‖ ^ 2) ∂σ₂) ∂σ₁ := by
          refine lintegral_congr fun u => ?_
          rw [lintegral_add_left measurable_const, lintegral_const, h2,
            lintegral_const_mul _ hmf]
      _ = θ * (2 * ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂σ₁ + 2 * ∫⁻ v, ENNReal.ofReal (‖v‖ ^ 2) ∂σ₂) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, h1,
            lintegral_mul_const _ (hmf.const_mul 2), lintegral_const_mul _ hmf]
          ring
  refine (mul_le_mul_right hA θ⁻¹).trans ?_
  by_cases h0 : θ = 0
  · simp [h0]
  · rw [← mul_assoc, ENNReal.inv_mul_cancel h0 hθfin, one_mul]

theorem wassersteinE_two_map_le {B' : Type*} [NormedAddCommGroup B'] [NormedSpace ℝ B']
    [MeasurableSpace B'] [BorelSpace B'] [SecondCountableTopology B']
    (T : B → B') (hT : Measurable T) (hL : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (P Q : Measure B) :
    wassersteinE 2 (P.map T) (Q.map T) ≤ wassersteinE 2 P Q := by
  refine le_iInf fun π => ?_
  have hTT : Measurable (fun z : B × B => (T z.1, T z.2)) :=
    (hT.comp measurable_fst).prodMk (hT.comp measurable_snd)
  have hc : IsCoupling (π.1.map (fun z : B × B => (T z.1, T z.2))) (P.map T) (Q.map T) := by
    constructor
    · have := congrArg (Measure.map T) π.2.1
      rw [Measure.map_map measurable_fst hTT, ← this, Measure.map_map hT measurable_fst]; rfl
    · have := congrArg (Measure.map T) π.2.2
      rw [Measure.map_map measurable_snd hTT, ← this, Measure.map_map hT measurable_snd]; rfl
  refine (wassersteinE_le_cost hc).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hcost : Measurable fun z : B' × B' => ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.pow_const _)
  rw [lintegral_map hcost hTT]
  refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
  exact Real.rpow_le_rpow (norm_nonneg _) (hL _ _) (by norm_num)

theorem wassersteinE_two_reweight [CompleteSpace B] (π₀ : Measure (B × B)) [IsProbabilityMeasure π₀]
    (F₁ F₂ : B × B → ℝ≥0∞) (h1 : Measurable F₁) (h2 : Measurable F₂)
    (hF₁ : ∫⁻ z, F₁ z ∂π₀ = 1) (hF₂ : ∫⁻ z, F₂ z ∂π₀ = 1) :
    wassersteinE 2 ((π₀.withDensity F₁).map Prod.fst) ((π₀.withDensity F₂).map Prod.snd) ≤
      (∫⁻ z, F₁ z * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀) ^ (1 / (2 : ℝ)) +
      (2 * ∫⁻ z, ((F₁ z - min (F₁ z) (F₂ z)) + (F₂ z - min (F₁ z) (F₂ z))) *
          ENNReal.ofReal (‖z.2‖ ^ 2) ∂π₀) ^ (1 / (2 : ℝ)) := by
  set P₁ := π₀.withDensity F₁ with hP₁
  set P₂ := π₀.withDensity F₂ with hP₂
  have hprob : ∀ (F : B × B → ℝ≥0∞), Measurable F → ∫⁻ z, F z ∂π₀ = 1 →
      IsProbabilityMeasure (π₀.withDensity F) := by
    intro F hF hF1
    exact ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hF1]⟩
  haveI := hprob F₁ h1 hF₁
  haveI := hprob F₂ h2 hF₂
  have hmeasMin : Measurable fun z => min (F₁ z) (F₂ z) := h1.min h2
  have hr1 : Measurable fun z => F₁ z - min (F₁ z) (F₂ z) := h1.sub hmeasMin
  have hr2 : Measurable fun z => F₂ z - min (F₁ z) (F₂ z) := h2.sub hmeasMin
  set P₀ := π₀.withDensity (fun z => min (F₁ z) (F₂ z)) with hP₀
  set σ₁ := π₀.withDensity (fun z => F₁ z - min (F₁ z) (F₂ z)) with hσ₁
  set σ₂ := π₀.withDensity (fun z => F₂ z - min (F₁ z) (F₂ z)) with hσ₂
  have e1 : P₁ = P₀ + σ₁ := by
    rw [hP₁, hP₀, hσ₁, ← withDensity_add_left hmeasMin]
    congr 1; funext z; exact (add_tsub_cancel_of_le (min_le_left _ _)).symm
  have e2 : P₂ = P₀ + σ₂ := by
    rw [hP₂, hP₀, hσ₂, ← withDensity_add_left hmeasMin]
    congr 1; funext z; exact (add_tsub_cancel_of_le (min_le_right _ _)).symm
  have hP₀fin : P₀ Set.univ ≠ ∞ := by
    have : P₀ Set.univ ≤ P₁ Set.univ := by
      rw [e1]; show P₀ Set.univ ≤ P₀ Set.univ + σ₁ Set.univ; exact le_self_add
    exact ne_top_of_le_ne_top (by simp) this
  have hσ₁fin : IsFiniteMeasure σ₁ := ⟨by
    have : σ₁ Set.univ ≤ P₁ Set.univ := by
      rw [e1]; show σ₁ Set.univ ≤ P₀ Set.univ + σ₁ Set.univ; exact le_add_self
    exact lt_of_le_of_lt this (by simp)⟩
  have hσ₂fin : IsFiniteMeasure σ₂ := ⟨by
    have : σ₂ Set.univ ≤ P₂ Set.univ := by
      rw [e2]; show σ₂ Set.univ ≤ P₀ Set.univ + σ₂ Set.univ; exact le_add_self
    exact lt_of_le_of_lt this (by simp)⟩
  have hmass : σ₁ Set.univ = σ₂ Set.univ := by
    have a1 : P₁ Set.univ = P₀ Set.univ + σ₁ Set.univ := by rw [e1]; rfl
    have a2 : P₂ Set.univ = P₀ Set.univ + σ₂ Set.univ := by rw [e2]; rfl
    rw [measure_univ] at a1 a2
    exact (ENNReal.add_right_inj hP₀fin).mp (a1.symm.trans a2)
  have hsndmeas : Measurable (Prod.snd : B × B → B) := measurable_snd
  have hcomm : wassersteinE 2 (P₁.map Prod.snd) (P₂.map Prod.snd) ≤
      (2 * ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂(σ₁.map Prod.snd) +
        2 * ∫⁻ v, ENNReal.ofReal (‖v‖ ^ 2) ∂(σ₂.map Prod.snd)) ^ (1 / (2 : ℝ)) := by
    haveI := hσ₁fin
    haveI := hσ₂fin
    rw [e1, e2, Measure.map_add _ _ hsndmeas, Measure.map_add _ _ hsndmeas]
    refine wassersteinE_two_le_common (P₀.map Prod.snd) (σ₁.map Prod.snd) (σ₂.map Prod.snd)
      (σ₁ Set.univ) ?_ ?_
    · rw [Measure.map_apply hsndmeas MeasurableSet.univ]; rfl
    · rw [Measure.map_apply hsndmeas MeasurableSet.univ, Set.preimage_univ, ← hmass]
  have hmf : Measurable fun z : B × B => ENNReal.ofReal (‖z.2‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_norm.comp measurable_snd).pow_const 2)
  have hmu : Measurable fun u : B => ENNReal.ofReal (‖u‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)
  have hint1 : ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂(σ₁.map Prod.snd) =
      ∫⁻ z, (F₁ z - min (F₁ z) (F₂ z)) * ENNReal.ofReal (‖z.2‖ ^ 2) ∂π₀ := by
    rw [lintegral_map hmu hsndmeas,
      hσ₁, lintegral_withDensity_eq_lintegral_mul _ hr1 hmf]
    rfl
  have hint2 : ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂(σ₂.map Prod.snd) =
      ∫⁻ z, (F₂ z - min (F₁ z) (F₂ z)) * ENNReal.ofReal (‖z.2‖ ^ 2) ∂π₀ := by
    rw [lintegral_map hmu hsndmeas,
      hσ₂, lintegral_withDensity_eq_lintegral_mul _ hr2 hmf]
    rfl
  have hsum : 2 * ∫⁻ u, ENNReal.ofReal (‖u‖ ^ 2) ∂(σ₁.map Prod.snd) +
        2 * ∫⁻ v, ENNReal.ofReal (‖v‖ ^ 2) ∂(σ₂.map Prod.snd) =
      2 * ∫⁻ z, ((F₁ z - min (F₁ z) (F₂ z)) + (F₂ z - min (F₁ z) (F₂ z))) *
          ENNReal.ofReal (‖z.2‖ ^ 2) ∂π₀ := by
    have hm1 : Measurable fun z : B × B =>
        (F₁ z - min (F₁ z) (F₂ z)) * ENNReal.ofReal (‖z.2‖ ^ 2) := hr1.mul hmf
    rw [hint1, hint2, ← mul_add, ← lintegral_add_left hm1]
    congr 1
    refine lintegral_congr fun z => ?_
    simp [add_mul]
  have hcoupA : IsCoupling P₁ (P₁.map Prod.fst) (P₁.map Prod.snd) := ⟨rfl, rfl⟩
  have hcostA := wassersteinE_le_cost (p := 2) hcoupA
  have hcostA' : (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂P₁) =
      ∫⁻ z, F₁ z * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ := by
    have hcostm : Measurable fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) :=
      ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.pow_const _)
    rw [hP₁, lintegral_withDensity_eq_lintegral_mul _ h1 hcostm]
    rfl
  haveI : IsProbabilityMeasure (P₁.map Prod.fst) := inferInstance
  calc _ ≤ wassersteinE 2 (P₁.map Prod.fst) (P₁.map Prod.snd) +
        wassersteinE 2 (P₁.map Prod.snd) (P₂.map Prod.snd) :=
        wassersteinE_triangle 2 (by norm_num) _ _ _
    _ ≤ _ := by
      refine add_le_add ?_ ?_
      · rw [← hcostA']; simpa using hcostA
      · rw [← hsum]; exact hcomm

end HRS.StaticLimitAux
