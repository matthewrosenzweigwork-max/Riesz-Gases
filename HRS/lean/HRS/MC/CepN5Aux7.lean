import HRS.MC.CepN5Aux6

/-!
# Packet N5, helper 7: stopping-time properties of the localisation

`τe`, `rhat`, `τ1` are `𝒢`-stopping times (`𝒢 = n5_shF ℱ t₁`), `A₁ ∈ 𝒢 0`, and `τ2 = τR` is a `𝒢`-stopping time.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section StopTimes

variable {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → ℝ} {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0}
  {δ ε dur : ℝ} {A : Set Ω}

theorem n5_isStoppingTime_tauE (hG : ∀ ω, Continuous fun t => G t ω)
    (hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t)) :
    IsStoppingTime (n5_shF ℱ (t₁ : ℝ)) (n5_tauE G t₁ δ ε) :=
  isStoppingTime_hittingAfter_of_isClosed (n5_shF ℱ (t₁ : ℝ)) (n5_H G t₁)
    (fun s => n5_H_adapted hGad t₁ s) (n5_H_cont hG t₁)
    (isClosed_Iic.union isClosed_Ici) 0

theorem n5_isStoppingTime_rhat (hρ : IsStoppingTime ℱ ρ) :
    IsStoppingTime (n5_shF ℱ (t₁ : ℝ)) (n5_rhat ρ t₁) := by
  intro s
  by_cases hs : 0 ≤ s
  · have hset : {ω | n5_rhat ρ t₁ ω ≤ (s : WithTop ℝ)} = {ω | ρ ω ≤ (((t₁ : ℝ) + s : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [mem_ofPred_eq, n5_rhat]
      cases h : ρ ω with
      | top => simp
      | coe r =>
        simp only [WithTop.map_coe, WithTop.coe_le_coe]
        constructor
        · intro h1; have := (le_max_left (r - t₁) 0).trans h1; linarith
        · intro h1; exact max_le (by linarith) hs
    rw [hset]
    have := hρ ((t₁ : ℝ) + s)
    have hle : ℱ ((t₁ : ℝ) + s) ≤ n5_shF ℱ (t₁ : ℝ) s := by
      rw [n5_shF_apply, max_eq_left hs]
    exact hle _ this
  · have hset : {ω | n5_rhat ρ t₁ ω ≤ (s : WithTop ℝ)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, n5_rhat, mem_empty_iff_false, iff_false]
      cases h : ρ ω with
      | top => simp
      | coe r =>
        simp only [WithTop.map_coe, WithTop.coe_le_coe, not_le]
        exact lt_of_lt_of_le (not_le.1 hs) (le_max_right _ _)
    rw [hset]
    exact @MeasurableSet.empty _ (n5_shF ℱ (t₁ : ℝ) s)

theorem n5_isStoppingTime_tau1 (hG : ∀ ω, Continuous fun t => G t ω)
    (hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t)) (hρ : IsStoppingTime ℱ ρ) :
    IsStoppingTime (n5_shF ℱ (t₁ : ℝ)) (n5_tau1 G ρ t₁ δ ε dur) :=
  ((n5_isStoppingTime_tauE hG hGad).min (n5_isStoppingTime_rhat hρ)).min_const dur

theorem n5_A1_meas (hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t)) (hρ : IsStoppingTime ℱ ρ)
    (hA : MeasurableSet[ℱ (t₁ : ℝ)] A) :
    MeasurableSet[n5_shF ℱ (t₁ : ℝ) 0] (n5_A1 G ρ t₁ δ A) := by
  have h0 : n5_shF ℱ (t₁ : ℝ) 0 = ℱ (t₁ : ℝ) := by rw [n5_shF_apply]; simp
  rw [h0]
  refine (hA.inter ?_).inter ?_
  · have := (hρ.measurableSet_lt (t₁ : ℝ)).compl
    convert this using 1
    ext ω; simp
  · exact (hGad (t₁ : ℝ) t₁.2) measurableSet_Ioi

theorem n5_isStoppingTime_tau2 (hdur : 0 ≤ dur) (hG : ∀ ω, Continuous fun t => G t ω)
    (hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t)) (hρ : IsStoppingTime ℱ ρ)
    (hA : MeasurableSet[ℱ (t₁ : ℝ)] A) :
    IsStoppingTime (n5_shF ℱ (t₁ : ℝ)) (n5_tau2 G ρ t₁ δ ε dur A) := by
  intro s
  by_cases hs : 0 ≤ s
  · have hA1 : MeasurableSet[n5_shF ℱ (t₁ : ℝ) s] (n5_A1 G ρ t₁ δ A) :=
      (n5_shF ℱ (t₁ : ℝ)).mono hs _ (n5_A1_meas hGad hρ hA)
    have h1 := n5_isStoppingTime_tau1 (t₁ := t₁) (δ := δ) (ε := ε) (dur := dur) hG hGad hρ s
    have hset : {ω | n5_tau2 G ρ t₁ δ ε dur A ω ≤ (s : WithTop ℝ)} =
        (n5_A1 G ρ t₁ δ A ∩ {ω | n5_tau1 G ρ t₁ δ ε dur ω ≤ (s : WithTop ℝ)}) ∪ (n5_A1 G ρ t₁ δ A)ᶜ := by
      ext ω
      by_cases hω : ω ∈ n5_A1 G ρ t₁ δ A
      · have := n5_tauR_of_mem (ε := ε) (dur := dur) hω
        simp only [mem_ofPred_eq, n5_tau2, mem_union, mem_inter_iff, hω, true_and, mem_compl_iff,
          not_true_eq_false, or_false]
        rw [this]
      · have := n5_tauR_of_not_mem (ε := ε) (dur := dur) hω
        simp only [mem_ofPred_eq, n5_tau2, mem_union, mem_inter_iff, hω, false_and, mem_compl_iff,
          not_false_eq_true, or_true, iff_true, this]
        exact_mod_cast hs
    rw [hset]
    exact (hA1.inter h1).union hA1.compl
  · have hset : {ω | n5_tau2 G ρ t₁ δ ε dur A ω ≤ (s : WithTop ℝ)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, n5_tau2, mem_empty_iff_false, iff_false, not_le]
      have := n5_tauR_nonneg (G := G) (ρ := ρ) (t₁ := t₁) (δ := δ) (ε := ε) (A := A) hdur ω
      have : (s : ℝ) < n5_tauR G ρ t₁ δ ε dur A ω := lt_of_lt_of_le (not_le.1 hs) this
      exact_mod_cast this
    rw [hset]
    exact @MeasurableSet.empty _ (n5_shF ℱ (t₁ : ℝ) s)

end StopTimes

end HRS.MC.CepN5
