import HRS.Uniform.Q45Jor5
import HRS.Uniform.Q45Ten2

/-!
# Q45 (Lemma 3.20): integrability of the propagated bilinear form
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Obs

variable {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma obs_integrable_le {S : EvolData H E} {T K : ℝ} (hT : 0 ≤ T) (hS : S.MaxHyp T K)
    {Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hDb : IsDetCovDensity T Db)
    {t1 t2 : ℝ} (h1 : t1 ∈ Set.Icc (0 : ℝ) T) (h2 : t2 ∈ Set.Icc (0 : ℝ) T) (h12 : t1 ≤ t2)
    (ℓ1 ℓ2 : E →L[ℝ] ℝ) :
    IntegrableOn (fun r => Db r (pullbackVec S t1 r ℓ1) (pullbackVec S t2 r ℓ2)) (Set.Icc 0 t1) := by
  have hev := hS.1
  rcases h1.1.eq_or_lt with h0 | hpos
  · have ht0 : t1 = 0 := h0.symm
    rw [ht0]
    simp
  · have hB10 : 0 ≤ detConst T K * ‖ℓ1‖ := mul_nonneg (detConst_pos T K).le (norm_nonneg _)
    have hB20 : 0 ≤ detConst T K * ‖ℓ2‖ := mul_nonneg (detConst_pos T K).le (norm_nonneg _)
    have hB1 : ∀ s ∈ Set.Icc 0 t1, ‖pullbackVec S t1 s ℓ1‖ ≤ detConst T K * ‖ℓ1‖ := fun s hs =>
      norm_pullback_le hT hS hs.1 hs.2 h1.2 ℓ1
    have hB2 : ∀ s ∈ Set.Icc 0 t1, ‖pullbackVec S t2 s ℓ2‖ ≤ detConst T K * ‖ℓ2‖ := fun s hs =>
      norm_pullback_le hT hS hs.1 (hs.2.trans h12) h2.2 ℓ2
    refine (cells_tendsto hpos
      (Φ := fun σ s => Db σ (pullbackVec S t1 s ℓ1) (pullbackVec S t2 s ℓ2))
      (β := fun σ => traceNormForm (Db σ) * ((detConst T K * ‖ℓ1‖) * (detConst T K * ‖ℓ2‖)))
      (fun s => hDb.meas _ _) ?_ ?_ ?_).2
    · intro σ hσ s hs
      have hσT : σ ∈ Set.Icc 0 T := ⟨hσ.1, hσ.2.trans h1.2⟩
      calc |Db σ (pullbackVec S t1 s ℓ1) (pullbackVec S t2 s ℓ2)|
          ≤ traceNormForm (Db σ) * (‖pullbackVec S t1 s ℓ1‖ * ‖pullbackVec S t2 s ℓ2‖) :=
            psd_apply_le (hDb.traceClass σ hσT) _ _
        _ ≤ traceNormForm (Db σ) * ((detConst T K * ‖ℓ1‖) * (detConst T K * ‖ℓ2‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hB1 s hs) (hB2 s hs) (norm_nonneg _) hB10)
              (traceNormForm_nonneg _)
    · exact (hDb.int.mono_set (Set.Icc_subset_Icc_right h1.2)).mul_const _
    · intro σ hσ
      have hσ1 : σ ∈ Set.Icc 0 t1 := Set.Ioc_subset_Icc_self hσ
      have hσT : σ ∈ Set.Icc 0 T := ⟨hσ.1.le, hσ.2.trans h1.2⟩
      have hid : Tendsto (id : ℝ → ℝ) (𝓝[Set.Icc 0 t1] σ) (𝓝 σ) :=
        (tendsto_id (x := 𝓝[Set.Icc 0 t1] σ)).mono_right nhdsWithin_le_nhds
      have hm1 : ∀ᶠ s in 𝓝[Set.Icc 0 t1] σ, s ∈ Set.Icc 0 t1 := self_mem_nhdsWithin
      have hm2 : ∀ᶠ s in 𝓝[Set.Icc 0 t1] σ, s ∈ Set.Icc 0 t2 := by
        filter_upwards [hm1] with s hs
        exact ⟨hs.1, hs.2.trans h12⟩
      refine psd_tendsto_weak (hDb.traceClass σ hσT) (fun s => pullbackVec S t1 s ℓ1)
        (fun s => pullbackVec S t2 s ℓ2) _ _ (B := max (detConst T K * ‖ℓ1‖) (detConst T K * ‖ℓ2‖))
        (le_max_of_le_left hB10) ?_ ?_ ?_ ?_
      · filter_upwards [hm1] with s hs using (hB1 s hs).trans (le_max_left _ _)
      · filter_upwards [hm1] with s hs using (hB2 s hs).trans (le_max_right _ _)
      · intro x
        exact pullback_weak_tendsto hev h1 ℓ1 id hσ1 hm1 hid x
      · intro x
        exact pullback_weak_tendsto hev h2 ℓ2 id ⟨hσ.1.le, hσ.2.trans h12⟩ hm2 hid x

lemma obs_integrable {S : EvolData H E} {T K : ℝ} (hT : 0 ≤ T) (hS : S.MaxHyp T K)
    {Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hDb : IsDetCovDensity T Db)
    {t1 t2 : ℝ} (h1 : t1 ∈ Set.Icc (0 : ℝ) T) (h2 : t2 ∈ Set.Icc (0 : ℝ) T)
    (ℓ1 ℓ2 : E →L[ℝ] ℝ) :
    IntegrableOn (fun r => Db r (pullbackVec S t1 r ℓ1) (pullbackVec S t2 r ℓ2)) (Set.Icc 0 (min t1 t2)) := by
  rcases le_total t1 t2 with h12 | h21
  · rw [min_eq_left h12]; exact obs_integrable_le hT hS hDb h1 h2 h12 ℓ1 ℓ2
  · rw [min_eq_right h21]
    have := obs_integrable_le hT hS hDb h2 h1 h21 ℓ2 ℓ1
    refine this.congr_fun (fun r hr => ?_) measurableSet_Icc
    have hrT : r ∈ Set.Icc 0 T := ⟨hr.1, hr.2.trans h2.2⟩
    exact (hDb.traceClass r hrT).symm _ _

end Obs

end HRS.Uniform.Q45
