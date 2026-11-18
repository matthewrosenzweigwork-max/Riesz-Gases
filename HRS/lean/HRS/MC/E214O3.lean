import HRS.MC.E214PD
import HRS.MC.E214K6
import HRS.MC.E214L3
import HRS.MC.E214M2
import HRS.MC.E213U11i
import HRS.MC.E214O2

/-!
# Packet E214O, part 3: `Dwin_relax` (the deterministic estimates)

`o_block_weighted`: the weighted integral of a nonnegative function is bounded by its unit-block integrals.
`o_drift_det`: the pathwise bound for `D^R(b₁) - D^{Rs}(b₂)` (linearity + `winDrift_L1` + `winDrift_compare`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214O

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

theorem o_cont_weight (c a : ℝ) : Continuous fun v : ℝ => Real.exp (-c * (a - v)) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))

theorem o_block_weighted {c κ a T : ℝ} (hc : 0 ≤ c) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hT : 0 ≤ T) {φ : ℝ → ℝ}
    (hφ0 : ∀ v, 0 ≤ φ v) {N : ℕ} (hN : a + T ≤ N) (hφ : IntegrableOn φ (Set.Icc 0 (N : ℝ))) {Y : ℕ → ℝ}
    (hY : ∀ k < N, ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x ≤ Y k) :
    ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * φ v ≤
      Real.exp (c * T) * Real.exp (-(min c κ) * a) * ∑ k ∈ Finset.range N, Y k := by
  have hsub : Set.Ioc (0 : ℝ) (a + T) ⊆ Set.Icc 0 (N : ℝ) := fun v hv => ⟨hv.1.le, hv.2.trans hN⟩
  set K := Real.exp (c * T) * Real.exp (-(min c κ) * a) with hK
  have hK0 : 0 ≤ K := by positivity
  have hwc : Continuous fun v : ℝ => Real.exp (-c * (a - v)) * Real.exp (-κ * v) :=
    (o_cont_weight c a).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hint1 : IntegrableOn (fun v => Real.exp (-c * (a - v)) * Real.exp (-κ * v) * φ v) (Set.Ioc 0 (a + T)) :=
    (IntegrableOn.continuousOn_mul hwc.continuousOn hφ isCompact_Icc).mono_set hsub
  have hint2 : IntegrableOn (fun v => K * φ v) (Set.Ioc 0 (a + T)) := (hφ.mono_set hsub).const_mul K
  have s1 : ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * φ v ≤
      ∫ v in Set.Ioc 0 (a + T), K * φ v := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioc fun v hv => ?_
    exact mul_le_mul_of_nonneg_right (o_exp_weight_le hc hκ hT ha hv.1.le hv.2) (hφ0 v)
  have s2 := HRS.MC.E213U11.u11_weighted_block φ hφ0 N hφ 0 0 (a + T) le_rfl hN
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at s2
  have s3 : ∑ k ∈ Finset.range N, ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x ≤ ∑ k ∈ Finset.range N, Y k :=
    Finset.sum_le_sum fun k hk => hY k (Finset.mem_range.1 hk)
  refine s1.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (s2.trans s3) hK0

/-- Pathwise bound for the drift difference (linearity, `winDrift_L1`, `winDrift_compare`, block decomposition). -/
theorem o_drift_det {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)
    (T : ℝ) (hT : 0 < T) {C₁ c₁ C₂ c₂ κ : ℝ} (hC₂ : 0 ≤ C₂) (hc₂ : 0 ≤ c₂) (hκ : 0 ≤ κ)
    (hL1 : ∀ (a : ℝ) (ha : 0 ≤ a) (bq : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 bq) →
      IntegrableOn (fun v => Real.exp (-c₁ * (a - v)) * ‖bq v‖) (Set.Ioc 0 (a + T)) →
      ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T)‖ ≤
        C₁ * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c₁ * (a - v)) * ‖bq v‖)
    (hcmp : ∀ (a : ℝ) (ha : 0 ≤ a) (bq : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 bq) →
      IntegrableOn (fun v => Real.exp (-c₂ * (a - v)) * ‖bq v‖) (Set.Ioc 0 (a + T)) →
      ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T) -
          winDrift (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T)‖ ≤
        C₂ * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c₂ * (a - v)) * Real.exp (-κ * v) * ‖bq v‖)
    (a : ℝ) (ha : 0 ≤ a) (b1 b2 : ℝ → NegSobolev d (rLvl d))
    (h1 : Measurable (nearCoef 0 b1)) (h2 : Measurable (nearCoef 0 b2)) (N : ℕ) (hN : a + T ≤ N)
    (i1 : IntegrableOn (fun v => ‖b1 v‖) (Set.Icc 0 (N : ℝ)))
    (i2 : IntegrableOn (fun v => ‖b2 v‖) (Set.Icc 0 (N : ℝ)))
    (blk : ∀ k : ℕ, MemLp (fun t => b2 ((k : ℝ) + t)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b1 v)) 0 (a + T) -
        winDrift (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (b2 v)) 0 (a + T)‖ ≤
      C₁ * (∫ v in Set.Ioc 0 (a + T), Real.exp (-c₁ * (a - v)) * ‖b1 v - b2 v‖) +
        C₂ * (Real.exp (c₂ * T) * Real.exp (-(min c₂ κ) * a)) *
          ∑ k ∈ Finset.range N, ‖toL2 (rLvl d) 1 (fun t => b2 ((k : ℝ) + t))‖ := by
  have hH : 0 ≤ a + T := by linarith
  have hsub : Set.Ioc (0 : ℝ) (a + T) ⊆ Set.Icc 0 (N : ℝ) := fun v hv => ⟨hv.1.le, hv.2.trans hN⟩
  set δ : ℝ → NegSobolev d (rLvl d) := fun v => b1 v - b2 v with hδ
  have hδm : Measurable (nearCoef 0 δ) := by
    have : nearCoef 0 δ = fun v => nearCoef 0 b1 v - nearCoef 0 b2 v := by
      funext v; unfold nearCoef; split_ifs <;> simp [hδ]
    rw [this]; exact h1.sub h2
  have e1 := HRS.MC.E213U1.u1_aesm_of_nearCoef h1 (measurableSet_Icc (a := (0 : ℝ)) (b := N))
    (fun v hv => Set.mem_Ici.2 hv.1)
  have e2 := HRS.MC.E213U1.u1_aesm_of_nearCoef h2 (measurableSet_Icc (a := (0 : ℝ)) (b := N))
    (fun v hv => Set.mem_Ici.2 hv.1)
  have iδ : IntegrableOn (fun v => ‖δ v‖) (Set.Icc 0 (N : ℝ)) := by
    refine (i1.add i2).mono' (e1.sub e2).norm (Eventually.of_forall fun v => ?_)
    simp only [norm_norm]
    exact norm_sub_le _ _
  have wint : ∀ (c : ℝ) (φ : ℝ → ℝ), IntegrableOn φ (Set.Icc 0 (N : ℝ)) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * φ v) (Set.Ioc 0 (a + T)) := fun c φ hφ =>
    (IntegrableOn.continuousOn_mul (o_cont_weight c a).continuousOn hφ isCompact_Icc).mono_set hsub
  have hsubI : Set.Icc (0 : ℝ) (a + T) ⊆ Set.Icc 0 (N : ℝ) := Set.Icc_subset_Icc le_rfl hN
  have hadd := HRS.MC.E213U1.winDrift_add_proof hE T hT a ha δ b2 hδm h2 (iδ.mono_set hsubI) (i2.mono_set hsubI)
    0 (a + T) le_rfl hH le_rfl
  have hb1 : (fun v => NegSobolev.embed m (δ v + b2 v)) = fun v => NegSobolev.embed m (b1 v) := by
    funext v; simp [hδ]
  rw [hb1] at hadd
  have key : winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b1 v)) 0 (a + T) -
        winDrift (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (b2 v)) 0 (a + T) =
      winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (δ v)) 0 (a + T) +
        (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (b2 v)) 0 (a + T) -
          winDrift (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (b2 v)) 0 (a + T)) := by
    rw [hadd]; abel
  rw [key]
  refine (norm_add_le _ _).trans (add_le_add (hL1 a ha δ hδm (wint c₁ _ iδ)) ?_)
  refine (hcmp a ha b2 h2 (wint c₂ _ i2)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC₂
  exact o_block_weighted hc₂ hκ ha hT.le (fun v => norm_nonneg _) hN i2
    (fun k _ => HRS.MC.E213U11.u11_block_integral_le b2 k (blk k))

end HRS.MC.E214O

end
