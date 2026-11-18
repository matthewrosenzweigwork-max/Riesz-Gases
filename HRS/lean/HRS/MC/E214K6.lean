import HRS.MC.E214K5
import HRS.MC.E213U1b
import HRS.MC.E214K3
import HRS.MC.E214PD

/-!
# Packet E214K, part 6: `winDrift_compare_proof` (P2c, drift difference between the regimes for a fixed coefficient)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214K

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E213U1 HRS.MC.E214Plan

variable {d : ℕ}

/-- `pathOf` of a difference of two continuous paths. -/
theorem pathOf_sub' {m T : ℝ} (g1 g2 : ℝ → NegSobolev d m)
    (h1 : Continuous fun t : Set.Icc (0 : ℝ) T => g1 t) (h2 : Continuous fun t : Set.Icc (0 : ℝ) T => g2 t) :
    Sec7.pathOf m T g1 - Sec7.pathOf m T g2 = Sec7.pathOf m T (fun t => g1 t - g2 t) := by
  have h12 : Continuous fun t : Set.Icc (0 : ℝ) T => (g1 t - g2 t) := h1.sub h2
  refine e213o_ext (fun t => ?_)
  rw [e213o_pathOf_at' _ h12 t]
  show (Sec7.pathOf m T g1).at' t - (Sec7.pathOf m T g2).at' t = _
  rw [e213o_pathOf_at' _ h1 t, e213o_pathOf_at' _ h2 t]

/-- Integrability of the drift integrand at a fixed time `t ∈ [0,a+T]`. -/
theorem drift_integrableOn {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (hT : 0 < T)
    (ha : 0 ≤ a) (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T))) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (a + T)) :
    IntegrableOn (fun v => Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t v (NegSobolev.embed m (bq v)))
      (Set.Ioc 0 (min (a + T) t)) := by
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := u1_vev hE
  have hsp' := hsp
  obtain ⟨-, heq, -⟩ := hsp
  obtain ⟨-, hint, -⟩ := u1_Fint hE hC hc hsp' T a hT ha bq hbm hbi 0 (a + T) le_rfl le_rfl t ht
  have h1 := (integrable_indicator_iff (measurableSet_Iic (a := t))).1 hint
  have hset : Set.Ioc 0 (min (a + T) t) = Set.Iic t ∩ Set.Ioc 0 (a + T) := by
    ext v; simp only [Set.mem_Ioc, le_min_iff, Set.mem_inter_iff, Set.mem_Iic]; tauto
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iic] at h1
  rw [IntegrableOn, hset]
  refine h1.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Iic.inter measurableSet_Ioc)]
  refine Filter.Eventually.of_forall fun v hv => ?_
  have hv0 : 0 ≤ v := hv.2.1.le
  have hvt : v ≤ t := hv.1
  simp only [u1_cl_eq hv0 hvt]
  rw [heq v t hv0 hvt]
  rfl

/-- Pointwise (in the window time) bound for the difference of the two drift integrals. -/
theorem drift_diff_le {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)
    {C c κ : ℝ}
    (hcmp : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ F : NegSobolev d (rLvl d),
      ‖Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u (NegSobolev.embed m F) -
          Vprop (regime S β₀ hE).D (fun _ => (regime S β₀ hE).ρβ) m t u (NegSobolev.embed m F)‖ ≤
        C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) * ‖F‖)
    (hC : 0 < C) (hc : 0 < c) (hκ : 0 < κ) (T a : ℝ) (hT : 0 < T) (ha : 0 ≤ a)
    (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T)))
    (hw : IntegrableOn (fun v => Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖) (Set.Ioc 0 (a + T)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (a + T)) (hat : a ≤ t) :
    ‖(∫ v in Set.Ioc 0 (min (a + T) t),
        Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t v (NegSobolev.embed m (bq v))) -
      (∫ v in Set.Ioc 0 (min (a + T) t),
        Vprop (regime sd.Ss S.β sd.hEs).D (regime sd.Ss S.β sd.hEs).ρ m t v (NegSobolev.embed m (bq v)))‖ ≤
      C * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖ := by
  have hmin : min (a + T) t = t := min_eq_right ht.2
  have i1 := drift_integrableOn hE T a hT ha bq hbm hbi t ht
  have i2 := drift_integrableOn sd.hEs T a hT ha bq hbm hbi t ht
  rw [hmin] at i1 i2
  rw [sd.hD, sd.hρ] at i2
  rw [hmin, sd.hD, sd.hρ, ← integral_sub i1 i2]
  have hg0 : ∀ v, 0 ≤ C * (Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖) := fun v => by positivity
  have hwC : IntegrableOn (fun v => C * (Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖))
      (Set.Ioc 0 (a + T)) := hw.const_mul C
  have hwt : IntegrableOn (fun v => C * (Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖))
      (Set.Ioc 0 t) := hwC.mono_set (Set.Ioc_subset_Ioc_right ht.2)
  have hsub : Set.Ioc 0 t ⊆ Set.Ioc 0 (a + T) := Set.Ioc_subset_Ioc_right ht.2
  calc _ ≤ ∫ v in Set.Ioc 0 t, C * (Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖) := by
        refine norm_integral_le_of_norm_le hwt ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
        have hv0 : 0 ≤ v := hv.1.le
        have hvt : v ≤ t := hv.2
        beta_reduce
        refine (hcmp v t hv0 hvt (bq v)).trans ?_
        have he : Real.exp (-c * (t - v)) ≤ Real.exp (-c * (a - v)) :=
          Real.exp_le_exp.2 (by nlinarith)
        calc C * Real.exp (-c * (t - v)) * Real.exp (-κ * v) * ‖bq v‖
            ≤ C * Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖ := by gcongr
          _ = _ := by ring
    _ ≤ ∫ v in Set.Ioc 0 (a + T), C * (Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖) :=
        setIntegral_mono_set hwC (Filter.Eventually.of_forall hg0) (Filter.Eventually.of_forall hsub)
    _ = _ := integral_const_mul _ _

/-- **P2c, drift difference between the regimes for a fixed coefficient.** -/
theorem winDrift_compare_proof {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}
    (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (bq : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 bq) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖bq v‖) (Set.Ioc 0 (a + T)) →
      ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T) -
          winDrift (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T)‖ ≤
        C * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖bq v‖ := by
  obtain ⟨C0, c0, κ0, hC0, hc0, hκ0, hcmp⟩ := vprop_compare_Er_proof (S := S) (β₀ := β₀) (m := m) (hE := hE)
  refine ⟨C0, c0, κ0, hC0, hc0, hκ0, fun a ha bq hbm hbw => ?_⟩
  have hH : 0 ≤ a + T := by linarith
  have haesm : AEStronglyMeasurable bq (volume.restrict (Set.Ioc 0 (a + T))) :=
    u1_aesm_of_nearCoef hbm measurableSet_Ioc (fun v hv => hv.1.le)
  have hbiIoc : IntegrableOn (fun v => ‖bq v‖) (Set.Ioc 0 (a + T)) := by
    refine Integrable.mono' (hbw.const_mul (Real.exp (c0 * a))) haesm.norm ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun v hv => ?_
    have hv0 : 0 ≤ v := hv.1.le
    have h1 : 1 ≤ Real.exp (c0 * a) * Real.exp (-c0 * (a - v)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖bq v‖ = 1 * ‖bq v‖ := (one_mul _).symm
      _ ≤ (Real.exp (c0 * a) * Real.exp (-c0 * (a - v))) * ‖bq v‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := mul_assoc _ _ _
  have hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T)) :=
    (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).2 hbiIoc
  have hw : IntegrableOn (fun v => Real.exp (-c0 * (a - v)) * Real.exp (-κ0 * v) * ‖bq v‖)
      (Set.Ioc 0 (a + T)) := by
    refine Integrable.mono' hbw ?_ ?_
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) haesm.norm
      · exact (by fun_prop : Continuous fun v : ℝ => Real.exp (-c0 * (a - v))).aestronglyMeasurable
      · exact (by fun_prop : Continuous fun v : ℝ => Real.exp (-κ0 * v)).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun v hv => ?_
      have hv0 : 0 ≤ v := hv.1.le
      have h1 : Real.exp (-κ0 * v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (Real.exp_pos _).le h1) (norm_nonneg _)
  have hc1 := winDrift_cont_proof hE T hT a ha bq hbm hbi 0 (a + T) le_rfl hH le_rfl
  have hc2 := winDrift_cont_proof sd.hEs T hT a ha bq hbm hbi 0 (a + T) le_rfl hH le_rfl
  have hdiff : winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T) -
      winDrift (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T) =
      winRestr a ha (Sec7.pathOf m (a + T) (fun t =>
        (∫ v in Set.Ioc 0 (min (a + T) t),
          Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t v (NegSobolev.embed m (bq v))) -
        (∫ v in Set.Ioc 0 (min (a + T) t),
          Vprop (regime sd.Ss S.β sd.hEs).D (regime sd.Ss S.β sd.hEs).ρ m t v (NegSobolev.embed m (bq v))))) := by
    show winRestr a ha (Sec7.pathOf m (a + T) _) - winRestr a ha (Sec7.pathOf m (a + T) _) = _
    rw [← map_sub, pathOf_sub' _ _ hc1 hc2]
  rw [hdiff]
  refine u1_winRestr_pathOf_norm_le a ha _ (mul_nonneg hC0.le (setIntegral_nonneg measurableSet_Ioc
    fun v _ => by positivity)) (fun s hs => ?_)
  exact drift_diff_le sd hcmp hC0 hc0 hκ0 T a hT ha bq hbm hbi hw (a + s)
    ⟨by linarith [hs.1], by linarith [hs.2]⟩ (by linarith [hs.1])

end HRS.MC.E214K

end
