import HRS.Whole.AppendixA
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB1
import HRS.MH.CoercLowerB2

/-!
# CoercLower B3b: Fubini for mixtures (packets P05a, P05b, P05c)

Proofs of the statements in `HRS/MH/CoercLowerSpec.lean`, copied verbatim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower


variable {d N : ℕ}

/-- Auxiliary: three-fold integrability of `(t, y) ↦ H t (x - y) ρ y` on `ν.prod volume`. -/
theorem clb3b_integrable_F {ν : Measure ℝ} [SFinite ν] (H : ℝ → Euc d → ℝ) (K ρ : Euc d → ℝ)
    (hH : Measurable (fun p : ℝ × Euc d => H p.1 p.2)) (hint : ∀ z, Integrable (fun t => H t z) ν)
    (hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ K z) (hρ : HRS.Whole.IsProbDensity ρ) (hK : DomK K ρ)
    (x : Euc d) :
    Integrable (fun p : ℝ × Euc d => H p.1 (x - p.2) * ρ p.2) (ν.prod volume) := by
  have hmeas : Measurable (fun p : ℝ × Euc d => H p.1 (x - p.2) * ρ p.2) :=
    (hH.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))).mul
      (hρ.measurable.comp measurable_snd)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun y => (hint (x - y)).mul_const (ρ y), ?_⟩
  refine (hK.1 x).mono' ?_ ?_
  · exact (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := ν)).measurable.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    have h1 : ∫ t, ‖H t (x - y) * ρ y‖ ∂ν = (∫ t, ‖H t (x - y)‖ ∂ν) * ρ y := by
      rw [← integral_mul_const]
      congr 1
      funext t
      rw [norm_mul, Real.norm_eq_abs (ρ y), abs_of_nonneg (hρ.nonneg y)]
    have h2 : 0 ≤ ∫ t, ‖H t (x - y) * ρ y‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h2, h1]
    exact mul_le_mul_of_nonneg_right (hdom (x - y)) (hρ.nonneg y)

/-- Auxiliary: the norm-integral is dominated by `K * ρ`. -/
theorem clb3b_bound {ν : Measure ℝ} [SFinite ν] (H : ℝ → Euc d → ℝ) (K ρ : Euc d → ℝ)
    (hH : Measurable (fun p : ℝ × Euc d => H p.1 p.2)) (hint : ∀ z, Integrable (fun t => H t z) ν)
    (hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ K z) (hρ : HRS.Whole.IsProbDensity ρ) (hK : DomK K ρ)
    (x : Euc d) :
    ∫ t, ∫ y, ‖H t (x - y) * ρ y‖ ∂volume ∂ν ≤ HRS.Whole.convFun K ρ x := by
  have hF := (clb3b_integrable_F H K ρ hH hint hdom hρ hK x).norm
  have hswap := integral_integral_swap (μ := ν) (ν := (volume : Measure (Euc d)))
    (f := fun t y => ‖H t (x - y) * ρ y‖) hF
  rw [hswap]
  unfold HRS.Whole.convFun
  refine integral_mono (hF.integral_prod_right) (hK.1 x) (fun y => ?_)
  have h1 : ∫ t, ‖H t (x - y) * ρ y‖ ∂ν = (∫ t, ‖H t (x - y)‖ ∂ν) * ρ y := by
    rw [← integral_mul_const]
    congr 1
    funext t
    rw [norm_mul, Real.norm_eq_abs (ρ y), abs_of_nonneg (hρ.nonneg y)]
  show ∫ t, ‖H t (x - y) * ρ y‖ ∂ν ≤ K (x - y) * ρ y
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hdom (x - y)) (hρ.nonneg y)

/-- [P05a] Fubini for the convolution of a mixture `z ↦ ∫ H t z dν(t)`. -/
theorem convFun_mix {ν : Measure ℝ} [SFinite ν] (H : ℝ → Euc d → ℝ) (K ρ : Euc d → ℝ)
    (hH : Measurable (fun p : ℝ × Euc d => H p.1 p.2)) (hint : ∀ z, Integrable (fun t => H t z) ν)
    (hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ K z) (hρ : HRS.Whole.IsProbDensity ρ) (hK : DomK K ρ) (x : Euc d) :
    HRS.Whole.convFun (fun z => ∫ t, H t z ∂ν) ρ x = ∫ t, HRS.Whole.convFun (H t) ρ x ∂ν ∧
      Integrable (fun t => HRS.Whole.convFun (H t) ρ x) ν := by
  have hF := clb3b_integrable_F H K ρ hH hint hdom hρ hK x
  refine ⟨?_, hF.integral_prod_left⟩
  have hswap := integral_integral_swap (μ := ν) (ν := (volume : Measure (Euc d)))
    (f := fun t y => H t (x - y) * ρ y) hF
  unfold HRS.Whole.convFun
  rw [hswap]
  congr 1
  funext y
  rw [integral_mul_const]

/-- [P05b] Fubini for the energy of a mixture. -/
theorem energyDens_mix {ν : Measure ℝ} [SFinite ν] (H : ℝ → Euc d → ℝ) (K ρ : Euc d → ℝ)
    (hH : Measurable (fun p : ℝ × Euc d => H p.1 p.2)) (hint : ∀ z, Integrable (fun t => H t z) ν)
    (hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ K z) (hρ : HRS.Whole.IsProbDensity ρ) (hK : DomK K ρ) :
    energyDens (fun z => ∫ t, H t z ∂ν) ρ = ∫ t, energyDens (H t) ρ ∂ν ∧
      Integrable (fun t => energyDens (H t) ρ) ν := by
  -- measurability of the joint convolution
  have hΦ : Measurable (fun r : (ℝ × Euc d) × Euc d => H r.1.1 (r.1.2 - r.2) * ρ r.2) :=
    (hH.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd))).mul
      (hρ.measurable.comp measurable_snd)
  have hconv : Measurable (fun q : ℝ × Euc d => HRS.Whole.convFun (H q.1) ρ q.2) :=
    (hΦ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  have hG : Measurable (fun p : ℝ × Euc d => ρ p.2 * HRS.Whole.convFun (H p.1) ρ p.2) :=
    (hρ.measurable.comp measurable_snd).mul hconv
  have hGi : Integrable (fun p : ℝ × Euc d => ρ p.2 * HRS.Whole.convFun (H p.1) ρ p.2)
      (ν.prod volume) := by
    rw [integrable_prod_iff' hG.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · exact ((convFun_mix H K ρ hH hint hdom hρ hK x).2).const_mul (ρ x)
    · refine hK.2.mono' ?_ ?_
      · exact (hG.norm.stronglyMeasurable.integral_prod_left' (μ := ν)).measurable.aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun x => ?_
        have hρx := hρ.nonneg x
        have h1 : ∫ t, ‖ρ x * HRS.Whole.convFun (H t) ρ x‖ ∂ν =
            ρ x * ∫ t, ‖HRS.Whole.convFun (H t) ρ x‖ ∂ν := by
          rw [← integral_const_mul]
          congr 1
          funext t
          rw [norm_mul, Real.norm_eq_abs (ρ x), abs_of_nonneg hρx]
        have h2 : 0 ≤ ∫ t, ‖ρ x * HRS.Whole.convFun (H t) ρ x‖ ∂ν :=
          integral_nonneg fun _ => norm_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg h2, h1]
        apply mul_le_mul_of_nonneg_left _ hρx
        have hFn := (clb3b_integrable_F H K ρ hH hint hdom hρ hK x).norm
        calc ∫ t, ‖HRS.Whole.convFun (H t) ρ x‖ ∂ν
            ≤ ∫ t, ∫ y, ‖H t (x - y) * ρ y‖ ∂volume ∂ν := by
              refine integral_mono (convFun_mix H K ρ hH hint hdom hρ hK x).2.norm
                hFn.integral_prod_left (fun t => ?_)
              exact norm_integral_le_integral_norm _
          _ ≤ HRS.Whole.convFun K ρ x := clb3b_bound H K ρ hH hint hdom hρ hK x
  refine ⟨?_, hGi.integral_prod_left⟩
  have hswap := integral_integral_swap (μ := ν) (ν := (volume : Measure (Euc d)))
    (f := fun t x => ρ x * HRS.Whole.convFun (H t) ρ x) hGi
  unfold energyDens
  rw [hswap]
  congr 1
  funext x
  rw [(convFun_mix H K ρ hH hint hdom hρ hK x).1, integral_const_mul]

/-- [P05c] `Qform` commutes with mixtures (assembles P05a, P05b). -/
theorem Qform_mix {ν : Measure ℝ} [SFinite ν] (H : ℝ → Euc d → ℝ) (K ρ : Euc d → ℝ)
    (hH : Measurable (fun p : ℝ × Euc d => H p.1 p.2)) (hint : ∀ z, Integrable (fun t => H t z) ν)
    (hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ K z) (hρ : HRS.Whole.IsProbDensity ρ) (hK : DomK K ρ)
    (X : HRS.Whole.EucConfig d N) :
    Qform (fun z => ∫ t, H t z ∂ν) X ρ = ∫ t, Qform (H t) X ρ ∂ν := by
  have hE := energyDens_mix H K ρ hH hint hdom hρ hK
  have hC := fun x => convFun_mix H K ρ hH hint hdom hρ hK x
  have i1 : ∀ i j, Integrable (fun t => H t (X i - X j)) ν := fun i j => hint _
  have i2 : ∀ i, Integrable (fun t => HRS.Whole.convFun (H t) ρ (X i)) ν := fun i => (hC _).2
  have s1 : Integrable (fun t => (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, H t (X i - X j)) ν :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i1 i j).const_mul _
  have s2 : Integrable (fun t => (2 / (N : ℝ)) * ∑ i, HRS.Whole.convFun (H t) ρ (X i)) ν :=
    (integrable_finsetSum _ fun i _ => i2 i).const_mul _
  have s12 : Integrable (fun t => (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, H t (X i - X j) -
      (2 / (N : ℝ)) * ∑ i, HRS.Whole.convFun (H t) ρ (X i)) ν := s1.sub s2
  unfold Qform
  rw [integral_add s12 hE.2, integral_sub s1 s2, integral_const_mul, integral_const_mul,
    integral_finset_sum _ (fun i _ => integrable_finsetSum _ fun j _ => i1 i j),
    integral_finset_sum _ (fun i _ => i2 i), hE.1]
  congr 3
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => i1 i j)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hC (X i)).1]

end HRS.MH.CoercLower
