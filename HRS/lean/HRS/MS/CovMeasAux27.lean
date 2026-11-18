import HRS.MS.CovMeasAux26
import HRS.MS.GenPathAux10

/-!
# S10.1 (worker S101B), part 27: the linear map `Ψ = s101Bri ∘ tensorMap 𝒯`, trace densities closed under combinations
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9

variable {d : ℕ} {m T : ℝ}

/-- `Ψ τ = s101Bri (tensorMap 𝒯 τ)`. -/
def s101Psi (hT : 0 ≤ T) (τ : ProjTensor2 (PathSp T (KSpace d m T))) : TensorDual (OscPath d m T) 2 :=
  s101Bri (tensorMap (s56_reconCLM hT) τ)

lemma s101Psi_add (hT : 0 ≤ T) (τ τ' : ProjTensor2 (PathSp T (KSpace d m T))) :
    s101Psi hT (τ + τ') = s101Psi hT τ + s101Psi hT τ' := by
  unfold s101Psi; rw [map_add, s101Bri_add]

lemma s101Psi_smul (hT : 0 ≤ T) (a : ℝ) (τ : ProjTensor2 (PathSp T (KSpace d m T))) :
    s101Psi hT (a • τ) = a • s101Psi hT τ := by
  unfold s101Psi; rw [map_smul, s101Bri_smul]

lemma s101Psi_zero (hT : 0 ≤ T) : s101Psi hT (0 : ProjTensor2 (PathSp T (KSpace d m T))) = 0 := by
  have := s101Psi_smul (d := d) (m := m) hT 0 0
  simpa using this

lemma s101Psi_sub (hT : 0 ≤ T) (τ τ' : ProjTensor2 (PathSp T (KSpace d m T))) :
    s101Psi hT (τ - τ') = s101Psi hT τ - s101Psi hT τ' := by
  unfold s101Psi; rw [map_sub, s101Bri_sub]

lemma norm_s101Psi_le (hT : 0 ≤ T) (τ : ProjTensor2 (PathSp T (KSpace d m T))) :
    ‖s101Psi hT τ‖ ≤ ‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ^ 2 * ‖τ‖ :=
  (norm_s101Bri_le _).trans (norm_tensorMap_le _ _)

lemma s101Psi_mem (hT : 0 ≤ T) (τ : ProjTensor2 (PathSp T (KSpace d m T))) :
    s101Psi hT τ ∈ projTensor (OscPath d m T) 2 := s101Bri_mem _

lemma s101_bdd_smul (c : ℝ) {A : S101Bil d m T}
    (hA : BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) => ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)|)) :
    BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) => ∑ i, |(c • A) (p.1.2.1 i) (p.1.2.2 i)|) := by
  obtain ⟨b, hb⟩ := hA
  refine ⟨|c| * b, ?_⟩
  rintro _ ⟨p, rfl⟩
  have h : ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)| ≤ b := hb ⟨p, rfl⟩
  calc ∑ i, |(c • A) (p.1.2.1 i) (p.1.2.2 i)| = |c| * ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)| := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        simp [abs_mul]
    _ ≤ |c| * b := mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem s101_isTraceDensity_comb {D₁ D₂ : ℝ → S101Bil d m T} (h₁ : IsTraceDensityL1 T D₁)
    (h₂ : IsTraceDensityL1 T D₂) (a b : ℝ) : IsTraceDensityL1 T (fun r => a • D₁ r + b • D₂ r) := by
  obtain ⟨s1, b1, m1, i1⟩ := h₁
  obtain ⟨s2, b2, m2, i2⟩ := h₂
  have hent : ∀ r x y, (a • D₁ r + b • D₂ r) x y = a * D₁ r x y + b * D₂ r x y := by
    intro r x y; simp
  have hmeasE : ∀ x y, Measurable fun r => (a • D₁ r + b • D₂ r) x y := by
    intro x y
    have : (fun r => (a • D₁ r + b • D₂ r) x y) = fun r => a * D₁ r x y + b * D₂ r x y :=
      funext fun r => hent r x y
    rw [this]; exact ((m1 x y).const_mul a).add ((m2 x y).const_mul b)
  refine ⟨fun r x y => ?_, fun r hr => ?_, hmeasE, ?_⟩
  · rw [hent, hent, s1, s2]
  · obtain ⟨c1, hc1⟩ := s101_bdd_smul a (b1 r hr)
    obtain ⟨c2, hc2⟩ := s101_bdd_smul b (b2 r hr)
    refine ⟨c1 + c2, ?_⟩
    rintro _ ⟨p, rfl⟩
    have e1 : ∑ i, |(a • D₁ r) (p.1.2.1 i) (p.1.2.2 i)| ≤ c1 := hc1 ⟨p, rfl⟩
    have e2 : ∑ i, |(b • D₂ r) (p.1.2.1 i) (p.1.2.2 i)| ≤ c2 := hc2 ⟨p, rfl⟩
    show ∑ i, |(a • D₁ r + b • D₂ r) (p.1.2.1 i) (p.1.2.2 i)| ≤ c1 + c2
    calc ∑ i, |(a • D₁ r + b • D₂ r) (p.1.2.1 i) (p.1.2.2 i)|
        ≤ ∑ i, (|(a • D₁ r) (p.1.2.1 i) (p.1.2.2 i)| + |(b • D₂ r) (p.1.2.1 i) (p.1.2.2 i)|) :=
          Finset.sum_le_sum fun i _ => abs_add_le _ _
      _ ≤ c1 + c2 := by rw [Finset.sum_add_distrib]; exact add_le_add e1 e2
  · have hm : Measurable fun r => HRS.traceNormForm (a • D₁ r + b • D₂ r) :=
      HRS.measurable_traceNormForm _ hmeasE
    have hint : Integrable (fun r => |a| * HRS.traceNormForm (D₁ r) + |b| * HRS.traceNormForm (D₂ r))
        (volume.restrict (Icc (0 : ℝ) T)) := (i1.const_mul |a|).add (i2.const_mul |b|)
    refine hint.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (HRS.traceNormForm_nonneg _)]
    calc HRS.traceNormForm (a • D₁ r + b • D₂ r)
        ≤ HRS.traceNormForm (a • D₁ r) + HRS.traceNormForm (b • D₂ r) :=
          s101_tn_add_le (s101_bdd_smul a (b1 r hr)) (s101_bdd_smul b (b2 r hr))
      _ ≤ |a| * HRS.traceNormForm (D₁ r) + |b| * HRS.traceNormForm (D₂ r) :=
          add_le_add (s101_tn_smul_le a (b1 r hr)) (s101_tn_smul_le b (b2 r hr))

end HRS.MS.CovMeas
