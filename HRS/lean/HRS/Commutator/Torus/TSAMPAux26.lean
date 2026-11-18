import HRS.Commutator.Torus.TSAMPAux25
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# T-SAMP helpers, part 26: continuity of `L^q ⋆ L^p` on the torus
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform Convolution

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_conv_integrable_Lq {p q : ℝ} (hpq : p.HolderConjugate q) {K f : Torus d → ℝ}
    (hK : MemLp K (ENNReal.ofReal q) volume) (hf : MemLp f (ENNReal.ofReal p) volume) (x : Torus d) :
    Integrable (fun y => K (x - y) * f y) := by
  haveI := hpq.ennrealOfReal
  have hKx : MemLp (fun y => K (x - y)) (ENNReal.ofReal q) volume :=
    hK.comp_measurePreserving ((volume : Measure (Torus d)).measurePreserving_sub_left x)
  have hprod := MemLp.integrable_mul (𝕜 := ℝ) (p := ENNReal.ofReal q) (q := ENNReal.ofReal p)
    (f := fun y => ‖K (x - y)‖) (g := fun y => ‖f y‖) hKx.norm hf.norm
  refine hprod.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact hKx.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · simp [norm_mul]

theorem tsamp_continuous_conv {p q : ℝ} (hpq : p.HolderConjugate q) {K f : Torus d → ℝ}
    (hK : MemLp K (ENNReal.ofReal q) volume) (hf : MemLp f (ENNReal.ofReal p) volume) :
    Continuous (fun x => ∫ y, K (x - y) * f y) := by
  haveI := hpq.ennrealOfReal
  set Q : ℝ≥0∞ := ENNReal.ofReal q with hQ
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hQt : Q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP1 : 1 ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hpq.lt.le
  have hq0 : 0 < q := hpq.symm.pos
  have happrox : ∀ n : ℕ, ∃ g : BoundedContinuousFunction (Torus d) ℝ, eLpNorm (K - (g : Torus d → ℝ)) Q volume ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧ MemLp g Q volume := fun n =>
    hK.exists_boundedContinuous_eLpNorm_sub_le hQt
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
  choose g hgn hgm using happrox
  have hcont : ∀ n, Continuous (fun x => ∫ y, g n (x - y) * f y) := by
    intro n
    have hbdd : BddAbove (Set.range fun x : Torus d => ‖(g n : Torus d → ℝ) x‖) :=
      ⟨‖g n‖, by rintro _ ⟨x, rfl⟩; exact (g n).norm_coe_le_norm x⟩
    have := BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℝ ℝ) hbdd
      (hf.integrable hP1) (g n).continuous (μ := (volume : Measure (Torus d)))
    convert this using 1
    ext x
    simp only [convolution_def, ContinuousLinearMap.mul_apply']
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  have hwt : eLpNorm f P volume ≠ ⊤ := hf.eLpNorm_lt_top.ne
  have hunif : TendstoUniformly (fun n x => ∫ y, g n (x - y) * f y)
      (fun x => ∫ y, K (x - y) * f y) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    set C : ℝ := (eLpNorm f P volume).toReal with hC
    have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
    obtain ⟨N, hN⟩ := exists_nat_gt ((C + 1) / ε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have hsub : (∫ y, K (x - y) * f y) - ∫ y, g n (x - y) * f y =
        textConv (K - (g n : Torus d → ℝ)) f x := by
      unfold textConv
      rw [← integral_sub (tsamp_conv_integrable_Lq hpq hK hf x)
        (tsamp_conv_integrable_Lq hpq (hgm n) hf x)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [sub_mul]
    have h1 := text_conv_enorm_le (p := P) (p' := Q) (hK.sub (hgm n)) hf x
    have h2 : ‖textConv (K - (g n : Torus d → ℝ)) f x‖ ≤ (1 / ((n : ℝ) + 1)) * C := by
      have h3 : ‖textConv (K - (g n : Torus d → ℝ)) f x‖ₑ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) * eLpNorm f P volume :=
        h1.trans (mul_le_mul_left (hgn n) _)
      have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwt) h3
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), toReal_enorm] at h4
      exact h4
    rw [dist_eq_norm, hsub]
    refine lt_of_le_of_lt h2 ?_
    have hn' : (C + 1) / ε < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
    rw [div_lt_iff₀ hε] at hn'
    rw [one_div, inv_mul_eq_div, div_lt_iff₀ (by positivity)]
    nlinarith
  exact hunif.continuous (Eventually.of_forall hcont).frequently

end HRS.Commutator.TorusNote
