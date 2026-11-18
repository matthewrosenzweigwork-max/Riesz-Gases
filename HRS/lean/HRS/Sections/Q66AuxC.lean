import HRS.Sections.Q66AuxB
import HRS.Dynamics.InitialData
import HRS.PDE.MeanFieldSchauder
import HRS.PDE.MeanFieldAux

/-!
# Packet Q66: regularity of the one-body response, part C (continuity of `g * u`, `g, u ∈ L²`)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate BoundedContinuousFunction

noncomputable section

namespace HRS.Q66

open HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ}

/-- Cauchy--Schwarz for the torus convolution: `|a * u (x)| ≤ ‖a‖₂ ‖u‖₂` for every `x`. -/
theorem q66_conv_bound {a u : Torus d → ℝ} (ha : MemLp a 2 (volume : Measure (Torus d)))
    (hu : MemLp u 2 (volume : Measure (Torus d))) (x : Torus d) :
    |convFun a u x| ≤ (∫ y, a y ^ 2) ^ (1 / 2 : ℝ) * (∫ y, u y ^ 2) ^ (1 / 2 : ℝ) := by
  have hmp : MeasurePreserving (fun y : Torus d => x - y) (volume : Measure (Torus d)) volume :=
    Measure.measurePreserving_sub_left volume x
  have ha' : MemLp (fun y => a (x - y)) 2 (volume : Measure (Torus d)) := ha.comp_measurePreserving hmp
  have h1 : |convFun a u x| ≤ ∫ y, |a (x - y)| * |u y| := by
    unfold convFun
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [abs_mul]
  refine h1.trans ?_
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have := integral_mul_le_Lp_mul_Lq_of_nonneg hp (μ := (volume : Measure (Torus d)))
    (f := fun y => |a (x - y)|) (g := fun y => |u y|)
    (Eventually.of_forall fun y => abs_nonneg _) (Eventually.of_forall fun y => abs_nonneg _)
    (by rw [ENNReal.ofReal_ofNat]; simpa only [Real.norm_eq_abs] using ha'.norm)
    (by rw [ENNReal.ofReal_ofNat]; simpa only [Real.norm_eq_abs] using hu.norm)
  refine this.trans (le_of_eq ?_)
  have e1 : ∫ y, |a (x - y)| ^ (2 : ℝ) = ∫ y, a y ^ 2 := by
    have : ∀ y, |a (x - y)| ^ (2 : ℝ) = (fun z => a z ^ 2) (x - y) := fun y => by
      rw [Real.rpow_two, sq_abs]
    simp_rw [this]
    exact integral_sub_left_eq_self (fun z => a z ^ 2) volume x
  have e2 : ∫ y, |u y| ^ (2 : ℝ) = ∫ y, u y ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Real.rpow_two, sq_abs]
  rw [e1, e2]

theorem q66_conv_sub {g g' u : Torus d → ℝ} (hg : MemLp g 2 (volume : Measure (Torus d)))
    (hg' : MemLp g' 2 (volume : Measure (Torus d))) (hu : MemLp u 2 (volume : Measure (Torus d)))
    (x : Torus d) :
    convFun (fun y => g y - g' y) u x = convFun g u x - convFun g' u x := by
  have hmp : MeasurePreserving (fun y : Torus d => x - y) (volume : Measure (Torus d)) volume :=
    Measure.measurePreserving_sub_left volume x
  have h1 : Integrable (fun y => g (x - y) * u y) (volume : Measure (Torus d)) :=
    (hg.comp_measurePreserving hmp).integrable_mul hu
  have h2 : Integrable (fun y => g' (x - y) * u y) (volume : Measure (Torus d)) :=
    (hg'.comp_measurePreserving hmp).integrable_mul hu
  unfold convFun
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sub_mul]

theorem q66_continuous_conv {g u : Torus d → ℝ} (hg : MemLp g 2 (volume : Measure (Torus d)))
    (hu : MemLp u 2 (volume : Measure (Torus d))) : Continuous (convFun g u) := by
  have hg' : MemLp g (ENNReal.ofReal 2) (volume : Measure (Torus d)) := by
    rwa [ENNReal.ofReal_ofNat]
  have happ : ∀ n : ℕ, ∃ gn : Torus d →ᵇ ℝ,
      (∫ x, ‖g x - gn x‖ ^ (2 : ℝ)) ≤ 1 / ((n : ℝ) + 1) ∧
        MemLp gn (ENNReal.ofReal 2) (volume : Measure (Torus d)) := fun n =>
    hg'.exists_boundedContinuous_integral_rpow_sub_le (by norm_num) (by positivity)
  choose gn hgn using happ
  have hgn2 : ∀ n, MemLp (gn n) 2 (volume : Measure (Torus d)) := fun n => by
    simpa only [ENNReal.ofReal_ofNat] using (hgn n).2
  have hF : ∀ n, Continuous (convFun (gn n) u) := by
    intro n
    have hui : Integrable u (volume : Measure (Torus d)) := hu.integrable one_le_two
    have := continuous_convFun hui (gn n).continuous
    have e : convFun (gn n) u = convFun u (gn n) := by
      funext x
      rw [convFun_eq']
      unfold convFun
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [mul_comm]
    rw [e]; exact this
  set U : ℝ := (∫ y, u y ^ 2) ^ (1 / 2 : ℝ) with hU
  have hU0 : 0 ≤ U := Real.rpow_nonneg (integral_nonneg fun y => sq_nonneg _) _
  have hunif : TendstoUniformly (fun n => convFun (gn n) u) (convFun g u) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < (ε / (U + 1)) ^ 2 by positivity)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have hsub := q66_conv_sub hg (hgn2 n) hu x
    have hsubL : MemLp (fun y => g y - gn n y) 2 (volume : Measure (Torus d)) := hg.sub (hgn2 n)
    have hb := q66_conv_bound hsubL hu x
    rw [Real.dist_eq, ← hsub]
    have hint : ∫ y, (g y - gn n y) ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
      refine le_trans (le_of_eq ?_) (hgn n).1
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    have h5 : |convFun (fun y => g y - gn n y) u x| ≤ (1 / ((n : ℝ) + 1)) ^ (1 / 2 : ℝ) * U :=
      hb.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (integral_nonneg fun y => sq_nonneg _) hint (by norm_num)) hU0)
    refine lt_of_le_of_lt h5 ?_
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h2 : (1 / ((n : ℝ) + 1)) ^ (1 / 2 : ℝ) < ε / (U + 1) := by
      have h3 : (1 / ((n : ℝ) + 1)) < (ε / (U + 1)) ^ 2 := lt_of_le_of_lt h1 hN
      calc (1 / ((n : ℝ) + 1)) ^ (1 / 2 : ℝ) < ((ε / (U + 1)) ^ 2) ^ (1 / 2 : ℝ) :=
            Real.rpow_lt_rpow (by positivity) h3 (by norm_num)
        _ = ε / (U + 1) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    calc (1 / ((n : ℝ) + 1)) ^ (1 / 2 : ℝ) * U ≤ (ε / (U + 1)) * U :=
          mul_le_mul_of_nonneg_right h2.le hU0
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  exact hunif.continuous (Eventually.of_forall hF).frequently

end HRS.Q66

end
