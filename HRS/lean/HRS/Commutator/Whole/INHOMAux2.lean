import HRS.Commutator.Whole.LOWVAux11
import HRS.Commutator.Whole.INHOMAux1
import HRS.Commutator.Whole.Energy

/-!
# CMX-INHOM auxiliary 2: a real Schwartz density `a dx` as a signed measure
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma inhom_schw_props {a : Euc d → ℝ} {φ : SchwartzMap (Euc d) ℂ}
    (hφ : ∀ x, φ x = ((a x : ℝ) : ℂ)) :
    Continuous a ∧ Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|) volume ∧
      (∃ M : ℝ, ∀ x, |a x| ≤ M) ∧ Integrable a volume ∧
      Integrable (fun x : Euc d => a x ^ 2) volume := by
  have habs : ∀ x, |a x| = ‖φ x‖ := fun x => by
    rw [hφ x, Complex.norm_real, Real.norm_eq_abs]
  have hac : Continuous a := by
    have : a = fun x => (φ x).re := by funext x; rw [hφ x]; simp
    rw [this]; exact Complex.continuous_re.comp φ.continuous
  have hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|) volume := by
    have := cmxFB_integrable_pow_mul φ 1
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [habs, pow_one]
  obtain ⟨C0, hC00, hC0⟩ := cmxFB_decay φ 0
  have hM : ∀ x, |a x| ≤ C0 := fun x => by
    rw [habs]; simpa using hC0 x
  obtain ⟨ha1, -⟩ := lowv_a_int_aux hac hai
  have ha2 : Integrable (fun x : Euc d => a x ^ 2) volume := by
    refine (ha1.const_mul C0).mono' (hac.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq]
    calc |a x| * |a x| ≤ C0 * |a x| := by gcongr; exact hM x
      _ = _ := rfl
  have ha1' : Integrable a volume :=
    (integrable_norm_iff hac.aestronglyMeasurable).1 (by simpa [Real.norm_eq_abs] using ha1)
  exact ⟨hac, hai, ⟨C0, hM⟩, ha1', ha2⟩

lemma inhom_ofDensity_finite {a : Euc d → ℝ} (hint : Integrable a volume) :
    (SMeas.ofDensity a).IsFinite :=
  ⟨isFiniteMeasure_withDensity_ofReal hint.2, isFiniteMeasure_withDensity_ofReal hint.neg.2⟩

lemma inhom_ofDensity_admissible {a : Euc d → ℝ} {φ : SchwartzMap (Euc d) ℂ}
    (hφ : ∀ x, φ x = ((a x : ℝ) : ℂ)) : IsAdmissible (SMeas.ofDensity a) :=
  ⟨inhom_ofDensity_finite (inhom_schw_props hφ).2.2.2.1, Or.inr ⟨a, ⟨φ, hφ⟩, rfl⟩⟩

lemma inhom_ofDensity_mass {a : Euc d → ℝ} (hm : Measurable a) (hint : Integrable a volume) :
    (SMeas.ofDensity a).mass = ∫ x, a x := by
  unfold SMeas.mass
  rw [energyAux_int_ofDensity a (fun _ => 1) hm (by simpa using hint)]
  simp

lemma inhom_ofDensity_fourier {a : Euc d → ℝ} (hm : Measurable a) (hint : Integrable a volume)
    (ξ : Euc d) :
    (SMeas.ofDensity a).fourier ξ = 𝓕 (fun x : Euc d => ((a x : ℝ) : ℂ)) ξ := by
  have hc : Continuous fun x : Euc d => (Complex.exp (-(2 * Real.pi * Complex.I *
      (inner ℝ x ξ : ℝ))) : ℂ) := by fun_prop
  have hint' : Integrable (fun x : Euc d => a x • (Complex.exp (-(2 * Real.pi * Complex.I *
      (inner ℝ x ξ : ℝ))) : ℂ)) := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ x : Euc d, ‖(Complex.exp (-(2 * Real.pi * Complex.I *
        (inner ℝ x ξ : ℝ))) : ℂ)‖ ≤ C := ⟨1, fun x => by
          rw [Complex.norm_exp]; simp⟩
    refine Integrable.mono' (g := fun x => C * ‖a x‖) (hint.norm.const_mul C) ?_ ?_
    · exact (hm.smul hc.measurable).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _) |>.trans_eq' (by ring)
  have hgen := energyAux_int_ofDensity_gen a (fun x : Euc d => (Complex.exp (-(2 * Real.pi *
    Complex.I * (inner ℝ x ξ : ℝ))) : ℂ)) hm hint'
  have e1 : (SMeas.ofDensity a).fourier ξ = ∫ x, a x • (Complex.exp (-(2 * Real.pi * Complex.I *
      (inner ℝ x ξ : ℝ))) : ℂ) := by
    unfold SMeas.fourier
    exact hgen
  rw [e1, Real.fourier_eq']
  congr 1
  funext x
  rw [Complex.real_smul, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

lemma inhom_ofDensity_intV {a : Euc d → ℝ} (hm : Measurable a) {g : Euc d → Euc d}
    (hg : Integrable (fun x => a x • g x) volume) :
    (SMeas.ofDensity a).intV g = ∫ x, a x • g x :=
  energyAux_int_ofDensity_gen a g hm hg
