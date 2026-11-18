/-
# HRS.Equilibrium.Q84dAuxJ — packet Q84d: integrability of `quadStat` (D2, first conjunct)
-/
import HRS.Equilibrium.Q84dAuxI

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

section Setting

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem q84d_q_le_const {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ X : Config d N,
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) ≤ Q := by
  obtain ⟨c, hc⟩ := q84d_hlow hd hcrit hV hN
  refine ⟨Real.exp (β * c), (Real.exp_pos _).le, fun X => ?_⟩
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hc X]

theorem q84d_integral_bound_of_le_w {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ)
    {h : Torus d → Torus d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hh : ∀ x y : Torus d, x ≠ y → |h x y| ≤ B * wEnv s x y) :
    ∃ M : ℝ, ∀ x : Torus d, |∫ y, h x y ∂(withDensityReal ρ)| ≤ M := by
  obtain ⟨Mμ, hMμ0, hMμ⟩ := q84d_integral_wEnv_mu_le hd hcrit hρs
  refine ⟨B * Mμ, fun x => ?_⟩
  obtain ⟨hint, hle⟩ := hMμ x
  have hae : ∀ᵐ y ∂(withDensityReal ρ), ‖h x y‖ ≤ B * wEnv s x y := by
    have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
      rw [ae_iff]; simpa using volume_singleton_torus (by omega) x
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h0] with y hy
    rw [Real.norm_eq_abs]; exact hh x y hy.symm
  have := norm_integral_le_of_norm_le (hint.const_mul B) hae
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hle hB

end Setting

section QuadStat

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem q84d_integrable_quadStat {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) :
    Integrable (quadStat (hTransport d s f) (withDensityReal ρ) (N := N))
      (canonicalGibbs (periodicRiesz d s) V N β) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρs.density
  set h := hTransport d s f with hh
  have hhm : Measurable (fun p : Torus d × Torus d => h p.1 p.2) :=
    HRS.LocalDivAux.measurable_hTransport hsd hf
  obtain ⟨Bf, hBf0, hBf⟩ := q84d_hTransport_le_w hd hs0 hsd hf
  obtain ⟨Mm, hMm⟩ := q84d_integral_bound_of_le_w hd hcrit hρs hBf0 hBf
  obtain ⟨C₁, hC₁0, hC₁⟩ := q84d_q_mul_w_le hd hcrit hV hβ hN
  obtain ⟨Q, hQ0, hQ⟩ := q84d_q_le_const hd hcrit hV hβ hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hmm : Measurable (fun x : Torus d => ∫ y, h x y ∂(withDensityReal ρ)) :=
    (hhm.stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρ)).measurable
  set c₃ : ℝ := ∫ x, ∫ y, h x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hc₃
  have hMm0 : 0 ≤ Mm := (abs_nonneg _).trans (hMm 0)
  refine q84d_integrable_of_q_bound hd hcrit hV hβ hN (C := (1 / (N : ℝ) ^ 2) * (N * (N * (Bf * C₁))) +
      2 * (1 / (N : ℝ)) * (N * (Q * Mm)) + Q * |c₃|) ?_ ?_
  · -- measurability
    unfold quadStat
    refine AEStronglyMeasurable.add (AEStronglyMeasurable.sub ?_ ?_) aestronglyMeasurable_const
    · exact (q84d_aesm_pairSum (N := N) hhm.aestronglyMeasurable).const_mul _
    · refine AEStronglyMeasurable.const_mul (AEStronglyMeasurable.const_mul ?_ _) _
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (hmm.comp (measurable_pi_apply i)).aestronglyMeasurable
  · intro X hX
    set q := Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) with hq
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hXne : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij hXij => hX ⟨i, j, hij, hXij⟩
    have hps := q84d_pairSum_bound q hq0 h X (M := Bf * C₁) (mul_nonneg hBf0 hC₁0) (fun i j hij => by
      have h1 := (hC₁ X i j hij).1
      have h2 := hBf (X i) (X j) (hXne i j hij)
      calc q * |h (X i) (X j)| ≤ q * (Bf * wEnv s (X i) (X j)) :=
            mul_le_mul_of_nonneg_left h2 hq0
        _ = Bf * (q * wEnv s (X i) (X j)) := by ring
        _ ≤ Bf * C₁ := mul_le_mul_of_nonneg_left h1 hBf0)
    have hsum : q * |∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ)| ≤ N * (Q * Mm) := by
      calc q * |∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ)|
          ≤ q * ∑ i, |∫ y, h (X i) y ∂(withDensityReal ρ)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hq0
        _ = ∑ i, q * |∫ y, h (X i) y ∂(withDensityReal ρ)| := by rw [Finset.mul_sum]
        _ ≤ ∑ _i : Fin N, (Q * Mm) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact mul_le_mul (hQ X) ((hMm (X i))) (abs_nonneg _) hQ0
        _ = N * (Q * Mm) := by simp
    have hqc : q * |c₃| ≤ Q * |c₃| := mul_le_mul_of_nonneg_right (hQ X) (abs_nonneg _)
    unfold quadStat
    have e1 : (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) =
        (1 / (N : ℝ) ^ 2) * pairSumOrdered h X := rfl
    rw [e1]
    set A := pairSumOrdered h X with hA
    set Bs := ∑ i, ∫ y, h (X i) y ∂(withDensityReal ρ) with hBs
    calc q * |(1 / (N : ℝ) ^ 2) * A - 2 * ((1 / (N : ℝ)) * Bs) + c₃|
        ≤ q * (|(1 / (N : ℝ) ^ 2) * A| + |2 * ((1 / (N : ℝ)) * Bs)| + |c₃|) := by
          refine mul_le_mul_of_nonneg_left ?_ hq0
          calc _ ≤ |(1 / (N : ℝ) ^ 2) * A - 2 * ((1 / (N : ℝ)) * Bs)| + |c₃| := abs_add_le _ _
            _ ≤ _ := by gcongr; exact abs_sub _ _
      _ = (1 / (N : ℝ) ^ 2) * (q * |A|) + 2 * (1 / (N : ℝ)) * (q * |Bs|) + q * |c₃| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (N : ℝ) ^ 2),
            abs_of_pos (by positivity : (0:ℝ) < 2), abs_of_pos (by positivity : (0:ℝ) < 1 / (N : ℝ))]
          ring
      _ ≤ (1 / (N : ℝ) ^ 2) * (N * (N * (Bf * C₁))) + 2 * (1 / (N : ℝ)) * (N * (Q * Mm)) + Q * |c₃| := by
          gcongr

end QuadStat

end HRS.Q84d

end
