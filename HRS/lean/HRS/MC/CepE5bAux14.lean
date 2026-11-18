import HRS.MC.CepE5bAux11

/-!
# Packet CEPE5B, auxiliary 14: `(1/n) E Φ_n(z₀) → 0`
-/

open MeasureTheory Filter Topology Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE4 (e4_rho)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e5b_u_tendsto [IsProbabilityMeasure P] {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N}
    (hJ : cep_Yosida a N J) {z0 : Ω → Ch N} (hz0m : Measurable z0) (hz0A : ∀ ω, z0 ω ∈ cep_Alcove N)
    {R : ℝ} (hR : ∀ ω, ‖z0 ω‖ ≤ R) :
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * ∫ ω, e5b_Pn a N J n (z0 ω) ∂P) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  set cL : ℝ := (a / N) * HRS.MC.CepE2.cepe2_npairs N * Real.log 2 with hcL
  set c0 : ℝ := cL + |cep_chamberPot a N (e4_rho N)| with hc0
  have hcL0 : 0 ≤ cL := by
    have : 0 ≤ HRS.MC.CepE2.cepe2_npairs N := by unfold HRS.MC.CepE2.cepe2_npairs; positivity
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hc00 : 0 ≤ c0 := by positivity
  have hpos : ∀ m : ℕ, (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := fun m => by positivity
  have hrew : ∀ m : ℕ, (1 / ((m + 1 : ℕ) : ℝ)) * ∫ ω, e5b_Pn a N J ((m + 1 : ℕ) : ℝ) (z0 ω) ∂P =
      ∫ ω, (1 / ((m + 1 : ℕ) : ℝ)) * e5b_Pn a N J ((m + 1 : ℕ) : ℝ) (z0 ω) ∂P := fun m => by
    rw [integral_const_mul]
  simp_rw [hrew]
  have := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun (m : ℕ) ω => (1 / ((m + 1 : ℕ) : ℝ)) * e5b_Pn a N J ((m + 1 : ℕ) : ℝ) (z0 ω))
    (f := fun _ => (0 : ℝ)) (fun _ => c0 + ‖e4_rho N‖ ^ 2 + R ^ 2)
    (fun m => ?_) (integrable_const _) (fun m => ?_) ?_
  · simpa using this
  · exact (((e5b_contDiff_Pn ha hJ (hpos m)).continuous.measurable.comp hz0m).const_mul _).aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    have hn := hpos m
    have h := e5b_Pn_abs_le ha hJ hn (z0 ω)
    set n : ℝ := ((m + 1 : ℕ) : ℝ) with hn'
    have hn1 : 1 ≤ n := by rw [hn']; exact_mod_cast Nat.succ_pos m
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 1 / n)]
    have h1 : ‖z0 ω‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hR ω) 2
    have h2 : 1 / n * |e5b_Pn a N J n (z0 ω)| ≤ 1 / n * ((c0 + n * ‖e4_rho N‖ ^ 2) + n * ‖z0 ω‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa [hc0, hcL, add_assoc] using h) (by positivity)
    have h3 : 1 / n * ((c0 + n * ‖e4_rho N‖ ^ 2) + n * ‖z0 ω‖ ^ 2) =
        c0 / n + ‖e4_rho N‖ ^ 2 + ‖z0 ω‖ ^ 2 := by field_simp
    have h4 : c0 / n ≤ c0 := div_le_self hc00 hn1
    linarith
  · refine Eventually.of_forall fun ω => ?_
    have hlo : Tendsto (fun m : ℕ => -cL / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (-cL))
    have hhi : Tendsto (fun m : ℕ => cep_chamberPot a N (z0 ω) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun m => ?_) (fun m => ?_)
    · have hn := hpos m
      have := e5b_Pn_lower ha.le hJ hn (z0 ω)
      calc -cL / ((m + 1 : ℕ) : ℝ) ≤ e5b_Pn a N J ((m + 1 : ℕ) : ℝ) (z0 ω) / ((m + 1 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (by simpa [hcL] using this) hn.le
        _ = _ := by ring
    · have hn := hpos m
      have := e5b_Pn_le ha.le hJ hn (z0 ω) (hz0A ω)
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        add_zero] at this
      calc (1 / ((m + 1 : ℕ) : ℝ)) * e5b_Pn a N J ((m + 1 : ℕ) : ℝ) (z0 ω) =
          e5b_Pn a N J ((m + 1 : ℕ) : ℝ) (z0 ω) / ((m + 1 : ℕ) : ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right this hn.le

end HRS.MC.CepE5b
