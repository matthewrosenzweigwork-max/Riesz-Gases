import HRS.Main.EqBiasAux4
import HRS.Equilibrium.L49Aux6

/-!
# EQ-BIAS, S8a: the model radial integral `∫_{|w|<δ} |w|^{-2s} e^{-u|w|^{-s}} dw` (supercritical `p = d/s ∈ (1,2)`)

`eqbias_model`: `= (|𝕊^{d-1}|/s) ((1/u)^{2-p} Γ(2-p) - I₀)` with `0 ≤ I₀ ≤ (δ^{-s})^{2-p}/(2-p)`
(polar coordinates, substitution `v = r^{-s}` (`integral_comp_rpow_Ioi`), and the Gamma integral).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

open HRS.LocalDivAux

/-- Gamma tail: `∫_{v>a} v^{1-p} e^{-uv} = (1/u)^{2-p}Γ(2-p) - I₀`, `0 ≤ I₀ ≤ a^{2-p}/(2-p)`. -/
theorem eqbias_gamma_tail {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {a : ℝ} (ha : 0 < a) {u : ℝ}
    (hu : 0 < u) :
    ∃ I₀ : ℝ, 0 ≤ I₀ ∧ I₀ ≤ a ^ (2 - p) / (2 - p) ∧
      ∫ v in Ioi a, v ^ (1 - p) * Real.exp (-(u * v)) =
        (1 / u) ^ (2 - p) * Real.Gamma (2 - p) - I₀ := by
  have hfull : IntegrableOn (fun v : ℝ => v ^ (1 - p) * Real.exp (-(u * v))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1 - p) (b := u)
      (by linarith) one_pos hu
    refine this.congr_fun (fun v hv => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have hG : ∫ v in Ioi (0 : ℝ), v ^ (1 - p) * Real.exp (-(u * v)) =
      (1 / u) ^ (2 - p) * Real.Gamma (2 - p) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2 - p) (r := u) (by linarith) hu
    rw [show (1 : ℝ) - p = 2 - p - 1 by ring]
    exact this
  have hsplit : Ioi (0 : ℝ) = Ioc 0 a ∪ Ioi a := (Ioc_union_Ioi_eq_Ioi ha.le).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) a) (Ioi a) := Ioc_disjoint_Ioi le_rfl
  have hint1 : IntegrableOn (fun v : ℝ => v ^ (1 - p) * Real.exp (-(u * v))) (Ioc 0 a) :=
    hfull.mono_set (by rw [hsplit]; exact subset_union_left)
  have hint2 : IntegrableOn (fun v : ℝ => v ^ (1 - p) * Real.exp (-(u * v))) (Ioi a) :=
    hfull.mono_set (by rw [hsplit]; exact subset_union_right)
  refine ⟨∫ v in Ioc (0 : ℝ) a, v ^ (1 - p) * Real.exp (-(u * v)), ?_, ?_, ?_⟩
  · exact setIntegral_nonneg measurableSet_Ioc fun v hv =>
      mul_nonneg (Real.rpow_nonneg hv.1.le _) (Real.exp_pos _).le
  · have hpow : IntegrableOn (fun v : ℝ => v ^ (1 - p)) (Ioc 0 a) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    calc ∫ v in Ioc (0 : ℝ) a, v ^ (1 - p) * Real.exp (-(u * v))
        ≤ ∫ v in Ioc (0 : ℝ) a, v ^ (1 - p) := by
          refine setIntegral_mono_on hint1 hpow measurableSet_Ioc fun v hv => ?_
          have h1 : Real.exp (-(u * v)) ≤ 1 := by
            rw [Real.exp_le_one_iff]; have := hv.1; nlinarith
          calc v ^ (1 - p) * Real.exp (-(u * v)) ≤ v ^ (1 - p) * 1 :=
                mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hv.1.le _)
            _ = _ := mul_one _
      _ = a ^ (2 - p) / (2 - p) := by
          rw [← intervalIntegral.integral_of_le ha.le, integral_rpow (Or.inl (by linarith))]
          rw [show 1 - p + 1 = 2 - p by ring, Real.zero_rpow (by linarith)]
          ring
  · have := setIntegral_union hdisj measurableSet_Ioi hint1 hint2
    rw [← hsplit, hG] at this
    linarith

/-- The model radial integral. -/
theorem eqbias_model (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (hp2 : (d : ℝ) / s < 2) {δ : ℝ} (hδ : 0 < δ) {u : ℝ} (hu : 0 < u) :
    ∃ I₀ : ℝ, 0 ≤ I₀ ∧ I₀ ≤ (δ ^ (-s)) ^ (2 - (d : ℝ) / s) / (2 - (d : ℝ) / s) ∧
      ∫ w : Euc d, (Ioc (0 : ℝ) δ).indicator
          (fun r : ℝ => r ^ (-(2 * s)) * Real.exp (-(u * r ^ (-s)))) ‖w‖ =
        ballConst d / s * ((1 / u) ^ (2 - (d : ℝ) / s) * Real.Gamma (2 - (d : ℝ) / s) - I₀) := by
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  set p : ℝ := (d : ℝ) / s with hp
  have hsp : s * p = d := by rw [hp]; field_simp
  have haδ : 0 < δ ^ (-s) := Real.rpow_pos_of_pos hδ _
  obtain ⟨I₀, hI0, hI1, hI2⟩ := eqbias_gamma_tail hp1 hp2 haδ hu
  refine ⟨I₀, hI0, hI1, ?_⟩
  rw [integral_radial hd]
  -- the one-dimensional integral
  set g : ℝ → ℝ := (Ici (δ ^ (-s))).indicator (fun v => v ^ (1 - p) * Real.exp (-(u * v))) with hg
  have hsub := integral_comp_rpow_Ioi g (p := -s) (by linarith)
  have hpt : ∀ r ∈ Ioi (0 : ℝ), (|-s| * r ^ (-s - 1)) • g (r ^ (-s)) =
      s * (r ^ (d - 1) * (Ioc (0 : ℝ) δ).indicator
        (fun r : ℝ => r ^ (-(2 * s)) * Real.exp (-(u * r ^ (-s)))) r) := by
    intro r hr
    have hr0 : 0 < r := hr
    rw [abs_neg, abs_of_pos hs0, smul_eq_mul]
    by_cases hrδ : r ≤ δ
    · have h1 : r ^ (-s) ∈ Ici (δ ^ (-s)) := by
        simp only [mem_Ici]
        exact Real.rpow_le_rpow_of_nonpos hr0 hrδ (by linarith)
      rw [hg, indicator_of_mem h1, indicator_of_mem (show r ∈ Ioc (0 : ℝ) δ from ⟨hr0, hrδ⟩)]
      have e1 : (r ^ (-s)) ^ (1 - p) = r ^ (-s * (1 - p)) := by
        rw [← Real.rpow_mul hr0.le]
      have e2 : r ^ (d - 1) = r ^ ((d : ℝ) - 1) := by
        rw [← Real.rpow_natCast]; congr 1; push_cast
        rw [Nat.cast_sub hd]; simp
      rw [e1, e2]
      have e3 : r ^ (-s - 1) * r ^ (-s * (1 - p)) = r ^ ((d : ℝ) - 1) * r ^ (-(2 * s)) := by
        rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]
        congr 1
        linarith [hsp]
      calc s * r ^ (-s - 1) * (r ^ (-s * (1 - p)) * Real.exp (-(u * r ^ (-s))))
          = s * ((r ^ (-s - 1) * r ^ (-s * (1 - p))) * Real.exp (-(u * r ^ (-s)))) := by ring
        _ = _ := by rw [e3]; ring
    · have h1 : r ^ (-s) ∉ Ici (δ ^ (-s)) := by
        simp only [mem_Ici, not_le]
        exact Real.rpow_lt_rpow_of_neg hδ (not_le.1 hrδ) (by linarith)
      rw [hg, indicator_of_notMem h1, indicator_of_notMem (show r ∉ Ioc (0 : ℝ) δ from
        fun h => hrδ h.2)]
      simp
  have hcongr : ∫ r in Ioi (0 : ℝ), (|-s| * r ^ (-s - 1)) • g (r ^ (-s)) =
      s * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * (Ioc (0 : ℝ) δ).indicator
        (fun r : ℝ => r ^ (-(2 * s)) * Real.exp (-(u * r ^ (-s)))) r := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi hpt
  have hgint : ∫ y in Ioi (0 : ℝ), g y = ∫ v in Ioi (δ ^ (-s)), v ^ (1 - p) * Real.exp (-(u * v)) := by
    rw [hg, setIntegral_indicator measurableSet_Ici]
    have hset : Ioi (0 : ℝ) ∩ Ici (δ ^ (-s)) = Ici (δ ^ (-s)) := by
      ext v
      simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      exact ⟨fun h => h.2, fun h => ⟨haδ.trans_le h, h⟩⟩
    rw [hset, integral_Ici_eq_integral_Ioi]
  rw [hcongr, hgint, hI2] at hsub
  have hs0' : s ≠ 0 := hs0.ne'
  have hI : ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * (Ioc (0 : ℝ) δ).indicator
        (fun r : ℝ => r ^ (-(2 * s)) * Real.exp (-(u * r ^ (-s)))) r =
      ((1 / u) ^ (2 - p) * Real.Gamma (2 - p) - I₀) / s := by
    rw [eq_div_iff hs0']
    linarith [hsub]
  rw [hI]
  ring

end Main

end HRS

end
