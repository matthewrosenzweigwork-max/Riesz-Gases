import HRS.MS.R26T8AP24
import HRS.MS.R26T8AP26

/-!
# S8.2 local Newton layer, packet T8A.P27 (part a): time bound and regularity of the pair inverse
`b(t) = c1 on (0,1], c2 e^{-ct} on (1,oo)`: the jets of `S_t R = tensorU U t R` are `<= b(t) w` with `c1 = 3 C0 (nu0 + delta)`
(P24 jets) and `c2 = Cj nu0` (clause 4b of the merged S8.3), `nu0 = pairNormE M 8 R`; then `s8h2_param_set` integrates.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ} {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

def r26t8a_p27_b (c1 c2 c : ℝ) : ℝ → ℝ := fun t =>
  (Set.Ioc (0 : ℝ) 1).indicator (fun _ => c1) t +
    (Set.Ioi (1 : ℝ)).indicator (fun t => c2 * Real.exp (-c * t)) t

theorem r26t8a_p27_b_props {c1 c2 c : ℝ} (hc : 0 < c) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    Integrable (r26t8a_p27_b c1 c2 c) ∧ (∀ t, 0 ≤ r26t8a_p27_b c1 c2 c t) ∧
    ∫ t in Set.Ioi (0 : ℝ), r26t8a_p27_b c1 c2 c t = c1 + c2 * ∫ t in Set.Ioi (1 : ℝ), Real.exp (-c * t) := by
  have hi2 : IntegrableOn (fun t : ℝ => c2 * Real.exp (-c * t)) (Set.Ioi 1) :=
    (integrableOn_exp_mul_Ioi (a := -c) (by linarith) (1 : ℝ)).const_mul c2
  have hi1 : Integrable ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => c1)) :=
    (integrable_indicator_iff measurableSet_Ioc).2 continuous_const.integrableOn_Ioc
  have hi2' : Integrable ((Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => c2 * Real.exp (-c * t))) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hi2
  refine ⟨hi1.add hi2', fun t => add_nonneg (Set.indicator_nonneg (fun _ _ => hc1) t)
    (Set.indicator_nonneg (fun s _ => by positivity) t), ?_⟩
  unfold r26t8a_p27_b
  have e1 : Set.Ioi (0 : ℝ) ∩ Set.Ioc 0 1 = Set.Ioc 0 1 := Set.inter_eq_right.2 fun x hx => hx.1
  have e2 : Set.Ioi (0 : ℝ) ∩ Set.Ioi 1 = Set.Ioi 1 :=
    Set.inter_eq_right.2 fun x (hx : 1 < x) => (zero_lt_one.trans hx : 0 < x)
  rw [integral_add hi1.integrableOn hi2'.integrableOn, setIntegral_indicator measurableSet_Ioc,
    setIntegral_indicator measurableSet_Ioi, e1, e2, integral_const_mul]
  simp

theorem r26t8a_p27_time
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (hM : 0 ≤ M) {C0 : ℝ}
    (hjet : ∀ {F : Euc d × Euc d → ℝ}, S8hPair M 8 F → ∀ {ν : ℝ}, 0 < ν →
      (∀ i ≤ 8, ∀ z, ‖iteratedFDeriv ℝ i F z‖ ≤ ν * s8h_w M z) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ 8 (s8h2_S U t F) ∧
      ∀ i ≤ 8, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_S U t F) z‖ ≤ 3 * C0 * ν * s8h_w M z)
    {Cj c : ℝ}
    (h4 : ∀ t : ℝ, 1 ≤ t → ∀ R : Euc d → Euc d → ℝ, MemCMpair M 0 R →
      IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R →
      MemCMpair M 8 (tensorU U t R) ∧
      pairNormE M 8 (tensorU U t R) ≤ ENNReal.ofReal (Cj * Real.exp (-c * t)) * pairNormE M 0 R)
    {R : Euc d → Euc d → ℝ} (hR : MemCMpair M 8 R)
    (hdc : IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R) {δ : ℝ} (hδ : 0 < δ) :
    ∀ t : ℝ, 0 < t → ContDiff ℝ 8 (s8h2_S U t (Function.uncurry R)) ∧
      ∀ k ≤ 8, ∀ z, ‖iteratedFDeriv ℝ k (s8h2_S U t (Function.uncurry R)) z‖ ≤
        r26t8a_p27_b (3 * C0 * ((pairNormE M 8 R).toReal + δ)) (max Cj 0 * (pairNormE M 8 R).toReal) c t *
          s8h_w M z := by
  have hRp : S8hPair M 8 (Function.uncurry R) := s8h_pair_iff.1 hR
  obtain ⟨hPtop, hν⟩ := r26t8a_p24_of_pair hRp
  set ν0 : ℝ := (pairNormE M 8 R).toReal with hν0
  have hν0n : 0 ≤ ν0 := ENNReal.toReal_nonneg
  intro t ht
  by_cases ht1 : t ≤ 1
  · have hmem : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
    have h0 : t ∉ Set.Ioi (1 : ℝ) := fun h => by linarith [h.out]
    obtain ⟨hcd, hb⟩ := hjet hRp (ν := ν0 + δ) (by linarith) (fun i hi z =>
      (hν i hi z).trans (mul_le_mul_of_nonneg_right (by linarith) (s8h_w_pos M z).le)) t ⟨ht.le, ht1⟩
    refine ⟨hcd, fun k hk z => ?_⟩
    unfold r26t8a_p27_b
    simp only [Set.indicator_of_mem hmem, Set.indicator_of_notMem h0, add_zero]
    exact hb k hk z
  · push Not at ht1
    have h0 : t ∉ Set.Ioc (0 : ℝ) 1 := fun h => by linarith [h.2]
    have hR0 : MemCMpair M 0 R := s8h_pair_iff.2 (s8h2_pair_mono (Nat.zero_le 8) hRp)
    obtain ⟨hm8, hpn⟩ := h4 t ht1.le R hR0 hdc
    refine ⟨(s8h_pair_iff.1 hm8).1, fun k hk z => ?_⟩
    have hn0 : pairNormE M 0 R ≤ ENNReal.ofReal ν0 :=
      r26t8a_p24_norm_le (fun i hi z => hν i (hi.trans (by norm_num)) z)
    have hle : pairNormE M 8 (tensorU U t R) ≤ ENNReal.ofReal (max Cj 0 * Real.exp (-c * t) * ν0) := by
      calc _ ≤ ENNReal.ofReal (Cj * Real.exp (-c * t)) * pairNormE M 0 R := hpn
        _ ≤ ENNReal.ofReal (max Cj 0 * Real.exp (-c * t)) * ENNReal.ofReal ν0 :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Real.exp_pos _).le)) hn0
        _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
    have hj := r26t8a_p24_jet_of_norm (by positivity) hle k hk z
    unfold r26t8a_p27_b
    simp only [Set.indicator_of_notMem h0, Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from ht1), zero_add]
    refine hj.trans (le_of_eq ?_)
    ring

end HRS.MS.R26T8A
