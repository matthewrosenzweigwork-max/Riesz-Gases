import HRS.MS.S111TermAux1
import HRS.MS.S11GAux9

/-!
# S11.1 terminal wave, part 2: clause (b) and the frozen `r2_tensor_relaxation` from the open producers

`S111tV01` and `S111tV02` are the exact contracts V01 (`paired_physical_sources`) and V02
(`stationary_cubic_reinterpretation`) of Pro's `S11.1-Terminal` skeleton, stated against the live frozen predicates.
They are not assumed anywhere in the project: every theorem below is conditional on them.  The terminal assembly
(`S11X2ClauseB` from V01, V02, T05, T10; then the frozen type; then S11.2) is fully proved.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111T

open HRS.Whole
open HRS (Euc)

/-- Contract V01 (`paired_physical_sources`): two physical source triples at the same shift with BV-difference bounds. -/
def S111tV01 (d : ℕ) (s a beta gamma T lam : ℝ) : Prop :=
  ∃ c0 B : ℝ, 0 < c0 ∧ 0 ≤ B ∧ ∀ rho : Euc d → ℝ,
    IsThermalEquilibrium d s a beta rho →
    IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
    ∀ u : ℝ, 0 ≤ u → ∀ Ku Kb : projTensor (R2X d T) 3,
    IsR2PathCubic d s a beta gamma rho T u Ku →
    IsR2PathCubic d s a beta beta rho T u Kb →
    ∃ Su : PhysicalCubicSources d s a beta gamma rho T u Ku,
    ∃ Sb : PhysicalCubicSources d s a beta beta rho T u Kb,
      ‖Su.initial - Sb.initial‖ ≤ B * Real.exp (-3 * c0 * u) ∧
      eVariationOn (fun v => Su.drift v - Sb.drift v) (Set.Icc 0 (u + T)) ≤
        ENNReal.ofReal (B * ∫ v in Set.Icc 0 (u + T),
          Real.exp (-c0 * max (u - v) 0) * Real.exp (-(lam / beta) * v)) ∧
      eVariationOn (fun v => Su.covariance v - Sb.covariance v) (Set.Icc 0 (u + T)) ≤
        ENNReal.ofReal (B * ∫ v in Set.Icc 0 (u + T),
          Real.exp (-2 * c0 * max (u - v) 0) * Real.exp (-(lam / beta) * v))

/-- Contract V02 (`stationary_cubic_reinterpretation`): the given time-zero stationary cubic tensor has the shifted formula. -/
def S111tV02 (d : ℕ) (s a beta T : ℝ) : Prop :=
  ∀ u : ℝ, 0 ≤ u → ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
    ∀ Kb : projTensor (R2X d T) 3,
    IsR2PathCubic d s a beta beta rho T 0 Kb → IsR2PathCubic d s a beta beta rho T u Kb

/-- **Clause (b) of `r2_tensor_relaxation` from V01, V02, T05 and T10.** -/
theorem s111t_clauseB_of_producers (d : ℕ) (s a beta gamma T lam : ℝ) (hT : 0 < T) (hbeta : 0 < beta)
    (hlam : 0 < lam) (hV01 : S111tV01 d s a beta gamma T lam) (hV02 : S111tV02 d s a beta T) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
      HRS.MS.S111X2.S11X2ClauseB d s a beta gamma T c C rho := by
  obtain ⟨c0, B0, hc0, hB0, hsources⟩ := hV01
  have hkappa : 0 < lam / beta := div_pos hlam hbeta
  set c : ℝ := min c0 (lam / beta) / 2 with hcdef
  have hmin : 0 < min c0 (lam / beta) := lt_min hc0 hkappa
  have hc : 0 < c := by rw [hcdef]; positivity
  have hc1 : c < c0 := by
    have := min_le_left c0 (lam / beta); rw [hcdef]; linarith
  have hc2 : c < lam / beta := by
    have := min_le_right c0 (lam / beta); rw [hcdef]; linarith
  obtain ⟨C, hC, hrel⟩ := s111t_source_norm_to_relaxation d T c0 (lam / beta) c B0 hT hc0 hkappa hc hc1 hc2 hB0
  refine ⟨c, hc, C, fun rho hrho hp u hu Ku Kb hKu hKb => ?_⟩
  have hKbu := hV02 u hu rho hrho Kb hKb
  obtain ⟨Su, Sb, hI, hD, hJ⟩ := hsources rho hrho hp u hu Ku Kb hKu hKbu
  exact hrel u hu Ku Kb Su.toCubicSources Sb.toCubicSources hI hD hJ

/-- **`r2_tensor_relaxation` (frozen type) from V01 and V02**, clause (a) being the proved `s111x2_clauseA`. -/
theorem s111t_tensor_relaxation_of_producers {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (a β γ : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam) (hV01 : S111tV01 d s a β γ T lam) (hV02 : S111tV02 d s a β T) :
    type_of% (r2_tensor_relaxation hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam) :=
  HRS.MS.S111X2.s111x2_tensor_relaxation_of_parts hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
    (HRS.MS.S111X2.s111x2_clauseA hd s a β γ T lam hs0 hs ha hβ hγ hT hlam)
    (s111t_clauseB_of_producers d s a β γ T lam hT hβ hlam hV01 hV02)

/-- **S11.2 (`r2_two_parameter_edgeworth`) from the producers V01 (at `γ` and at `β`) and V02.** -/
theorem s111t_two_param_of_producers {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (a β γ : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam) (hV01 : S111tV01 d s a β γ T lam) (hV01β : S111tV01 d s a β β T lam)
    (hV02 : S111tV02 d s a β T) :
    type_of% (r2_two_parameter_edgeworth hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam) :=
  HRS.MS.S11G.s11g_two_param_of_relaxation hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
    (s111t_tensor_relaxation_of_producers hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam hV01 hV02)
    (s111t_tensor_relaxation_of_producers hd s hs0 hs a β β ha hβ hβ.le (fun _ => hβ) T hT lam hlam hV01β hV02)

end HRS.MS.S111T
