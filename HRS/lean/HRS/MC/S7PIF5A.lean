import HRS.MC.S7PIF4

/-!
# Packet piF5, part A: joint measurability of `(r, F) ↦ eval F (obsTest_i r)`

`S7PIF5_g R m T t φ i (r, F) = 1_{r ≥ 0} eval F (obsTest_i r)` is a Borel function of `(r, F) ∈ ℝ × E_m`
(through the joint continuity of `(u, F) ↦ V^{τ,u} F` and `eval (V^{τ,r} F) φ = eval F (U^{r,τ} φ)`), and bounded by
`C ‖F‖` uniformly in `r`.  Namespace `HRS.MC.Sec7.S7PIF5`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF5

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF4

variable {d : ℕ}

/-- the evaluation of `F` on the frozen test function, restricted to `r ≥ 0` -/
def S7PIF5_g (D : DynData d) (ρ : ℝ → Torus d → ℝ) {m : ℝ} {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (i : Fin q) (p : ℝ × NegSobolev d m) : ℝ :=
  if 0 ≤ p.1 then NegSobolev.eval p.2 (obsTest D ρ t φ i p.1) else 0

theorem S7PIF5_g_neg (D : DynData d) (ρ : ℝ → Torus d → ℝ) {m : ℝ} {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (i : Fin q) {r : ℝ} (hr : ¬ 0 ≤ r) (F : NegSobolev d m) :
    S7PIF5_g D ρ t φ i (r, F) = 0 := by
  unfold S7PIF5_g; simp [hr]

theorem S7PIF5_g_pos (D : DynData d) (ρ : ℝ → Torus d → ℝ) {m : ℝ} {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (i : Fin q) {r : ℝ} (hr : 0 ≤ r) (F : NegSobolev d m) :
    S7PIF5_g D ρ t φ i (r, F) = NegSobolev.eval F (obsTest D ρ t φ i r) := by
  unfold S7PIF5_g; simp [hr]

/-- `eval F 0 = 0` after `t_i`; the value of `g` at `r > t_i` is `0` -/
theorem S7PIF5_g_gt (D : DynData d) (ρ : ℝ → Torus d → ℝ) {m : ℝ} {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (i : Fin q) {r : ℝ} (hr : t i < r) (F : NegSobolev d m) :
    S7PIF5_g D ρ t φ i (r, F) = 0 := by
  unfold S7PIF5_g obsTest
  by_cases h0 : 0 ≤ r
  · simp [h0, not_le.2 hr, S7PIF4_eval_zero_fun]
  · simp [h0]

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- `g` is a Borel function of `(r, F)` -/
theorem S7PIF5_g_meas {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (i : Fin q) :
    Measurable (S7PIF5_g R.D R.ρ (m := m) t φ i) := by
  have hτ := ht i
  have hws : A33WS m (φ i) := a33_ws_smooth m (hφ i)
  rcases hτ.1.eq_or_lt with h0 | hpos
  · -- `t_i = 0`
    have heq : S7PIF5_g R.D R.ρ (m := m) t φ i = fun p => if p.1 = 0 then NegSobolev.eval p.2 (φ i) else 0 := by
      funext ⟨r, F⟩
      show S7PIF5_g R.D R.ρ t φ i (r, F) = if r = 0 then NegSobolev.eval F (φ i) else 0
      by_cases hp : 0 ≤ r
      · rw [S7PIF5_g_pos _ _ _ _ _ hp]
        unfold obsTest
        by_cases hp0 : r = 0
        · rw [if_pos hp0, if_pos (by rw [hp0, ← h0])]
          rw [hp0, ← h0, S7PIF4_prop_self R m hm T hT N hN P X₀ W X hreal (hφ i) ⟨le_rfl, hT.le⟩]
        · rw [if_neg hp0, if_neg (by rw [← h0]; exact fun h => hp0 (le_antisymm h hp))]
          exact S7PIF4_eval_zero_fun m _
      · rw [S7PIF5_g_neg _ _ _ _ _ hp, if_neg (fun h => hp h.symm.le)]
    rw [heq]
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) ?_ measurable_const
    exact ((S7PIF4_evalCLM m hws).continuous.comp continuous_snd).measurable
  · -- `t_i > 0`
    set τ := t i with hτdef
    have hτ' : τ ∈ Set.Ioc 0 T := ⟨hpos, hτ.2⟩
    obtain ⟨CV, hCV0, hCV, hjc⟩ := S7PIF4_core R m hm T hT
    have hproj : Continuous (fun p : ℝ × NegSobolev d m => (Set.projIcc 0 τ hpos.le p.1, p.2)) :=
      (continuous_projIcc.comp continuous_fst).prodMk continuous_snd
    have hΦ : Continuous (fun p : ℝ × NegSobolev d m =>
        NegSobolev.eval (Vprop R.D R.ρ m τ (Set.projIcc 0 τ hpos.le p.1).1 p.2) (φ i)) := by
      have h : Continuous ((fun p : Set.Icc (0 : ℝ) τ × NegSobolev d m =>
          S7PIF4_evalCLM m hws (Vprop R.D R.ρ m τ p.1.1 p.2)) ∘
          (fun p : ℝ × NegSobolev d m => (Set.projIcc 0 τ hpos.le p.1, p.2))) :=
        Continuous.comp ((S7PIF4_evalCLM m hws).continuous.comp (hjc τ hτ')) hproj
      exact h
    have hset : MeasurableSet {p : ℝ × NegSobolev d m | 0 ≤ p.1 ∧ p.1 ≤ τ} :=
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)
    have heq : S7PIF5_g R.D R.ρ (m := m) t φ i = Set.indicator {p : ℝ × NegSobolev d m | 0 ≤ p.1 ∧ p.1 ≤ τ}
        (fun p => NegSobolev.eval (Vprop R.D R.ρ m τ (Set.projIcc 0 τ hpos.le p.1).1 p.2) (φ i)) := by
      funext ⟨r, F⟩
      show S7PIF5_g R.D R.ρ t φ i (r, F) = Set.indicator {p : ℝ × NegSobolev d m | 0 ≤ p.1 ∧ p.1 ≤ τ}
        (fun p => NegSobolev.eval (Vprop R.D R.ρ m τ (Set.projIcc 0 τ hpos.le p.1).1 p.2) (φ i)) (r, F)
      by_cases hp : 0 ≤ r
      · rw [S7PIF5_g_pos _ _ _ _ _ hp]
        by_cases hp1 : r ≤ τ
        · rw [Set.indicator_of_mem (show (r, F) ∈ {p : ℝ × NegSobolev d m | 0 ≤ p.1 ∧ p.1 ≤ τ} from ⟨hp, hp1⟩)]
          unfold obsTest
          rw [if_pos hp1]
          show _ = NegSobolev.eval (Vprop R.D R.ρ m τ (Set.projIcc 0 τ hpos.le r).1 F) (φ i)
          rw [Set.projIcc_of_mem _ ⟨hp, hp1⟩]
          exact (HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm T hT r τ hp hp1 hτ.2 F (φ i) (hφ i)).symm
        · rw [Set.indicator_of_notMem (show (r, F) ∉ {p : ℝ × NegSobolev d m | 0 ≤ p.1 ∧ p.1 ≤ τ} from
            fun h => hp1 h.2)]
          unfold obsTest
          rw [if_neg hp1]
          exact S7PIF4_eval_zero_fun m _
      · rw [S7PIF5_g_neg _ _ _ _ _ hp]
        rw [Set.indicator_of_notMem (show (r, F) ∉ {p : ℝ × NegSobolev d m | 0 ≤ p.1 ∧ p.1 ≤ τ} from
          fun h => hp h.1)]
    rw [heq]
    exact hΦ.measurable.indicator hset

/-- `|g| ≤ C ‖F‖` -/
theorem S7PIF5_g_bound {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (i : Fin q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r (F : NegSobolev d m), 0 < r → |S7PIF5_g R.D R.ρ t φ i (r, F)| ≤ C * ‖F‖ := by
  have hτ := ht i
  have hws : A33WS m (φ i) := a33_ws_smooth m (hφ i)
  rcases hτ.1.eq_or_lt with h0 | hpos
  · refine ⟨0, le_rfl, fun r F hr => ?_⟩
    rw [S7PIF5_g_gt R.D R.ρ t φ i (by rw [← h0]; exact hr) F]
    simp
  · obtain ⟨C, hC0, hC⟩ := S7PIF4_eval_prop_bound R m hm T hT (hφ i)
    refine ⟨C, hC0, fun r F hr => ?_⟩
    by_cases h1 : r ≤ t i
    · rw [S7PIF5_g_pos _ _ _ _ _ hr.le]
      unfold obsTest
      rw [if_pos h1]
      exact hC (t i) ⟨hpos, hτ.2⟩ r ⟨hr.le, h1⟩ F
    · rw [S7PIF5_g_gt R.D R.ρ t φ i (not_le.1 h1) F]
      simpa using mul_nonneg hC0 (norm_nonneg F)

end Prob

end HRS.MC.Sec7.S7PIF5

end
