import HRS.MC.S7PIF4F
import HRS.MC.S7PIM3
import HRS.MC.S7PIS1Eval
import HRS.MC.S7PIS1Path2

/-!
# Packet piF4 (F4): `s7_PIF_coord_ito_proof` (namespace `HRS.MC.Sec7.S7PIF4`)

Each coordinate of the frozen observation `obsVec (𝖳_u ζ_N)` is `ζ_0(U^{0,t_i}φ_i) - N^{-1/2} ∫_{(0,u]} ℬ_N^r(obsTest_i r) dr + √N M^{(i)}_u`.
The statement is copied verbatim from `HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PIF_coord_ito`, integral parenthesised);
the tie is in `HRS/MC/S7PIF4Tie.lean`.  Route: part E/F (`S7PIF4_key_all`: the identity at the observation time `t_i`
for `u ≤ t_i`), `S2` (path facts) and `S1` (`V` is the adjoint of `U`) for the left-hand side, the constancy of the Itô integral
after `t_i` and `obsTest = 0` after `t_i` for `u > t_i`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF4

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- the `r`-integral against `obsTest` stops at `t_i` -/
theorem S7PIF4_obsTest_integral (D : DynData d) (ρ : ℝ → Torus d → ℝ) {m : ℝ} {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (i : Fin q) (b : ℝ → NegSobolev d m) (u : ℝ) :
    ∫ r in Set.Ioc 0 u, NegSobolev.eval (b r) (obsTest D ρ t φ i r) =
      ∫ r in Set.Ioc 0 (min u (t i)), NegSobolev.eval (b r) (propagator D ρ r (t i) (φ i)) := by
  have h : ∀ r, NegSobolev.eval (b r) (obsTest D ρ t φ i r) =
      (Set.Iic (t i)).indicator (fun r => NegSobolev.eval (b r) (propagator D ρ r (t i) (φ i))) r := by
    intro r
    unfold obsTest
    by_cases hr : r ≤ t i
    · simp [hr]
    · simp [hr, S7PIF4_eval_zero_fun]
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Iic]
  congr 1
  ext r
  simp [le_min_iff, and_assoc]

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

theorem s7_PIF_coord_ito_proof {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (i : Fin q) :
    ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) T,
      obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) u) i =
        NegSobolev.eval (zetaAt m P X 0 ω) (propagator R.D R.ρ 0 (t i) (φ i)) -
        (Real.sqrt N)⁻¹ * (∫ r in Set.Ioc 0 u,
          NegSobolev.eval (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r)) +
        Real.sqrt N * empiricalMartingale P ℱ W' R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X u ω := by
  have hτ := ht i
  have hψ := hφ i
  have hM3 := (HRS.MC.Sec7.S7PIM.s7_PIM_zeta_path_proof R m hm T hT N hN P X₀ W X hreal).1
  have hkey := S7PIF4_key_all R m hm T hT N hN P X₀ W X hreal hF hψ hτ
  have hprog : IsProgressiveL2 P ℱ
      (empiricalNoiseIntegrand R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X) := by
    rcases hτ.1.eq_or_lt with h0 | hpos
    · rw [← h0]; exact S7PIF4_prog_zero R m hm T hT N hN P X₀ W X hreal hF hψ
    · exact S7PIF4_prog_pos R m hm T hT N hN P X₀ W X hreal hF hψ ⟨hpos, hτ.2⟩
  have hMc := S7PIF4_mart_const hF.brownian hprog hτ.1 (fun s ω k hs => by
    unfold empiricalNoiseIntegrand; rw [if_neg hs])
  have hPath := (HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof R m hm T hT).1
  filter_upwards [hM3, hkey, hMc] with ω hc hk hmc u hu
  have hu' : min u (t i) ∈ Set.Icc (0 : ℝ) (t i) := ⟨le_min hu.1 hτ.1, min_le_right _ _⟩
  have hL : obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) u) i =
      NegSobolev.eval (zetaAt m P X (min u (t i)) ω)
        (propagator R.D R.ρ (min u (t i)) (t i) (φ i)) := by
    show NegSobolev.eval (pathAt (predicted R.D R.ρ (zetaWin m T 0 P X ω) u) (t i)) (φ i) = _
    rw [hPath _ u (t i) hu hτ]
    by_cases h : t i ≤ u
    · rw [if_pos h, S7PIF4_pathAt_zetaWin P X ω hc hτ, min_eq_right h,
        S7PIF4_prop_self R m hm T hT N hN P X₀ W X hreal hψ hτ]
    · rw [if_neg h, S7PIF4_pathAt_zetaWin P X ω hc hu, min_eq_left (not_le.1 h).le]
      exact HRS.MC.Sec7.S7PIS1.s7_PIS_V_eval_proof R m hm T hT u (t i) hu.1 (not_le.1 h).le hτ.2 _ _ hψ
  have hM : empiricalMartingale P ℱ W' R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X u ω =
      empiricalMartingale P ℱ W' R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X (min u (t i)) ω :=
    hmc u hu.1
  rw [hL, S7PIF4_obsTest_integral, hM]
  exact hk _ hu'

end Prob

end HRS.MC.Sec7.S7PIF4

end
