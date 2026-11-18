import HRS.MS.SA16E1Det
import HRS.MS.SA16E1Defs

/-!
# S.A.16 E1: reduction of `charFlow` to the flow of the translated drift

For a continuous path `w`, `a t = ∑ w_i(t) √(2ν) e_i`, `Y_t = charFlow t - a t` solves `Y' = -b̃(t,Y)` with
`b̃(t,y) = b(t, y + a t)`, which satisfies `IsDriftBounds` (path-dependent growth constant) with the
path-independent derivative bound `B`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.Whole.AppendixALemmas

/-- The noise directions. -/
def e1Sig (d : ℕ) (ν : ℝ) : Fin d → Euc d :=
  fun i => Real.sqrt (2*ν) • EuclideanSpace.single i (1 : ℝ)

/-- The additive noise path. -/
def e1a (d : ℕ) (ν : ℝ) (w : ℝ≥0 → Fin d → ℝ) : ℝ → Euc d := HRS.addNoise (e1Sig d ν) w

/-- The translated drift. -/
def e1bt (d : ℕ) (ν : ℝ) (w : ℝ≥0 → Fin d → ℝ) (b : ℝ → Euc d → Euc d) : ℝ → Euc d → Euc d :=
  fun τ y => b τ (y + e1a d ν w τ)

theorem e1_charFlow_def (d : ℕ) (b : ℝ → Euc d → Euc d) (ν : ℝ) (w : ℝ≥0 → Fin d → ℝ) (t : ℝ)
    (x : Euc d) : charFlow d b ν w t x =
      HRS.picardLim (fun r y => -b r y) (e1Sig d ν) w x t := rfl

theorem e1_B_nonneg {d k : ℕ} {B : ℝ} {b : ℝ → Euc d → Euc d} (hb : DriftBounds d k B b) :
    0 ≤ B :=
  (norm_nonneg _).trans (hb.2 0 le_rfl).2.1

theorem e1_lipB {d k : ℕ} (hk : 1 ≤ k) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d k B b) {τ : ℝ} (hτ : 0 ≤ τ) (x y : Euc d) :
    ‖b τ x - b τ y‖ ≤ B * ‖x - y‖ := by
  have hd : Differentiable ℝ (b τ) :=
    (hb.2 τ hτ).1.differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk)
  exact (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := b τ) (C := B) (fun x _ => hd x)
    (fun x _ => by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact (hb.2 τ hτ).2.2 1 le_rfl hk x) (mem_univ y) (mem_univ x)

theorem e1_isLip {d k : ℕ} (hk : 1 ≤ k) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d k B b) : IsLipschitzDrift (fun r y => -b r y) where
  cont := by
    have := hb.1.neg
    exact this
  lip T := ⟨B.toNNReal, fun t ht => by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (e1_B_nonneg hb),
      show -b t x - -b t y = -(b t x - b t y) by abel, norm_neg]
    exact e1_lipB hk hb ht.1 x y⟩

theorem e1_a_zero (d : ℕ) (ν : ℝ) (w : ℝ≥0 → Fin d → ℝ) (hw0 : w 0 = 0) : e1a d ν w 0 = 0 := by
  simp [e1a, HRS.addNoise, hw0]

theorem e1_a_cont (d : ℕ) (ν : ℝ) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) :
    Continuous (e1a d ν w) := HRS.continuous_addNoise _ hw

theorem e1_flow_eq {d k : ℕ} (hk : 1 ≤ k) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d k B b) (ν : ℝ) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (x : Euc d)
    {t : ℝ} (ht : 0 ≤ t) :
    charFlow d b ν w t x = x - (∫ s in (0:ℝ)..t, b s (charFlow d b ν w s x)) + e1a d ν w t := by
  have h := HRS.picardLim_eq (fun r y => -b r y) (e1_isLip hk hb) (e1Sig d ν) hw x t
  rw [max_eq_left ht] at h
  have hc : ∫ s in (0:ℝ)..t, -b (max s 0) (HRS.picardLim (fun r y => -b r y) (e1Sig d ν) w x s) =
      -∫ s in (0:ℝ)..t, b s (charFlow d b ν w s x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht] at hs
    simp only [max_eq_left hs.1]
    rfl
  rw [hc] at h
  rw [e1_charFlow_def]
  rw [h]
  simp only [e1a, sub_eq_add_neg]

theorem e1_flow_cont {d k : ℕ} (hk : 1 ≤ k) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d k B b) (ν : ℝ) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (x : Euc d) :
    Continuous (fun t => charFlow d b ν w t x) :=
  HRS.continuous_picardLim _ (e1_isLip hk hb) _ hw x

theorem e1_integrand_cont {d k : ℕ} (hk : 1 ≤ k) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d k B b) (ν : ℝ) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (x : Euc d) :
    Continuous (fun s => b (max s 0) (charFlow d b ν w (max s 0) x)) := by
  have h1 : Continuous (fun s : ℝ => (max s 0, charFlow d b ν w (max s 0) x)) :=
    (continuous_id.max continuous_const).prodMk
      ((e1_flow_cont hk hb ν hw x).comp (continuous_id.max continuous_const))
  have := hb.1.comp_continuous h1 (fun s => ⟨show (0:ℝ) ≤ max s 0 from le_max_right _ _, trivial⟩)
  exact this

end HRS.Whole.AppendixA.Phase2SA16Evolution
