import HRS.MS.MfeConfAux89

/-!
# S.B.1, packet F8 (part 22): the constant `κ_s = θ log K̄_s + (N/2) c̄_s`, its derivative `κ'_s` and their regularity

`sb1_lv_cdot s = ċ_s`, `sb1_lv_Kdot s = K̇_s` along the clamped trajectory: continuous and bounded by constants independent of `s`.
`sb1_lv_kappa`, `sb1_lv_kappa'`: `κ` is continuous and bounded, `κ'` is continuous and bounded, and `κ` has derivative `κ'` on `(0,T)`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

def sb1_lv_cdot (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) : ℝ :=
  sb1cdot D ρ k (sb1_lv_cl' hT s)

def sb1_lv_Kdot (D : Whole.WholeDyn d) (k : Euc d → ℝ) (β : ℝ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ)
    (s : ℝ) : ℝ := ∫ X : Whole.EucConfig d N, sb1Wdot D ρ k β N (sb1_lv_cl' hT s) X

def sb1_lv_kappa (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) : ℝ :=
  D.invβ * Real.log (sb1_lv_Kb k D.invβ⁻¹ N hT ρ s) + ((N : ℝ) / 2) * sb1_lv_cb k hT ρ s

def sb1_lv_kappa' (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) : ℝ :=
  D.invβ * (sb1_lv_Kdot D k D.invβ⁻¹ N hT ρ s / sb1_lv_Kb k D.invβ⁻¹ N hT ρ s) + ((N : ℝ) / 2) * sb1_lv_cdot D k hT ρ s

theorem sb1_lv_curry_x {F : ℝ → Euc d → ℝ} (h : Continuous (Function.uncurry F)) (s : ℝ) : Continuous (F s) :=
  h.comp (Continuous.prodMk_right s)

theorem sb1_lv_curry_s {F : ℝ → Euc d → ℝ} (h : Continuous (Function.uncurry F)) (x : Euc d) :
    Continuous (fun s => F s x) := h.comp (Continuous.prodMk_left x)

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_lv_cdot_eq (s : ℝ) : sb1_lv_cdot D k hT ρ s =
    ∫ x, (sb1At D hT ρ s x * sb1G k (sb1_lv_rb hT ρ s) x + sb1_lv_rb hT ρ s x * sb1_lv_cv k (sb1At D hT ρ s) x) := rfl

set_option maxHeartbeats 1600000 in
theorem sb1_lv_cdot_cont (hk4 : IsP4Kernel d D.s r₀ k) : Continuous (sb1_lv_cdot D k hT ρ) := by
  obtain ⟨A, hA⟩ := sb1_lv_gr_k hk4 H.tr.hs0
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  have hd := H.tr.hd
  have hw1 := sb1w_int hd (p := (d : ℝ) + 1) (by linarith)
  have hG := sb1_lv_G_cont H hT hA hk4.smooth.continuous
  have hGd := sb1_lv_Gd_cont H hT hA hk4.smooth.continuous
  have e : sb1_lv_cdot D k hT ρ = fun s => ∫ x, (sb1At D hT ρ s x * sb1G k (sb1_lv_rb hT ρ s) x +
      sb1_lv_rb hT ρ s x * sb1_lv_cv k (sb1At D hT ρ s) x) := funext fun s => sb1_lv_cdot_eq H hT s
  rw [e]
  refine continuous_of_dominated (bound := fun x => (sb1CA D B C C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) +
      C3 * sb1CGd d D.s (sb1CA D B C C3)) * sb1w ((d : ℝ) + 1) x) (fun s => ?_) (fun s => ?_) (hw1.const_mul _) ?_
  · have h1 := sb1_lv_curry_x (F := fun s x => sb1At D hT ρ s x) (sb1At_cont H.tr hT) s
    have h2 := sb1_lv_curry_x (F := fun s x => sb1G k (sb1_lv_rb hT ρ s) x) hG s
    have h3 := sb1_lv_curry_x (F := fun s x => sb1_lv_rb hT ρ s x) (sb1_lv_rb_cont H hT) s
    have h4 := sb1_lv_curry_x (F := fun s x => sb1_lv_cv k (sb1At D hT ρ s) x) hGd s
    exact ((h1.mul h2).add (h3.mul h4)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have hr := sb1_lv_cl'_mem hT s
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    have h1 := sb1_AG_pt H hk hr x
    have h2 := sb1_rhoGd_pt H hk hr x
    have e1 : sb1At D hT ρ s x = sb1A D (ρ (sb1_lv_cl' hT s)) x := rfl
    have e2 : sb1_lv_rb hT ρ s x = ρ (sb1_lv_cl' hT s) x := rfl
    have e3 : sb1_lv_cv k (sb1At D hT ρ s) x = sb1Gd D ρ k (sb1_lv_cl' hT s) x := rfl
    have e4 : sb1G k (sb1_lv_rb hT ρ s) x = sb1G k (ρ (sb1_lv_cl' hT s)) x := rfl
    rw [e1, e2, e3, e4]
    nlinarith
  · refine Eventually.of_forall fun x => ?_
    have h1 := sb1_lv_curry_s (F := fun s x => sb1At D hT ρ s x) (sb1At_cont H.tr hT) x
    have h2 := sb1_lv_curry_s (F := fun s x => sb1G k (sb1_lv_rb hT ρ s) x) hG x
    have h3 := sb1_lv_curry_s (F := fun s x => sb1_lv_rb hT ρ s x) (sb1_lv_rb_cont H hT) x
    have h4 := sb1_lv_curry_s (F := fun s x => sb1_lv_cv k (sb1At D hT ρ s) x) hGd x
    exact (h1.mul h2).add (h3.mul h4)

theorem sb1_lv_cdot_bound (hk4 : IsP4Kernel d D.s r₀ k) (s : ℝ) :
    |sb1_lv_cdot D k hT ρ s| ≤ (sb1CA D B C C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) +
      C3 * sb1CGd d D.s (sb1CA D B C C3)) * ∫ x : Euc d, sb1w ((d : ℝ) + 1) x :=
  sb1_cdot_bound H (sb1KerU_of_p4 H.tr.hs0 hk4) (sb1_lv_cl'_mem hT s)

end Traj

end HRS.MS.MfeConf
