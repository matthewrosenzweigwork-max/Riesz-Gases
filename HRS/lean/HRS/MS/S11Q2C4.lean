import HRS.MS.S11Q2C1
import HRS.Whole.Dynamics

/-!
# S11.3 Liouville (worker S11Q2), C4: a surviving path solves the cut-off equation

Deterministic: for a continuous path `X` satisfying the integrated SDE with the continuous noise path `W` up to time `T`, and `X_r ∈ D` for
`r ≤ t ≤ T`, the pair `(y, c) = (X ∘ toNNReal, σ W ∘ toNNReal)` satisfies the hypotheses `s11q2_Sol` of the Euler analysis with the
cut-off drift `b~` of C3.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set intervalIntegral
open scoped ENNReal NNReal

namespace HRS.MS.S11Q2

open HRS HRS.Whole

theorem s11q2_path_sol {d N : ℕ} (Dyn : WholeDyn d) {D : Set (EucConfig d N)} {bt : EucConfig d N → EucConfig d N}
    {L M : ℝ} (hL0 : 0 ≤ L) (hM0 : 0 ≤ M) (hL : ∀ x y, ‖bt x - bt y‖ ≤ L * ‖x - y‖) (hM : ∀ x, ‖bt x‖ ≤ M)
    (hbc : Continuous bt) (hbD : ∀ x ∈ closure D, bt x = particleDriftW Dyn x)
    {Xp Wp : ℝ≥0 → EucConfig d N} (hXc : Continuous Xp) (hWc : Continuous Wp) {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (heqn : ∀ t' : ℝ≥0, (t' : ℝ) ≤ T → (∀ i, IntegrableOn (fun s : ℝ => particleDriftW Dyn (Xp (Real.toNNReal s)) i) (Icc 0 (t' : ℝ))) ∧
      ∀ i, Xp t' i = Xp 0 i + (∫ s in Icc (0 : ℝ) t', particleDriftW Dyn (Xp (Real.toNNReal s)) i) +
        Real.sqrt (2 * Dyn.invβ) • (Wp t' i - Wp 0 i))
    (hsurv : ∀ r : ℝ≥0, r ≤ t.toNNReal → Xp r ∈ D) :
    s11q2_Sol bt L M t (fun s => Xp s.toNNReal) (fun s => Real.sqrt (2 * Dyn.invβ) • Wp s.toNNReal) := by
  have hyc : Continuous fun s : ℝ => Xp s.toNNReal := hXc.comp continuous_real_toNNReal
  refine ⟨hL0, hM0, hL, hM, hbc, hyc.continuousOn, ((hWc.comp continuous_real_toNNReal).const_smul (Real.sqrt (2 * Dyn.invβ)) : Continuous fun s : ℝ => Real.sqrt (2 * Dyn.invβ) • Wp s.toNNReal).continuousOn, ?_⟩
  intro s hs
  have hsT : (s.toNNReal : ℝ) ≤ T := by rw [Real.coe_toNNReal _ hs.1]; exact hs.2.trans ht.2
  obtain ⟨hint, heq⟩ := heqn s.toNNReal hsT
  have hbtint : IntervalIntegrable (fun r => bt (Xp r.toNNReal)) volume 0 s :=
    (hbc.comp hyc).intervalIntegrable _ _
  refine funext fun i => ?_
  have h1 := heq i
  have hcongr : ∫ r in Icc (0 : ℝ) (s.toNNReal : ℝ), particleDriftW Dyn (Xp r.toNNReal) i =
      ∫ r in Icc (0 : ℝ) s, bt (Xp r.toNNReal) i := by
    rw [Real.coe_toNNReal _ hs.1]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrt : r.toNNReal ≤ t.toNNReal := Real.toNNReal_le_toNNReal (hr.2.trans hs.2)
    rw [hbD _ (subset_closure (hsurv _ hrt))]
  have h2 : (∫ r in (0 : ℝ)..s, bt (Xp r.toNNReal)) i = ∫ r in Icc (0 : ℝ) s, bt (Xp r.toNNReal) i := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).intervalIntegral_comp_comm hbtint
    simp only [ContinuousLinearMap.proj_apply] at this
    rw [← this, intervalIntegral.integral_of_le hs.1, integral_Icc_eq_integral_Ioc]
  have h3 : Xp s.toNNReal i = Xp 0 i + (∫ r in (0 : ℝ)..s, bt (Xp r.toNNReal)) i +
      Real.sqrt (2 * Dyn.invβ) • (Wp s.toNNReal i - Wp 0 i) := by
    rw [h2, ← hcongr]; exact h1
  simp only [Real.toNNReal_zero] at h3 ⊢
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [h3]
  simp only [smul_sub]

end HRS.MS.S11Q2

end
