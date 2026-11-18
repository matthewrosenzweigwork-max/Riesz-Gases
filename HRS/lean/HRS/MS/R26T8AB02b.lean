import HRS.MS.R26T8AB02a
import HRS.MS.R26T8AB01b

/-!
# S8.2 T8A B02b: age fundamental theorem of calculus for the drift field `V = D - Q'`

At a collision-free configuration `x`, `u ↦ VAge 0 u x` is an age primitive of `u ↦ VAge 1 u x` (continuous on `u ≥ 0`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 6400000 in
theorem r26t8a_b02_ftc (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d)
    (x : EucConfig d N) (hx : x ∉ eucCollisionSet d N) (s0 T : ℝ) (hs0 : 0 ≤ s0) :
    ContinuousOn (fun t : ℝ => r26t8a_VAge a beta m rho Psi alpha 1 (s0 + t) x) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T, r26t8a_VAge a beta m rho Psi alpha 0 (s0 + t) x =
      r26t8a_VAge a beta m rho Psi alpha 0 (s0 + 0) x +
        ∫ s in Set.Icc 0 t, r26t8a_VAge a beta m rho Psi alpha 1 (s0 + s) x := by
  obtain ⟨-, -, hDc1, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha 1 le_rfl
  obtain ⟨-, -, -, hDd0⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha 0 (by norm_num)
  obtain ⟨-, hQd1, -, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha 1 le_rfl
  have hQ2 := r26t8a_b02_QAge_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 2
    (by norm_num)
  let L0 : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => EucConfig d N) ℝ →L[ℝ] ℝ :=
    (continuousMultilinearCurryFin0 ℝ (EucConfig d N) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hL0 : ∀ (g : EucConfig d N → ℝ) (y : EucConfig d N), L0 (iteratedFDeriv ℝ 0 g y) = g y := by
    intro g y
    simp [L0, iteratedFDeriv_zero_eq_comp]
  have hder : ∀ v : ℝ, 0 ≤ v → HasDerivWithinAt (fun u => r26t8a_VAge a beta m rho Psi alpha 0 u x)
      (r26t8a_VAge a beta m rho Psi alpha 1 v x) (Set.Ici 0) v := by
    intro v hv
    have hD := hDd0 x hx v hv
    have h0 := hQd1 x hx v hv 0 (by norm_num)
    have h1 := L0.hasFDerivAt.comp_hasDerivWithinAt v h0
    simp only [hL0] at h1
    exact hD.sub h1
  have hcont1 : ContinuousOn (fun t : ℝ => r26t8a_VAge a beta m rho Psi alpha 1 (s0 + t) x) (Set.Icc 0 T) := by
    have hpath : ContinuousOn (fun t : ℝ => (s0 + t, x)) (Set.Icc 0 T) :=
      (continuous_const.add continuous_id).prodMk continuous_const |>.continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => (s0 + t, x)) (Set.Icc 0 T) (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) :=
      fun t ht => ⟨by simp only [Set.mem_Ici]; linarith [ht.1], hx⟩
    have hD := ContinuousOn.comp (g := fun p : ℝ × EucConfig d N => r26t8a_DAge a beta m rho Psi alpha 1 p.1 p.2)
      (f := fun t : ℝ => (s0 + t, x)) hDc1 hpath hmaps
    have hQ := ContinuousOn.comp (g := fun p : ℝ × EucConfig d N => r26t8a_QAge a beta m rho Psi alpha 2 p.1 p.2)
      (f := fun t : ℝ => (s0 + t, x)) hQ2 hpath hmaps
    exact hD.sub hQ
  refine ⟨hcont1, fun t ht => ?_⟩
  have hlin : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt (fun u : ℝ => r26t8a_VAge a beta m rho Psi alpha 0 (s0 + u) x)
      (r26t8a_VAge a beta m rho Psi alpha 1 (s0 + s) x) (Set.Ici 0) s := by
    intro s hs
    have hl : HasDerivWithinAt (fun u : ℝ => s0 + u) 1 (Set.Ici 0) s := ((hasDerivAt_id s).const_add s0).hasDerivWithinAt
    have h2 := (hder (s0 + s) (by linarith)).scomp s hl (fun u hu => by simp only [Set.mem_Ici] at *; linarith)
    have e : (1 : ℝ) • r26t8a_VAge a beta m rho Psi alpha 1 (s0 + s) x =
        r26t8a_VAge a beta m rho Psi alpha 1 (s0 + s) x := one_smul _ _
    rw [e] at h2
    exact h2
  have hcontφ : ContinuousOn (fun u : ℝ => r26t8a_VAge a beta m rho Psi alpha 0 (s0 + u) x) (Set.Icc 0 t) :=
    fun u hu => ((hlin u hu.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  have hint : IntervalIntegrable (fun u : ℝ => r26t8a_VAge a beta m rho Psi alpha 1 (s0 + u) x) volume 0 t :=
    (hcont1.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcontφ
    (fun u hu => (hlin u hu.1.le).mono (fun y hy => Set.mem_Ici.2 (le_trans hu.1.le (le_of_lt hy)))) hint
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1, hftc]
  ring

end HRS.MS.R26T8A

end
