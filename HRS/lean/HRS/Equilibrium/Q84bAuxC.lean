/-
# HRS.Equilibrium.Q84bAuxC — packet Q84b helpers (local formula for `Jop`, scalar splitting)
-/
import HRS.Equilibrium.Q84bAuxB

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

theorem q84b_conv_far_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {H : Torus d → ℝ}
    (hH : Integrable H) {a : Torus d} {r : ℝ} (hr : 0 < r)
    (hH0 : ∀ y, ‖a - y‖ < 2 * r → H y = 0) {x : Torus d} (hx : ‖x - a‖ < r) :
    Integrable (fun y => periodicRiesz d s (x - y) * H y) := by
  have hgi : Integrable (periodicRiesz d s) := HRS.PDE.MFAux.integrable_periodicRiesz hd s hs0 hsd
  obtain ⟨Mg, hMg⟩ := q84b_g_bdd hd hs0 hsd hr
  refine Integrable.mono' (hH.norm.mul_const Mg) ?_ (Eventually.of_forall fun y => ?_)
  · exact (hgi.comp_sub_left x).aestronglyMeasurable.mul hH.aestronglyMeasurable
  · by_cases hy : H y = 0
    · simp [hy]
    · have h1 : 2 * r ≤ ‖a - y‖ := by
        by_contra h; exact hy (hH0 y (not_le.1 h))
      have h2 : ‖a - y‖ ≤ ‖x - a‖ + ‖x - y‖ := by
        calc ‖a - y‖ = ‖(a - x) + (x - y)‖ := by congr 1; abel
          _ ≤ ‖a - x‖ + ‖x - y‖ := norm_add_le _ _
          _ = ‖x - a‖ + ‖x - y‖ := by rw [norm_sub_rev a x]
      have h3 : r ≤ ‖x - y‖ := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |periodicRiesz d s (x - y)| * |H y| ≤ Mg * |H y| :=
            mul_le_mul_of_nonneg_right (hMg _ h3) (abs_nonneg _)
        _ = ‖H y‖ * Mg := by rw [Real.norm_eq_abs, mul_comm]

/-- Scalar splitting: `H = H1 + H2` with `H1` of class `C¹` and `H2` integrable, vanishing near `a`. -/
theorem q84b_conv_split (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {H H1 H2 : Torus d → ℝ}
    (hH1 : Torus.IsCk 1 H1) (hH2 : Integrable H2) (hsum : ∀ y, H y = H1 y + H2 y)
    {a : Torus d} {r : ℝ} (hr : 0 < r) (hH20 : ∀ y, ‖a - y‖ < 2 * r → H2 y = 0) (j : Fin d) :
    DifferentiableAt ℝ (Torus.lift (convFun (periodicRiesz d s) H)) (Torus.rep a) ∧
    Torus.partialDeriv j (convFun (periodicRiesz d s) H) a =
      convFun (periodicRiesz d s) (Torus.partialDeriv j H1) a +
        ∫ y, H2 y * (periodicRieszGrad d s (a - y)) j := by
  have hgi : Integrable (periodicRiesz d s) := HRS.PDE.MFAux.integrable_periodicRiesz hd s hs0 hsd
  obtain ⟨hint2, hD2⟩ := q84b_conv_far hd hs0 hsd hH2 hr hH20
  have hD1 := q84b_convFun_hasFDerivAt hgi hH1 (Torus.rep a)
  have hH1c : Continuous H1 := HRS.PDE.MFAux.continuous_of_isCk hH1
  obtain ⟨B1, hB1⟩ := q84b_exists_bound_of_cont hH1c
  let U : Set (Euc d) := {u | ‖Torus.mk u - a‖ < r}
  have hUo : IsOpen U :=
    isOpen_lt (continuous_norm.comp (Q84a.q84a_continuous_mk.sub continuous_const)) continuous_const
  have hrepU : Torus.rep a ∈ U := by
    show ‖Torus.mk (Torus.rep a) - a‖ < r
    rw [Torus.mk_rep, sub_self, norm_zero]; exact hr
  have hev : Torus.lift (convFun (periodicRiesz d s) H) =ᶠ[𝓝 (Torus.rep a)]
      fun u => Torus.lift (convFun (periodicRiesz d s) H1) u +
        Torus.lift (convFun (periodicRiesz d s) H2) u := by
    filter_upwards [hUo.mem_nhds hrepU] with u hu
    have hu' : ‖Torus.mk u - a‖ < r := hu
    have i2 := q84b_conv_far_integrable hd hs0 hsd hH2 hr hH20 hu'
    have i1 : Integrable (fun y => periodicRiesz d s (Torus.mk u - y) * H1 y) :=
      (hgi.comp_sub_left (Torus.mk u)).mul_bdd (c := B1) hH1c.aestronglyMeasurable
        (Eventually.of_forall fun y => by simpa using hB1 y)
    simp only [Torus.lift, Function.comp, convFun]
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hsum y]; ring
  have hD : HasFDerivAt (Torus.lift (convFun (periodicRiesz d s) H))
      ((∫ z, periodicRiesz d s z • fderiv ℝ (Torus.lift H1) (Torus.rep a - Torus.rep z)) +
        ∫ y, H2 y • (InnerProductSpace.toDual ℝ (Euc d)
          (periodicRieszGrad d s (a - y)) : Euc d →L[ℝ] ℝ)) (Torus.rep a) :=
    (hD1.add hD2).congr_of_eventuallyEq hev
  refine ⟨hD.differentiableAt, ?_⟩
  have e0 : Torus.partialDeriv j (convFun (periodicRiesz d s) H) a =
      fderiv ℝ (Torus.lift (convFun (periodicRiesz d s) H)) (Torus.rep a) (EuclideanSpace.single j 1) :=
    rfl
  rw [e0, hD.fderiv, add_apply]
  congr 1
  · have := q84b_convFun_partialDeriv hgi hH1 j a
    rw [← this]
    have e1 : Torus.partialDeriv j (convFun (periodicRiesz d s) H1) a =
        fderiv ℝ (Torus.lift (convFun (periodicRiesz d s) H1)) (Torus.rep a)
          (EuclideanSpace.single j 1) := rfl
    rw [e1, hD1.fderiv]
  · rw [ContinuousLinearMap.integral_apply hint2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_right]

end HRS.Q84b
