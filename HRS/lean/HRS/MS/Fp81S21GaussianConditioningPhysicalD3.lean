import HRS.MS.Fp81S21GaussianConditioningPhysicalD2
import HRS.MS.Fp81S21GaussianConditioningMesh
import HRS.MS.Fp81S21RSSumDomination

/-! Packet 36D: the physical drift conditioning identity, including both
integrabilities. Uniform right-endpoint sums are dominated by the variation
norm of the retained history's BV transport. The final minus signs are literal.
The proposed Rad/Physical35/GRS shorthand is expanded to the compiled names;
there is no added mathematical hypothesis or changed quantifier order. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The exact D36 clause for the supplied GRS record. -/
def fp81s21_D36 {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {Q : fp81s21_Physical35 p R}
    {future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)}
    {a : ℝ} {ha : 0 ≤ a} {Φ : Window p → ℝ} (C : fp81s21_GRS Q future a ha Φ) : Prop :=
  Integrable (C.WG.drift.value 0 (a + p.T)) Q.src.G0.P ∧
  Integrable (fun ω => fderiv ℝ Φ (r26t3_Zpath Q.src.G0 a ω)
    (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω)) Q.src.G0.P ∧
  (-(∫ ω, C.WG.drift.value 0 (a + p.T) ω ∂Q.src.G0.P) =
    -(∫ ω, fderiv ℝ Φ (r26t3_Zpath Q.src.G0 a ω)
      (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω) ∂Q.src.G0.P))

/-- Physical drift conditioning for every retained package, compatible supplied
future and supplied GRS record, with one radius before all consumer variables. -/
theorem fp81s21_gaussian_conditioning_physical_D (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∀ future, fp81s21_moving_heat_full_clause p R future →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∀ C : fp81s21_GRS Q future a ha Φ, fp81s21_D36 C) := by
  obtain ⟨δ₀, hδ₀, hhalf, hcell⟩ := fp81s21_gaussian_conditioning_physical_D_cell p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q future hf a ha Φ hΦ C
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  let H := a + p.T
  have hH : 0 ≤ H := add_nonneg ha p.hT.le
  let Y := fp81s21_remote_G_extend Q.src.G0 a ha C.Y
  let A := fun ω t => fderiv ℝ (initialHeat future a ha Φ t) (Y ω t)
  let F := fun ω t => fp81s21_gaussian_Dcum (Q.OD a ha) hH (Q.UB a ha) t ω
  let L := fun ω => fderiv ℝ Φ (r26t3_Zpath Q.src.G0 a ω)
  let D := fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a
  let T := fp81s21_timeL2L1 H hH
  let LD := (fp81s21_driftBV (Q.OD a ha) hH (le_refl 0) hH le_rfl
    (by simp [H]) Q.hKD Q.hcD.le).comp T
  have hFL : ∀ ω t, t ∈ Icc 0 H → F ω t = fp81s21_bvExt hH (LD (Q.UB a ha ω)) t := by
    intro ω t ht
    rw [fp81s21_bvExt_apply hH (LD (Q.UB a ha ω)) ⟨t, ht⟩,
      ← fp81s21_bvPath_apply hH]
    change (Q.OD a ha).drift 0 t (T (Q.UB a ha ω)) =
      fp81s21_bvPath hH
        (fp81s21_driftBV (Q.OD a ha) hH (le_refl 0) hH le_rfl
          (by simp [H]) Q.hKD Q.hcD.le (T (Q.UB a ha ω))) ⟨t, ht⟩
    rw [fp81s21_driftBV_apply]
    simp only [zero_add, min_eq_left ht.2]
  have hAb : ∀ ω t, ‖A ω t‖ ≤ 1 := fun ω t =>
    (fp81s21_D36_derivative_bounds future hf.1 a ha Φ hΦ).2 t (Y ω t)
  obtain ⟨ht0, htN, htmono, htmesh, hmesh⟩ := fp81s21_uniform_mesh H hH
  have ht (n i : ℕ) (hi : i ≤ fp81s21_meshN n) :
      fp81s21_meshPoint H n i ∈ Icc 0 H := by
    have hw : 0 ≤ H / (fp81s21_meshN n : ℝ) :=
      div_nonneg hH (Nat.cast_nonneg _)
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hw, ?_⟩
    calc
      fp81s21_meshPoint H n i ≤ fp81s21_meshPoint H n (fp81s21_meshN n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hw
      _ = H := htN n
  have hc (n i : ℕ) (hi : i < fp81s21_meshN n) :=
    hcell δ hδ hδle R Q future hf a ha Φ hΦ C
      (fp81s21_meshPoint H n i) (fp81s21_meshPoint H n (i + 1))
      (ht n i hi.le).1 (htmono n i hi) (ht n (i + 1) (by omega)).2
  have hcond (n i : ℕ) (hi : i < fp81s21_meshN n) : Integrable
      (fun ω => A ω (fp81s21_meshPoint H n (i + 1))
        (F ω (fp81s21_meshPoint H n (i + 1)) - F ω (fp81s21_meshPoint H n i))) Q.src.G0.P :=
    (hc n i hi).1
  have huncond (n i : ℕ) (hi : i < fp81s21_meshN n) : Integrable
      (fun ω => L ω
        (F ω (fp81s21_meshPoint H n (i + 1)) - F ω (fp81s21_meshPoint H n i))) Q.src.G0.P :=
    (hc n i hi).2.1
  have hzero : ∀ᵐ ω ∂Q.src.G0.P, F ω 0 = 0 := by
    apply ae_of_all
    intro ω
    simp only [F, fp81s21_gaussian_Dcum, (Q.OD a ha).drift_zero,
      ContinuousLinearMap.zero_apply]
  have hend : ∀ᵐ ω ∂Q.src.G0.P, F ω H = D ω := by
    apply ae_of_all
    intro ω
    simp only [D, fp81s21_physical35_D, dif_pos ha]
    rfl
  obtain ⟨hV, hsum_bound⟩ := fp81s21_rs_sum_transport_domination Q.src.G0.P H hH
    1 zero_le_one (Q.UB a ha) ((Q.hUB a ha).2.1.integrable one_le_two) LD A F
    (ae_of_all _ hFL) hAb fp81s21_meshN (fp81s21_meshPoint H) ht0 htN htmono
  have he := fp81s21_conditioned_rs_expectation_limit Q.src.G0.P H hH A F C.WG.drift L D
    fp81s21_meshN (fp81s21_meshPoint H) (fp81s21_meshWidth H)
    ht0 htN htmono htmesh hmesh hzero hend hcond huncond
    (fun n i hi => (hc n i hi).2.2)
    (fun ω => 1 * ‖LD‖ * ‖Q.UB a ha ω‖) hV
    (fun n => (integrable_finset_sum _
      (fun i hi => hcond n i (Finset.mem_range.mp hi))).aestronglyMeasurable)
    hsum_bound (fp81s21_uniform_window_rs_limit Q.src.G0.P H hH A F C.WG.drift)
  exact ⟨he.1, he.2.1, congrArg Neg.neg he.2.2⟩

#print axioms fp81s21_gaussian_conditioning_physical_D
end HRS.Fp81.S21
end
