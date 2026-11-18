import HRS.MS.Fp81S21GaussianConditioningPhysicalJ2
import HRS.MS.Fp81S21GaussianConditioningMesh
import HRS.MS.Fp81S21RSSumDomination

/-! Packet 36J: the physical covariance conditioning identity, including both
integrabilities. Uniform right-endpoint sums are dominated by the variation
norm of the retained history's BV transport. The factor one half is applied only after passing expectations.
The proposed Rad/Physical35/GRS shorthand is expanded to the compiled names;
there is no added mathematical hypothesis or changed quantifier order. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_J36_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2

/-- The exact J36 clause for the supplied GRS record. -/
def fp81s21_J36 {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {Q : fp81s21_Physical35 p R}
    {future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)}
    {a : ℝ} {ha : 0 ≤ a} {Φ : Window p → ℝ} (C : fp81s21_GRS Q future a ha Φ) : Prop :=
  Integrable (C.WG.covariance.value 0 (a + p.T)) Q.src.G0.P ∧
  Integrable (fun ω =>
    (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω : TensorDual (Window p) 2)
      (iteratedFDeriv ℝ 2 Φ (r26t3_Zpath Q.src.G0 a ω))) Q.src.G0.P ∧
  ((1 / 2 : ℝ) * (∫ ω, C.WG.covariance.value 0 (a + p.T) ω ∂Q.src.G0.P) =
    (1 / 2 : ℝ) * (∫ ω,
      (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω : TensorDual (Window p) 2)
        (iteratedFDeriv ℝ 2 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P))

/-- Physical covariance conditioning for every retained package, compatible supplied
future and supplied GRS record, with one radius before all consumer variables. -/
theorem fp81s21_gaussian_conditioning_physical_J (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∀ future, fp81s21_moving_heat_full_clause p R future →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∀ C : fp81s21_GRS Q future a ha Φ, fp81s21_J36 C) := by
  obtain ⟨δ₀, hδ₀, hhalf, hcell⟩ := fp81s21_gaussian_conditioning_physical_J_cell p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q future hf a ha Φ hΦ C
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  let H := a + p.T
  have hH : 0 ≤ H := add_nonneg ha p.hT.le
  let Y := fp81s21_remote_G_extend Q.src.G0 a ha C.Y
  let A := fun ω t => fp81s21_covariance_pairingCLM
    (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ t) (Y ω t))
  let F := fun ω t => fp81s21_gaussian_Jcum (Q.OJ a ha) hH (Q.UG a ha) t ω
  let L := fun ω => fp81s21_covariance_pairingCLM
    (iteratedFDeriv ℝ 2 Φ (r26t3_Zpath Q.src.G0 a ω))
  let J := fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a
  let T := fp81s21_timeL2L1 H hH
  let LJ := (fp81s21_covarianceBV (Q.OJ a ha) hH (le_refl 0) hH le_rfl
    (by simp [H]) Q.hKJ Q.hcJ.le).comp T
  have hFL : ∀ ω t, t ∈ Icc 0 H → F ω t = fp81s21_bvExt hH (LJ (Q.UG a ha ω)) t := by
    intro ω t ht
    rw [fp81s21_bvExt_apply hH (LJ (Q.UG a ha ω)) ⟨t, ht⟩,
      ← fp81s21_bvPath_apply hH]
    change (Q.OJ a ha).covariance 0 t (T (Q.UG a ha ω)) =
      fp81s21_bvPath hH
        (fp81s21_covarianceBV (Q.OJ a ha) hH (le_refl 0) hH le_rfl
          (by simp [H]) Q.hKJ Q.hcJ.le (T (Q.UG a ha ω))) ⟨t, ht⟩
    rw [fp81s21_covarianceBV_apply]
    simp only [zero_add, min_eq_left ht.2]
  have hAb : ∀ ω t, ‖A ω t‖ ≤ 1 := fun ω t =>
    (fp81s21_covariance_pairingCLM_norm_le _).trans
      ((fp81s21_J36_derivative_bounds future hf.1 a ha Φ hΦ).2 t (Y ω t))
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
    simp only [F, fp81s21_gaussian_Jcum, (Q.OJ a ha).covariance_zero,
      ContinuousLinearMap.zero_apply]
  have hend : ∀ᵐ ω ∂Q.src.G0.P, F ω H = J ω := by
    apply ae_of_all
    intro ω
    simp only [J, fp81s21_physical35_J, dif_pos ha]
    rfl
  obtain ⟨hV, hsum_bound⟩ := fp81s21_rs_sum_transport_domination Q.src.G0.P H hH
    1 zero_le_one (Q.UG a ha) ((Q.hUG a ha).2.1.integrable one_le_two) LJ A F
    (ae_of_all _ hFL) hAb fp81s21_meshN (fp81s21_meshPoint H) ht0 htN htmono
  have he := fp81s21_conditioned_rs_expectation_limit Q.src.G0.P H hH A F C.WG.covariance L J
    fp81s21_meshN (fp81s21_meshPoint H) (fp81s21_meshWidth H)
    ht0 htN htmono htmesh hmesh hzero hend hcond huncond
    (fun n i hi => (hc n i hi).2.2)
    (fun ω => 1 * ‖LJ‖ * ‖Q.UG a ha ω‖) hV
    (fun n => (integrable_finset_sum _
      (fun i hi => hcond n i (Finset.mem_range.mp hi))).aestronglyMeasurable)
    hsum_bound (fp81s21_uniform_window_rs_limit Q.src.G0.P H hH A F C.WG.covariance)
  exact ⟨he.1, he.2.1, congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) he.2.2⟩

#print axioms fp81s21_gaussian_conditioning_physical_J
end HRS.Fp81.S21
end
