import HRS.MS.TransOpAux20
import HRS.Whole.Q34Aux2

/-!
# S611 packet P3a: the path operator `S_a z (t) = Λ_{γ(a+t)} z(t)` on `C([0,T]; B_m)` and window conjugation
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- The path `t ↦ Λ_{γ(a+t)} z(t)`. -/
def s611_pathFun (m : ℕ) (hm : 1 ≤ m) (γ : ℝ → Euc d) (hγ : Continuous γ) (a T : ℝ)
    (z : C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ))) : C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ)) where
  toFun t := s611_Lam m hm (γ (a + t)) (z t)
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    exact s611_Lam_tendsto m hm
      ((hγ.comp (continuous_const.add continuous_subtype_val)).tendsto t₀) (z.continuous.tendsto t₀)

/-- The path operator as a bounded linear map, for a shift path with `K(γ(a+t)) ≤ Kb` on `[0,T]`. -/
def s611_pathOp (m : ℕ) (hm : 1 ≤ m) (γ : ℝ → Euc d) (hγ : Continuous γ) (a T Kb : ℝ)
    (hKb : 0 ≤ Kb) (hK : ∀ t ∈ Set.Icc (0 : ℝ) T, s611_K m (γ (a + t)) ≤ Kb) :
    C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ)) →L[ℝ] C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ)) :=
  LinearMap.mkContinuous
    { toFun := s611_pathFun m hm γ hγ a T
      map_add' := fun z w => by
        ext t; simp [s611_pathFun]
      map_smul' := fun c z => by
        ext t; simp [s611_pathFun] }
    Kb (fun z => by
      refine (ContinuousMap.norm_le _ (mul_nonneg hKb (norm_nonneg _))).2 fun t => ?_
      show ‖s611_Lam m hm (γ (a + t)) (z t)‖ ≤ Kb * ‖z‖
      calc ‖s611_Lam m hm (γ (a + t)) (z t)‖ ≤ s611_K m (γ (a + t)) * ‖z t‖ :=
            ((s611_Lam m hm (γ (a + t))).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (s611_norm_Lam_le m hm _) (norm_nonneg _))
        _ ≤ Kb * ‖z‖ := mul_le_mul (hK t t.2) (ContinuousMap.norm_coe_le_norm z t) (norm_nonneg _) hKb)

theorem s611_pathOp_apply (m : ℕ) (hm : 1 ≤ m) (γ : ℝ → Euc d) (hγ : Continuous γ) (a T Kb : ℝ)
    (hKb : 0 ≤ Kb) (hK : ∀ t ∈ Set.Icc (0 : ℝ) T, s611_K m (γ (a + t)) ≤ Kb)
    (z : C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ))) (t : Set.Icc (0 : ℝ) T) :
    s611_pathOp m hm γ hγ a T Kb hKb hK z t = s611_Lam m hm (γ (a + t)) (z t) := rfl

theorem s611_windowPathOf_pos {m T a : ℝ} (f : ℝ → OscDual d m)
    (h : Continuous fun t : Set.Icc (0 : ℝ) T => f (a + t)) :
    windowPathOf m T a f = (⟨fun t => f (a + t), h⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
  unfold windowPathOf
  exact dif_pos h

theorem s611_windowPathOf_neg {m T a : ℝ} (f : ℝ → OscDual d m)
    (h : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => f (a + t)) :
    windowPathOf m T a f = 0 := by
  unfold windowPathOf
  exact dif_neg h

/-- Window conjugation: if `fX t = Λ_{γ t} (fY t)` for `t ≥ 0` and `a ≥ 0`, then `windowPathOf fX = S_a (windowPathOf fY)`. -/
theorem s611_window_conj (m : ℕ) (hm : 1 ≤ m) (γ : ℝ → Euc d) (hγ : Continuous γ) (a T Kb : ℝ)
    (ha : 0 ≤ a) (hKb : 0 ≤ Kb) (hK : ∀ t ∈ Set.Icc (0 : ℝ) T, s611_K m (γ (a + t)) ≤ Kb)
    (fX fY : ℝ → OscDual d (m : ℝ)) (h : ∀ t : ℝ, 0 ≤ t → fX t = s611_Lam m hm (γ t) (fY t)) :
    windowPathOf (m : ℝ) T a fX =
      s611_pathOp m hm γ hγ a T Kb hKb hK (windowPathOf (m : ℝ) T a fY) := by
  have hX : ∀ t : Set.Icc (0 : ℝ) T, fX (a + t) = s611_Lam m hm (γ (a + t)) (fY (a + t)) :=
    fun t => h _ (add_nonneg ha t.2.1)
  by_cases hY : Continuous fun t : Set.Icc (0 : ℝ) T => fY (a + t)
  · have hXc : Continuous fun t : Set.Icc (0 : ℝ) T => fX (a + t) := by
      have : (fun t : Set.Icc (0 : ℝ) T => fX (a + t)) =
          fun t : Set.Icc (0 : ℝ) T => s611_Lam m hm (γ (a + t)) (fY (a + t)) := funext hX
      rw [this]
      refine continuous_iff_continuousAt.2 fun t₀ => ?_
      exact s611_Lam_tendsto m hm
        ((hγ.comp (continuous_const.add continuous_subtype_val)).tendsto t₀) (hY.tendsto t₀)
    rw [s611_windowPathOf_pos fX hXc, s611_windowPathOf_pos fY hY]
    show (⟨fun t => fX (a + t), hXc⟩ : C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ))) =
      s611_pathOp m hm γ hγ a T Kb hKb hK (⟨fun t => fY (a + t), hY⟩ : C(Set.Icc (0 : ℝ) T, OscDual d (m : ℝ)))
    exact ContinuousMap.ext fun t => hX t
  · have hXc : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => fX (a + t) := by
      intro hXc
      apply hY
      have : (fun t : Set.Icc (0 : ℝ) T => fY (a + t)) =
          fun t : Set.Icc (0 : ℝ) T => s611_Lam m hm (-(γ (a + t))) (fX (a + t)) := by
        funext t
        rw [hX t, s611_Lam_neg]
      rw [this]
      refine continuous_iff_continuousAt.2 fun t₀ => ?_
      exact s611_Lam_tendsto m hm
        (((hγ.comp (continuous_const.add continuous_subtype_val)).neg).tendsto t₀) (hXc.tendsto t₀)
    rw [s611_windowPathOf_neg fX hXc, s611_windowPathOf_neg fY hY]
    exact (map_zero _).symm

theorem s611_measurable_shift {N : ℕ} (c : Euc d) :
    Measurable (fun Z : EucConfig d N => fun i => Z i + c) := by
  fun_prop

theorem s611_empirical_shift {N : ℕ} (Y : EucConfig d N) (c : Euc d) :
    (HRS.Whole.empirical Y).map (fun x => x + c) = HRS.Whole.empirical (fun i => Y i + c) := by
  ext A hA
  rw [Measure.map_apply (measurable_add_const c) hA]
  simp only [HRS.Whole.empirical, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    Measure.dirac_apply' _ hA, Measure.dirac_apply' _ ((measurable_add_const c) hA), smul_eq_mul]
  congr 1

theorem s611_meanEmpirical_shift {N : ℕ} (Q : Measure (EucConfig d N)) (c : Euc d) :
    HRS.Whole.meanEmpirical (Q.map (fun Z : EucConfig d N => fun i => Z i + c)) =
      (HRS.Whole.meanEmpirical Q).map (fun x => x + c) := by
  have hF : Measurable (fun Z : EucConfig d N => fun i => Z i + c) := s611_measurable_shift c
  ext A hA
  rw [HRS.Whole.meanEmpirical_apply _ hA, Measure.map_apply (measurable_add_const c) hA,
    HRS.Whole.meanEmpirical_apply _ ((measurable_add_const c) hA)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply hF (show MeasurableSet {X : EucConfig d N | X i ∈ A} from measurable_pi_apply i hA)]
  rfl

/-- The exact field transformation for the mean-field centered fluctuation. -/
theorem s611_fluc_shift (m : ℕ) (hm : 1 ≤ m) (hdm : (d : ℝ) < m) {N : ℕ} (hN : 1 ≤ N) (σ : ℝ)
    (Y : EucConfig d N) (ρβ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρβ) (c : Euc d) :
    σ • OscDual.ofMeasureDiff (m : ℝ) (HRS.Whole.empirical (fun i => Y i + c))
        (HRS.Whole.withDensityReal (fun x => ρβ (x - c))) =
      s611_Lam m hm c (σ • OscDual.ofMeasureDiff (m : ℝ) (HRS.Whole.empirical Y) (HRS.Whole.withDensityReal ρβ)) := by
  haveI : IsProbabilityMeasure (HRS.Whole.empirical Y) := HRS.Whole.empirical_isProbabilityMeasure hN Y
  haveI : IsFiniteMeasure (HRS.Whole.withDensityReal ρβ) := by
    haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    infer_instance
  rw [map_smul, s611_Lam_ofMeasureDiff m hm hdm c, s611_empirical_shift, HRS.MS.A0.a0_map_withDensity]

theorem s611_zeta_shift (m : ℕ) (hm : 1 ≤ m) (hdm : (d : ℝ) < m) {N : ℕ} (hN : 1 ≤ N)
    (Q : Measure (EucConfig d N)) [IsProbabilityMeasure Q] (Y : EucConfig d N) (c : Euc d) :
    HRS.Whole.zetaB (m : ℝ) (Q.map (fun Z : EucConfig d N => fun i => Z i + c)) (fun i => Y i + c) =
      s611_Lam m hm c (HRS.Whole.zetaB (m : ℝ) Q Y) := by
  haveI : IsProbabilityMeasure (HRS.Whole.empirical Y) := HRS.Whole.empirical_isProbabilityMeasure hN Y
  haveI : IsProbabilityMeasure (HRS.Whole.meanEmpirical Q) := HRS.Whole.meanEmpirical_isProbabilityMeasure Q hN
  unfold HRS.Whole.zetaB
  rw [map_smul, s611_Lam_ofMeasureDiff m hm hdm c, s611_empirical_shift, s611_meanEmpirical_shift]

end HRS.MS.TransOp

end
