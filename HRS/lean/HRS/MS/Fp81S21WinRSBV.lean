import HRS.MS.ProClosureS111WindowRestriction

/-! A contractive continuous lift for physical window restrictions. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Set

namespace HRS.Fp81.S21

open HRS HRS.Whole

/-- Clamp a full-horizon time to the physical window's time interval. -/
def fp81s21_physicalWindowExtensionTime
    {T a : ℝ} (hT : 0 ≤ T) (s : Icc (0 : ℝ) (a + T)) : Icc (0 : ℝ) T :=
  ⟨max 0 (min (s.1 - a) T), le_max_left _ _,
    max_le hT (min_le_right _ _)⟩

theorem fp81s21_physicalWindowExtensionTime_continuous
    {T a : ℝ} (hT : 0 ≤ T) :
    Continuous (fp81s21_physicalWindowExtensionTime (T := T) (a := a) hT) := by
  exact (continuous_max.comp
      (continuous_const.prodMk
        (continuous_min.comp
          ((continuous_subtype_val.sub continuous_const).prodMk continuous_const)))).subtype_mk
    (fun _ => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩)

/-- Extend a physical-window path constantly to the left of its starting
time. This is a norm-one right inverse to physical restriction. -/
def fp81s21_physicalWindowExtension
    {d : ℕ} {m T a : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    OscPath d m T →L[ℝ] OscPath d m (a + T) := by
  let θ := fp81s21_physicalWindowExtensionTime (T := T) (a := a) hT
  have hθ := fp81s21_physicalWindowExtensionTime_continuous (T := T) (a := a) hT
  let Llin : OscPath d m T →ₗ[ℝ] OscPath d m (a + T) :=
    { toFun := fun x =>
        (⟨fun s => OscPath.at' x (θ s),
          (show C(Icc (0 : ℝ) T, OscDual d m) from x).continuous.comp hθ⟩ :
          OscPath d m (a + T))
      map_add' := by
        intro x y
        apply ContinuousMap.ext
        intro s
        rfl
      map_smul' := by
        intro c x
        apply ContinuousMap.ext
        intro s
        rfl }
  exact Llin.mkContinuous 1 (by
    intro x
    simp only [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg x)).2
    intro s
    change ‖OscPath.at' (Llin x) s‖ ≤ ‖x‖
    change ‖OscPath.at' x (θ s)‖ ≤ ‖x‖
    exact ContinuousMap.norm_coe_le_norm
      (show C(Icc (0 : ℝ) T, OscDual d m) from x) (θ s))

/-- The extension map has operator norm at most one. -/
theorem fp81s21_physicalWindowExtension_norm_le
    {d : ℕ} {m T a : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    ‖fp81s21_physicalWindowExtension (d := d) (m := m) (T := T) ha hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖fp81s21_physicalWindowExtension (d := d) (m := m) (T := T) ha hT x‖ ≤ 1 * ‖x‖
  rw [one_mul]
  let θ := fp81s21_physicalWindowExtensionTime (T := T) (a := a) hT
  apply (ContinuousMap.norm_le _ (norm_nonneg x)).2
  intro s
  change ‖OscPath.at' (fp81s21_physicalWindowExtension (d := d) (m := m) (T := T) ha hT x) s‖ ≤ ‖x‖
  change ‖OscPath.at' x (θ s)‖ ≤ ‖x‖
  exact ContinuousMap.norm_coe_le_norm
    (show C(Icc (0 : ℝ) T, OscDual d m) from x) (θ s)

/-- Restriction followed by constant extension recovers every window path. -/
theorem fp81s21_physicalWindowRestriction_comp_extension
    {d : ℕ} {m T a : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    (HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := d) (m := m) (T := T) (H := a + T) ha le_rfl).comp
        (fp81s21_physicalWindowExtension (d := d) (m := m) (T := T) ha hT) =
      ContinuousLinearMap.id ℝ (OscPath d m T) := by
  ext x
  apply ContinuousMap.ext
  intro t
  change OscPath.at'
    (HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := d) (m := m) (T := T) (H := a + T) ha le_rfl
      (fp81s21_physicalWindowExtension (d := d) (m := m) (T := T) ha hT x)) t =
    OscPath.at' x t
  rw [HRS.MS.ProClosureS111.physicalWindowRestriction_apply]
  have htime : fp81s21_physicalWindowExtensionTime (T := T) (a := a) hT
      (HRS.MS.ProClosureS111.physicalWindowTime ha le_rfl t) = t := by
    apply Subtype.ext
    simp only [fp81s21_physicalWindowExtensionTime,
      HRS.MS.ProClosureS111.physicalWindowTime]
    have ht : a + (t : ℝ) - a = (t : ℝ) := by ring
    rw [ht, min_eq_left t.property.2, max_eq_right t.property.1]
  change OscPath.at' x
      (fp81s21_physicalWindowExtensionTime (T := T) (a := a) hT
        (HRS.MS.ProClosureS111.physicalWindowTime ha le_rfl t)) = OscPath.at' x t
  rw [htime]

/-- A functional on a physical window and its pullback to the full path have
the same operator norm. -/
theorem fp81s21_physicalWindow_pullback_norm_eq
    {d : ℕ} {m T a : ℝ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ha : 0 ≤ a) (hT : 0 ≤ T)
    (D : OscPath d m T →L[ℝ] F) :
    ‖D‖ = ‖D.comp (HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := d) (m := m) (T := T) (H := a + T) ha le_rfl)‖ := by
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := d) (m := m) (T := T) (H := a + T) ha le_rfl
  let L := fp81s21_physicalWindowExtension (d := d) (m := m) (T := T) ha hT
  change ‖D‖ = ‖D.comp W‖
  have hWL : W.comp L = ContinuousLinearMap.id ℝ (OscPath d m T) :=
    fp81s21_physicalWindowRestriction_comp_extension ha hT
  have hW : ‖W‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖W x‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact HRS.MS.ProClosureS111.physicalWindowRestriction_norm_le ha le_rfl x
  have hL := fp81s21_physicalWindowExtension_norm_le (d := d) (m := m) ha hT
  have hD : D = (D.comp W).comp L := by
    ext x
    change D x = D (W (L x))
    have hx := congrArg (fun G => G x) hWL
    change W (L x) = x at hx
    exact (congrArg D hx).symm
  have hDnorm : ‖D‖ = ‖(D.comp W).comp L‖ :=
    congrArg (fun K : OscPath d m T →L[ℝ] F => ‖K‖) hD
  have h1 : ‖D‖ ≤ ‖D.comp W‖ := by
    calc
      ‖D‖ = ‖(D.comp W).comp L‖ := hDnorm
      _ ≤ ‖D.comp W‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖D.comp W‖ := by
        exact mul_le_of_le_one_right (norm_nonneg _) hL
  have h2 : ‖D.comp W‖ ≤ ‖D‖ := by
    calc
      ‖D.comp W‖ ≤ ‖D‖ * ‖W‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖D‖ := by
        exact mul_le_of_le_one_right (norm_nonneg _) hW
  exact le_antisymm h1 h2

#print axioms HRS.Fp81.S21.fp81s21_physicalWindowExtensionTime_continuous
#print axioms HRS.Fp81.S21.fp81s21_physicalWindowExtension_norm_le
#print axioms HRS.Fp81.S21.fp81s21_physicalWindowRestriction_comp_extension
#print axioms HRS.Fp81.S21.fp81s21_physicalWindow_pullback_norm_eq

end HRS.Fp81.S21

end
