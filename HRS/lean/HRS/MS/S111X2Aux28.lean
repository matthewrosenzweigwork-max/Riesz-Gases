import HRS.MS.S111X2Aux27
import HRS.PDE.MovBAux1
import HRS.MS.S111X1F2

/-!
# S11.1 X2, packet E07 (part 3): the clamped time family of a classical solution, and the candidate `φ + ∫_r^H h`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34
open HRS.MS.S111X1 (EnData KData Nnl)

variable {d : ℕ}

/-- Clamping of the time variable to `[0,H]`. -/
def s111x2_clamp (H u : ℝ) : ℝ := max 0 (min u H)

theorem s111x2_clamp_mem {H : ℝ} (hH : 0 ≤ H) (u : ℝ) : s111x2_clamp H u ∈ Icc (0 : ℝ) H :=
  ⟨le_max_left _ _, max_le hH (min_le_right _ _)⟩

theorem s111x2_clamp_cont (H : ℝ) : Continuous (s111x2_clamp H) := by
  unfold s111x2_clamp; fun_prop

theorem s111x2_clamp_id {H u : ℝ} (hu : u ∈ Icc 0 H) : s111x2_clamp H u = u := by
  unfold s111x2_clamp; rw [min_eq_left hu.2, max_eq_right hu.1]

/-- The clamped time family of a classical solution is a `C²` family with bounded jointly continuous derivatives. -/
theorem s111x2_clamp_fam {C : WholeCoeff d} {H : ℝ} (hH : 0 ≤ H) {ψ : Euc d → ℝ} {h : ℝ → Euc d → ℝ}
    (hh : IsClassicalAdjointW C H ψ h) :
    ∃ B0 B1 B2 : ℝ, 0 ≤ B0 ∧ 0 ≤ B1 ∧ 0 ≤ B2 ∧ C2Fam (fun u => h (s111x2_clamp H u)) B1 B2 ∧
      ∀ u x, |h (s111x2_clamp H u) x| ≤ B0 := by
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hB⟩ := HRS.MS.S111X1.classical_bounds hh
  have hq : Continuous fun p : ℝ × Euc d =>
      ((⟨s111x2_clamp H p.1, s111x2_clamp_mem hH p.1⟩ : Icc (0 : ℝ) H), p.2) :=
    (((s111x2_clamp_cont H).subtype_mk _).comp continuous_fst).prodMk continuous_snd
  refine ⟨B0, B1, B2, hB0, hB1, hB2, ⟨fun u => hh.c2 _ (s111x2_clamp_mem hH u),
    fun u x => (hB _ (s111x2_clamp_mem hH u) x).2.1, fun u x => (hB _ (s111x2_clamp_mem hH u) x).2.2, ?_, ?_, ?_⟩,
    fun u x => ?_⟩
  · have h0 := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp
      ((hh.cont_c2 0 (by norm_num)).comp hq)
    refine h0.congr fun p => ?_
    simp [iteratedFDeriv_zero_eq_comp]
  · have h1 := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp
      ((hh.cont_c2 1 (by norm_num)).comp hq)
    refine h1.congr fun p => ?_
    simp [HRS.fderiv_eq_curry]
  · have h2 := (HRS.continuous_curry2 d).comp ((hh.cont_c2 2 le_rfl).comp hq)
    refine h2.congr fun p => ?_
    simp [HRS.fderiv_fderiv_eq_curry2]
  · rw [← Real.norm_eq_abs]; exact (hB _ (s111x2_clamp_mem hH u) x).1

section Ftil

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

/-- The candidate `φ + ∫_r^H h`. -/
def s111x2_Ftil (φ : Euc d → ℝ) (hb : ℝ → Euc d → ℝ) (H r : ℝ) (y : Euc d) : ℝ :=
  φ y + ∫ u in r..H, hb u y

theorem s111x2_cont_param_left {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℝ → X → F) (hc : Continuous (fun p : ℝ × X => g p.1 p.2)) (H : ℝ) :
    Continuous (fun p : ℝ × X => ∫ u in p.1..H, g u p.2) := by
  have := (s111x2_cont_param g hc H).neg
  refine this.congr fun p => ?_
  rw [Pi.neg_apply]; exact (intervalIntegral.integral_symm H p.1).symm

theorem s111x2_ftil_fderiv {g : ℝ → Euc d → ℝ} {B1 B2 : ℝ} (hg : C2Fam g B1 B2) {φ : Euc d → ℝ} {A1 A2 : ℝ}
    (hφ : CbD φ A1 A2) (H r : ℝ) (y : Euc d) :
    fderiv ℝ (s111x2_Ftil φ g H r) y = fderiv ℝ φ y + ∫ u in r..H, fderiv ℝ (g u) y := by
  unfold s111x2_Ftil
  rw [fderiv_fun_add (hφ.smooth.differentiable (by norm_num) y) ((hg.hasFDerivAt r H y).differentiableAt),
    (hg.hasFDerivAt r H y).fderiv]

theorem s111x2_ftil_fderiv₂ {g : ℝ → Euc d → ℝ} {B1 B2 : ℝ} (hg : C2Fam g B1 B2) {φ : Euc d → ℝ} {A1 A2 : ℝ}
    (hφ : CbD φ A1 A2) (H r : ℝ) (y : Euc d) :
    fderiv ℝ (fderiv ℝ (s111x2_Ftil φ g H r)) y =
      fderiv ℝ (fderiv ℝ φ) y + ∫ u in r..H, fderiv ℝ (fderiv ℝ (g u)) y := by
  have hfd : fderiv ℝ (s111x2_Ftil φ g H r) = fun y => fderiv ℝ φ y + ∫ u in r..H, fderiv ℝ (g u) y :=
    funext fun y => s111x2_ftil_fderiv hg hφ H r y
  rw [hfd, fderiv_fun_add ((hφ.smooth.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y)
    ((hg.hasFDerivAt₂ r H y).differentiableAt), (hg.hasFDerivAt₂ r H y).fderiv]

theorem s111x2_ftil_gen (T : TD d s β ρ M C) {H : ℝ} {φ : Euc d → ℝ} {A1 A2 : ℝ} (hφ : CbD φ A1 A2)
    {h : ℝ → Euc d → ℝ} (hh : IsClassicalAdjointW C H (generatorW C 0 φ) h)
    {B1 B2 : ℝ} (hfam : C2Fam (fun u => h (s111x2_clamp H u)) B1 B2) {r : ℝ} (hr : r ∈ Icc 0 H) (x : Euc d) :
    generatorW C 0 (s111x2_Ftil φ (fun u => h (s111x2_clamp H u)) H r) x = h r x := by
  have hH : 0 ≤ H := hr.1.trans hr.2
  obtain ⟨hgi, hint⟩ := s111x2_gen_integral T hfam hφ hr.2 x
  have hcb : ∀ u ∈ Icc (0 : ℝ) H, CbD (h u) B1 B2 := fun u hu => by
    have := (⟨hfam.smooth u, hfam.b1 u, hfam.b2 u⟩ : CbD (h (s111x2_clamp H u)) B1 B2)
    rwa [s111x2_clamp_id hu] at this
  have hd : ∀ u ∈ Ioo r H, HasDerivAt (fun u => h u x)
      (-generatorW C 0 (h (s111x2_clamp H u)) x) u := by
    intro u hu
    have hu0 : u ∈ Ioo 0 H := ⟨lt_of_le_of_lt hr.1 hu.1, hu.2⟩
    have hu1 : u ∈ Icc 0 H := ⟨hu0.1.le, hu0.2.le⟩
    have := hh.time_deriv x u hu0
    rw [s111x2_gen_auto T (hcb u hu1) u] at this
    rw [s111x2_clamp_id hu1]
    exact this
  have hc : ContinuousOn (fun u => h u x) (Icc r H) := by
    have := (hfam.c0.comp (continuous_id.prodMk continuous_const : Continuous fun u : ℝ => (u, x))).continuousOn
      (s := Icc r H)
    refine this.congr fun u hu => ?_
    simp only [Function.comp_apply, id]
    rw [s111x2_clamp_id ⟨hr.1.trans hu.1, hu.2⟩]
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.2 hc hd hint.neg
  rw [intervalIntegral.integral_neg] at key
  have hterm : h H x = generatorW C 0 φ x := by rw [hh.terminal]
  unfold s111x2_Ftil
  rw [hgi]
  linarith

end Ftil

end HRS.MS.S111X2
