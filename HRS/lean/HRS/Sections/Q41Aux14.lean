import HRS.PDE.MeanField
import HRS.PDE.MeanFieldFejer
import HRS.PDE.MeanFieldThermalUnique
import HRS.PDE.MeanFieldThermal
import HRS.Energy.Modulated

/-!
# Packet Q41, helper 14: regularity of an arbitrary thermal density

Every `IsThermalDensity` (no continuity assumed) is positive, bounded, continuous and hence smooth
for smooth `V` (`q41_thermal_regular`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE

variable {d : ℕ}

/-- `g ⋆ h` is continuous for an integrable kernel and a bounded measurable `h`. -/
theorem q41_continuous_convFun_bdd {g h : Torus d → ℝ} (hg : Integrable g) (hhm : Measurable h)
    {M : ℝ} (hM : ∀ y, |h y| ≤ M) : Continuous (convFun g h) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hmod : Tendsto (fun x : Torus d => ∫ w, |g (w - (x₀ - x)) - g w|) (𝓝 x₀) (𝓝 0) := by
    refine (MFThermalExist.l1_modulus hg).comp ?_
    have hc : Continuous fun x : Torus d => x₀ - x := continuous_const.sub continuous_id
    have := hc.tendsto x₀
    simp only [sub_self] at this
    exact this
  have hbound : ∀ x : Torus d, |convFun g h x - convFun g h x₀| ≤
      M * ∫ w, |g (w - (x₀ - x)) - g w| := by
    intro x
    have i1 : Integrable fun y => g (x - y) * h y :=
      (hg.comp_sub_left x).mul_bdd (hhm.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hM y)
    have i2 : Integrable fun y => g (x₀ - y) * h y :=
      (hg.comp_sub_left x₀).mul_bdd (hhm.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hM y)
    have hdiff : convFun g h x - convFun g h x₀ = ∫ y, (g (x - y) - g (x₀ - y)) * h y := by
      unfold convFun
      rw [← integral_sub i1 i2]
      congr 1; funext y; ring
    have iabs : Integrable fun y => |g (x - y) - g (x₀ - y)| :=
      ((hg.comp_sub_left x).sub (hg.comp_sub_left x₀)).abs
    have hsub : ∫ y, |g (x - y) - g (x₀ - y)| = ∫ w, |g (w - (x₀ - x)) - g w| := by
      rw [← integral_sub_left_eq_self (fun w => |g (w - (x₀ - x)) - g w|) volume x₀]
      congr 1; funext y
      have : x₀ - y - (x₀ - x) = x - y := by abel
      rw [this]
    rw [hdiff, ← Real.norm_eq_abs]
    calc ‖∫ y, (g (x - y) - g (x₀ - y)) * h y‖ ≤ ∫ y, |g (x - y) - g (x₀ - y)| * M :=
          norm_integral_le_of_norm_le (iabs.mul_const M) (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _))
      _ = M * ∫ w, |g (w - (x₀ - x)) - g w| := by
          rw [integral_mul_const, hsub]; ring
  have h0 : Tendsto (fun x : Torus d => M * ∫ w, |g (w - (x₀ - x)) - g w|) (𝓝 x₀) (𝓝 0) := by
    simpa using hmod.const_mul M
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have := (Metric.tendsto_nhds.1 h0) ε hε
  filter_upwards [this] with x hx
  rw [Real.dist_eq] at hx ⊢
  have hx' : M * ∫ w, |g (w - (x₀ - x)) - g w| < ε := by
    have := lt_of_le_of_lt (le_abs_self _) hx
    simpa using this
  exact lt_of_le_of_lt (hbound x) hx'

/-- A thermal density is positive and continuous (no a priori regularity assumed). -/
theorem q41_thermal_pos_cont (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    {V : Torus d → ℝ} (hVc : Continuous V) {ρ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) :
    (∀ x, 0 < ρ x) ∧ Continuous ρ := by
  set Z : ℝ := ∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y)) with hZ
  have hZ0 : 0 ≤ Z := integral_nonneg fun y => (Real.exp_pos _).le
  have hZpos : 0 < Z := by
    rcases hZ0.eq_or_lt with h | h
    · exfalso
      have h1 : ∀ x, ρ x = 0 := fun x => by rw [hρ.2 x, ← hZ, ← h, div_zero]
      have := hρ.1.integral_one
      simp [h1] at this
    · exact h
  have hpos : ∀ x, 0 < ρ x := fun x => by
    rw [hρ.2 x, ← hZ]; exact div_pos (Real.exp_pos _) hZpos
  refine ⟨hpos, ?_⟩
  have hint : Integrable ρ := by
    by_contra h
    have := hρ.1.integral_one
    rw [integral_undef h] at this
    norm_num at this
  -- boundedness
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0 hsd
  have hB0 : ∀ x, -|B| ≤ periodicRiesz d s x := fun x =>
    (neg_le_neg (le_abs_self B)).trans (hB x)
  have hconv_lo : ∀ x, -|B| ≤ convFun (periodicRiesz d s) ρ x := by
    intro x
    unfold convFun
    by_cases hi : Integrable fun y => periodicRiesz d s (x - y) * ρ y
    · have hi2 : Integrable fun y => -|B| * ρ y := hint.const_mul _
      calc -|B| = -|B| * ∫ y, ρ y := by rw [hρ.1.integral_one]; ring
        _ = ∫ y, -|B| * ρ y := by rw [integral_const_mul]
        _ ≤ _ := integral_mono hi2 hi fun y =>
            mul_le_mul_of_nonneg_right (hB0 _) (hρ.1.nonneg y)
    · rw [integral_undef hi]; exact neg_nonpos.2 (abs_nonneg _)
  obtain ⟨Mv, hMv⟩ := isCompact_univ.exists_bound_of_continuousOn hVc.continuousOn
  have hbd : ∀ x, |ρ x| ≤ Real.exp (β * (Mv + |B|)) / Z := by
    intro x
    rw [abs_of_pos (hpos x), hρ.2 x, ← hZ]
    refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) hZpos.le
    have h1 := hMv x (Set.mem_univ x)
    have h2 := hconv_lo x
    have h3 : -Mv ≤ V x := (abs_le.1 (by simpa [Real.norm_eq_abs] using h1)).1
    have h5 : -(Mv + |B|) ≤ V x + convFun (periodicRiesz d s) ρ x := by linarith
    nlinarith
  have hg : Integrable (periodicRiesz d s : Torus d → ℝ) :=
    MFOneLe.integrable_periodicRiesz (by omega) s hs0 hsd
  have hcc := q41_continuous_convFun_bdd hg hρ.1.measurable hbd
  have : ρ = fun x => Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x)) / Z := by
    funext x; rw [hρ.2 x]
  rw [this]
  exact (Real.continuous_exp.comp (continuous_const.mul (hVc.add hcc))).div_const _

/-- A thermal density for smooth `V` is positive and smooth. -/
theorem q41_thermal_regular (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {ρ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) :
    (∀ x, 0 < ρ x) ∧ Torus.IsSmooth ρ := by
  have hVc : Continuous V :=
    MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  obtain ⟨hp, hc⟩ := q41_thermal_pos_cont hd hs0 hsd hβ hVc hρ
  exact ⟨hp, MFThermalAssembly.thermal_isSmooth_all (by omega) s hs0 hsd V hV β hβ ρ hρ hc hp⟩

end HRS.Q41
