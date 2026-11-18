import HRS.MS.WsStatAux12

/-!
# S11.1 packet M1: shifted window measurability and the common evaluation event
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.S111BD

open HRS HRS.Whole

theorem s111_wpo_shift {d : ℕ} (m T u : ℝ) (f : ℝ → OscDual d m) :
    windowPathOf m T u f = windowPathOf m T 0 (fun t => f (u + t)) := by
  unfold windowPathOf
  exact HRS.GF.dite_continuousMap_congr _ _ (funext fun t => by simp)

theorem s111_shifted_window_aemeas (d : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : WholeCoeff d) (m q T u H : ℝ)
    (C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ)
    (Z : ℝ → Ω → OscDual d m)
    (hZ : IsLinearGaussianEvolutionW P C m q H C₀ Z)
    (hT : 0 ≤ T) (hu : 0 ≤ u) (hH : u + T ≤ H) :
    AEMeasurable (processWindow m T u Z) P ∧
      ∀ᵐ ζ ∂P, ∀ τ : Set.Icc (0 : ℝ) T,
        OscPath.at' (processWindow m T u Z ζ) τ = Z (u + τ) ζ := by
  have hsub : ∀ t ∈ Set.Icc (0 : ℝ) T, u + t ∈ Set.Icc (0 : ℝ) H :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcont : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Z (u + t) ζ) (Set.Icc 0 T) := by
    filter_upwards [hZ.cont] with ζ hζ
    exact hζ.comp (by fun_prop) (fun t ht => hsub t ht)
  constructor
  · have h := HRS.GF.gfb4_aemeasurable_windowPath P hT (fun t ζ => Z (u + t) ζ)
      (fun t ht => hZ.meas _) hcont
    rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
    have e : processWindow m T u Z =
        fun ζ => windowPathOf m T 0 (fun t => Z (u + t) ζ) :=
      funext fun ζ => s111_wpo_shift m T u (fun t => Z t ζ)
    rw [e]
    exact h
  · filter_upwards [hcont] with ζ hζ τ
    have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Z (u + (t : ℝ)) ζ :=
      (continuousOn_iff_continuous_restrict.1 hζ)
    have e : processWindow m T u Z ζ = (⟨fun t : Set.Icc (0 : ℝ) T => Z (u + (t : ℝ)) ζ, hc⟩ :
        C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
      unfold processWindow windowPathOf
      exact dif_pos hc
    rw [e]
    rfl

end HRS.MS.S111BD
