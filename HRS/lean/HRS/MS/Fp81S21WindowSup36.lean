import HRS.MS.Fp81S21WindowSup35

/-! Frozen-source Fubini inputs from uniform raw sixth moments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.S53

/-- The raw scaled S5.3 field for a fixed source-time configuration. -/
def fp81s21_frozen_raw_field {d N : ℕ} {Ω : Type}
    (σ : ℝ) (ρ : Euc d → ℝ) (G : ℝ → Euc d → ℝ)
    (X : Ω → EucConfig d N) (z : ℝ × Ω) : ℝ :=
  (N : ℝ) / 2 * s53_Dk σ ρ (G z.1) (X z.2)

/-- Sixth moments of the raw frozen-source field yield both Fubini inputs. -/
theorem fp81s21_frozen_raw_fubini_of_sixth
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {σ T : ℝ} {ρ : Euc d → ℝ} (hT : 0 ≤ T)
    (hρ : HRS.Whole.IsProbDensity ρ)
    (G : ℝ → Euc d → ℝ)
    (hG : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G τ)) (hc : S53Cont T G)
    (X : Ω → EucConfig d N) (hX : Measurable X)
    (M : ℝ) (hM : 0 ≤ M)
    (hSix : ∀ τ ∈ Icc (0 : ℝ) T, SixthBound P
      (fun ω => fp81s21_frozen_raw_field σ ρ G X (τ, ω)) M) :
    ∀ τ ∈ Icc (0 : ℝ) T,
      Integrable (fun z : Ω × ℝ => fp81s21_frozen_raw_field σ ρ G X (z.2, z.1))
        (P.prod (volume.restrict (Ioc (0 : ℝ) τ))) ∧
      IntervalIntegrable (fun u => ∫ ω, fp81s21_frozen_raw_field σ ρ G X (u, ω) ∂P)
        volume 0 τ := by
  let raw : ℝ × Ω → ℝ := fp81s21_frozen_raw_field σ ρ G X
  let F : ℝ × Ω → ℝ := fun z => raw (s53_clamp T z.1, z.2)
  have hF : Measurable F := by
    change Measurable (fun z : ℝ × Ω => (N : ℝ) / 2 *
      s53_Dk σ ρ (G (s53_clamp T z.1)) (X z.2))
    exact fp81s21_frozen_raw_s53_joint_meas hT hρ G hG hc X hX
  have hSix' : ∀ u : ℝ, SixthBound P (fun ω => F (u, ω)) M := by
    intro u
    change SixthBound P (fun ω => fp81s21_frozen_raw_field σ ρ G X
      (s53_clamp T u, ω)) M
    exact hSix (s53_clamp T u) (s53_clamp_mem hT u)
  have hEq : ∀ u ∈ Icc (0 : ℝ) T, ∀ ω, F (u, ω) = raw (u, ω) := by
    intro u hu ω
    change raw (s53_clamp T u, ω) = raw (u, ω)
    rw [s53_clamp_of_mem hu]
  exact fp81s21_fubini_on_interval_of_sixth P hT F raw hF M hM hSix' hEq

#print axioms fp81s21_frozen_raw_field
#print axioms fp81s21_frozen_raw_fubini_of_sixth
end HRS.Fp81.S21
end
