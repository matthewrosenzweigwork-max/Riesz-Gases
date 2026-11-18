import HRS.MS.Fp81S21PathMom
import HRS.MS.Fp81S21NoisePath5

/-! Uniform sixth moment and rational-time identification of the reconstructed noise. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MP.RdRem

/-- A measurable random variable whose norm has a bounded sixth moment. -/
def fp81s21_Moment6 {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E]
    (P : Measure Ω) (Y : Ω → E) (M : ℝ) : Prop :=
  AEMeasurable Y P ∧ Integrable (fun ω => ‖Y ω‖ ^ 6) P ∧
    (∫ ω, ‖Y ω‖ ^ 6 ∂P) ≤ M

/-- All modes and rational local times match on one full-measure event. -/
def fp81s21_NoiseMatch (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    {H : ℝ} (hH : 0 < H) (b : ℝ)
    (G : A.Ω → OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H) : Prop :=
  ∀ᵐ ζ ∂A.P, ∀ (α : MultiIndex p.d) (q : ℚ),
    OscDual.coord (OscPath.at' (G ζ) ⟨mrrClamp H (q : ℝ), mrrClamp_mem hH.le (q : ℝ)⟩) α =
      fp81s21_shiftedNoiseDiff p R A F b (b + mrrClamp H (q : ℝ)) α ζ

/-- The full continuous reconstructed noise has a uniform sixth-moment bound
and matches the shifted physical noise at all rational local times. -/
theorem fp81s21_noisePath (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ CM : ℝ, 0 ≤ CM ∧ ∀ H : ℝ, ∀ hH : 0 < H,
        ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
        ∀ b : ℝ, 0 ≤ b → ∀ F : FilteredParticle A,
        ∃ G : A.Ω → OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H,
          fp81s21_Moment6 A.P G ((CM * (1 + Real.sqrt H) ^ 3) ^ 6) ∧
          fp81s21_NoiseMatch p R A F hH b G := by
  obtain ⟨δf, hδf, hδfh, hfeat⟩ := fp81s21_noisePath_feature p
  obtain ⟨δa, hδa, hδah, hadj⟩ := fp81s21_path_moving_adjoint_window p
  refine ⟨min δf δa, lt_min hδf hδa, (min_le_left _ _).trans hδfh, ?_⟩
  intro δ hδ hδle R
  obtain ⟨C0, hC0, hfeature⟩ := hfeat δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨hC, hK⟩ := hadj δ hδ (hδle.trans (min_le_right _ _)) R
  have hbdg : 0 ≤ fp81s21_noisePathBDG :=
    (Classical.choose_spec fp81s21_noisePath_uniform_bdg).1
  have hβ : 0 ≤ p.β⁻¹ := inv_nonneg.mpr p.hβ.le
  let a : ℝ := 2 * p.β⁻¹ * (p.d : ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let CM : ℝ := 3 * (fp81s21_noisePathBDG + 1) * (a + 1) * C0
  have hCM : 0 ≤ CM := by dsimp [CM]; positivity
  refine ⟨CM, hCM, ?_⟩
  intro H hH N hN A b hb F
  obtain ⟨hphysical, hbound⟩ := hfeature H hH b hb
  obtain ⟨G, hG, hint, hmom, hmatch⟩ :=
    fp81s21_noisePath_moment_match p R hN A F hH hb hphysical
      (hC (b + H) (by linarith)) (hK H hH b hb)
      (C0 * (1 + Real.sqrt H)) (by positivity) hbound
  refine ⟨G, ⟨hG, hint, ?_⟩, hmatch⟩
  apply hmom.trans
  simpa only [a, CM, mul_assoc] using
    fp81s21_noisePath_horizon_envelope fp81s21_noisePathBDG a C0 H hbdg ha hC0 hH.le

#print axioms HRS.Fp81.S21.fp81s21_noisePath
end HRS.Fp81.S21
