import HRS.MS.Fp81S21WickApprox37
import HRS.MS.Fp81S21WickApprox38
import HRS.MS.Fp81S21TimeRep16

/-! Fixed particle and Gaussian physical selectors. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The complete particle producer payload for fixed strong-chart choices. -/
def fp81s21_ParticlePhysical31Payload (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (M : ℝ) (N : ℕ) (A : Particle R N)
    (qsη qsB : ℝ → A.Ω → r26t6_Coeff) : Prop :=
  fp81s21_MomentRep Es A.P (fp81s21_particleEmpField R N A) qsη M ∧
  fp81s21_MomentRep Es A.P (fp81s21_particleQuadField R N A) qsB M ∧
  (∀ u : ℝ, 0 ≤ u →
    AEMeasurable (fun ω => dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
      (fp81s21_particleEmpField R N A u ω)) A.P ∧
    (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
      (fp81s21_particleEmpField R N A u ω) ∂A.P) ≤ ENNReal.ofReal (Real.sqrt M)) ∧
  (∀ u : ℝ, 0 ≤ u →
    AEMeasurable (fun ω => dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
      (fp81s21_particleQuadField R N A u ω)) A.P ∧
    (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
      (fp81s21_particleQuadField R N A u ω) ∂A.P) ≤ ENNReal.ofReal (Real.sqrt M)) ∧
  let qη : ℝ → A.Ω → r26t6_Coeff :=
    fun u ω => fp81s21_particle_embedField p Es E (qsη u ω)
  let qB : ℝ → A.Ω → r26t6_Coeff :=
    fun u ω => fp81s21_particle_embedField p Es E (qsB u ω)
  fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A) qη M ∧
  fp81s21_MomentRep E A.P (fp81s21_particleQuadField R N A) qB M ∧
  ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
    ∃ Uη UB : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeRep E A.P (fp81s21_particleEmpField R N A) qη M a H Uη ∧
      fp81s21_TimeRep E A.P (fp81s21_particleQuadField R N A) qB M a H UB ∧
      ∀ m : ℕ,
        fp81s21_SqErr A.P Uη (fun ω => fp81s21_timeProject H m (Uη ω))
          (Real.sqrt (H * M) * ε m) ∧
        fp81s21_SqErr A.P UB (fun ω => fp81s21_timeProject H m (UB ω))
          (Real.sqrt (H * M) * ε m)

/-- The three physical families are fixed before rank and time parameters. -/
structure fp81s21_Physical31 (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εN εG εB : ℕ → ℝ) where
  MN : ℝ
  MN_nonneg : 0 ≤ MN
  qsηN : (N : ℕ) → (2 ≤ N) → (A : Particle R N) → ℝ → A.Ω → r26t6_Coeff
  qsBN : (N : ℕ) → (2 ≤ N) → (A : Particle R N) → ℝ → A.Ω → r26t6_Coeff
  particle : ∀ N hN A, fp81s21_ParticlePhysical31Payload p R Es E εN MN N A
    (qsηN N hN A) (qsBN N hN A)
  gaussian : fp81s21_GaussianPhysical31 p R Es E εG εB

/-- All three selectors and their uniform constants can be chosen together. -/
theorem fp81s21_physical31_exists (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ εN εG εB : ℕ → ℝ,
    (∀ m, 0 ≤ εN m) ∧ Tendsto εN atTop (𝓝 0) ∧
    (∀ m, 0 ≤ εG m) ∧ Tendsto εG atTop (𝓝 0) ∧
    (∀ m, 0 ≤ εB m) ∧ Tendsto εB atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      Nonempty (fp81s21_Physical31 p R Es E εN εG εB) := by
  obtain ⟨εN, hεN, hεNlim, δN, hδN, hδNh, hn⟩ :=
    fp81s21_particle_weakChart_time_tails p Es E
  obtain ⟨εG, εB, hεG, hεGlim, hεB, hεBlim, δG, hδG, hδGh, hg⟩ :=
    fp81s21_gaussianPhysical31_exists p Es E
  let δ0 := min δN δG
  refine ⟨εN, εG, εB, hεN, hεNlim, hεG, hεGlim, hεB, hεBlim,
    δ0, lt_min hδN hδG, (min_le_left _ _).trans hδNh, ?_⟩
  intro δ hδ hδle R
  obtain ⟨MN, hMN, hN⟩ := hn δ hδ (hδle.trans (min_le_left _ _)) R
  choose qη qB hq using hN
  exact ⟨⟨MN, hMN, qη, qB, hq,
    Classical.choice (hg δ hδ (hδle.trans (min_le_right _ _)) R)⟩⟩

#print axioms fp81s21_ParticlePhysical31Payload
#print axioms fp81s21_Physical31
#print axioms fp81s21_physical31_exists
end HRS.Fp81.S21
end
