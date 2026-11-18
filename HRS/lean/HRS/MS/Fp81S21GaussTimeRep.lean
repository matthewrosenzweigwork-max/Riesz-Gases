import HRS.MS.Fp81S21GaussMomRep10
import HRS.MS.Fp81S21EmbedTail
import HRS.MS.Fp81S21TimeRep12

/-! Coefficient-only time sections and projection tails for the embedded
linear Gaussian field. The raw weighted-test bridge is a separate obligation. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

local instance fp81s21_gaussTimeRep_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_gaussTimeRep_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

universe u v w

private theorem fp81s21_gaussian_transport_projection
    {α : Sort u} {P : α → Sort v} {Q : α → Sort w}
    (f : ∀ a, P a → Q a) {a b : α} (h : a = b) (x : P a) :
    f b (h ▸ x) = h ▸ f a x := by
  cases h
  rfl

/-- The fixed weak-chart representative obtained by applying the Gaussian
chart embedding to the strong-chart coefficient field. -/
noncomputable def fp81s21_gaussian_embedFamily (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {Ω : Type*} (qs : ℝ → Ω → r26t6_Coeff) : ℝ → Ω → r26t6_Coeff := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2) := by
    nlinarith [p.hd]
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  let Es' : r26t6_WeightedChart p.d (2 * p.d + 6)
      (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ Es
  exact fun u ω => fp81s21_embedField hP hPs Es' E (qs u ω)

/-- A fixed profile controls the embedded linear Gaussian's coefficient-only
time sections and their finite-rank projection errors. This theorem does not
identify raw oscillator evaluations on noncompact weighted tests. -/
theorem fp81s21_gaussian_weakChart_time_L2_tails (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ ε : ℕ → ℝ,
      (∀ m, 0 ≤ ε m) ∧
      Tendsto ε atTop (𝓝 0) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
          ∃ M : ℝ, 0 ≤ M ∧
            ∀ G : GaussianRealization R,
              ∃ qs : ℝ → G.Ω → r26t6_Coeff,
                fp81s21_MomentRep Es G.P
                  (fun u ω f => OscDual.eval (G.Z u ω) f) qs M ∧
                (∀ u : ℝ, 0 ≤ u →
                  AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                    ((p.d : ℝ) + 4)
                    (fun f => OscDual.eval (G.Z u ω) f)) G.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                    (fun f => OscDual.eval (G.Z u ω) f) ∂G.P) ≤
                    ENNReal.ofReal (Real.sqrt M)) ∧
                (let q := fp81s21_gaussian_embedFamily p Es E qs
                 fp81s21_MomentRep E G.P
                   (fun u ω f => OscDual.eval (G.Z u ω) f) q M ∧
                 (∀ u : ℝ, 0 ≤ u →
                   AEMeasurable (fun ω => dualNormE (2 * p.d + 8)
                     ((p.d : ℝ) + 2)
                     (fun f => OscDual.eval (G.Z u ω) f)) G.P ∧
                   (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
                     (fun f => OscDual.eval (G.Z u ω) f) ∂G.P) ≤
                     ENNReal.ofReal (Real.sqrt M)) ∧
                 ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
                   ∃ U : G.Ω → Lp r26t6_Coeff 2
                       (volume.restrict (Set.Icc (0 : ℝ) H)),
                     fp81s21_TimeL2Rep G.P q M a H U ∧
                     ∀ m : ℕ,
                       fp81s21_SqErr G.P U
                         (fun ω => fp81s21_timeProject H m (U ω))
                         (Real.sqrt (H * M) * ε m) ∧
                       ∀ ρ : ℝ, 0 < ρ →
                         G.P {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖} ≤
                           ENNReal.ofReal (H * M * (ε m) ^ 2 / ρ ^ 2)) := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2) := by
    nlinarith [p.hd]
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  let Es' : r26t6_WeightedChart p.d (2 * p.d + 6)
      (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ Es
  obtain ⟨ε, hε, hεlim, hprofile⟩ :=
    fp81s21_embedField_projectionTail hP hPs Es' E
  obtain ⟨δ₀, hδ₀, hhalf, hgauss⟩ :=
    fp81s21_gaussian_momentRep_embedded p
  refine ⟨ε, hε, hεlim, δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M, hM, hrealizations⟩ := hgauss δ hδ hδle R Es E
  refine ⟨M, hM, ?_⟩
  intro G
  obtain ⟨qs, hstrong, _⟩ := hrealizations G
  let Pkg : ℝ → Type := fun w =>
    PSigma fun Eη : r26t6_WeightedChart p.d (2 * p.d + 6) w =>
      fp81s21_MomentRep Eη G.P
        (fun u ω f => OscDual.eval (G.Z u ω) f) qs M
  let hPkg : Pkg ((p.d : ℝ) + 4) := ⟨Es, hstrong⟩
  let hPkg' : Pkg (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ hPkg
  have hstrong' : fp81s21_MomentRep Es' G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) qs M := by
    have hcast := fp81s21_gaussian_transport_projection
      (fun w (x : Pkg w) => x.1) hExp.symm hPkg
    have hchart : hPkg'.1 = Es' := by
      simpa [hPkg', hPkg, Pkg, Es'] using hcast
    rw [← hchart]
    exact hPkg'.2
  let Q : ℝ → G.Ω → (Euc p.d → ℝ) → ℝ :=
    fun u ω f => OscDual.eval (G.Z u ω) f
  let q : ℝ → G.Ω → r26t6_Coeff := fp81s21_gaussian_embedFamily p Es E qs
  have hfirstStrong : ∀ u : ℝ, 0 ≤ u →
      AEMeasurable (fun ω => dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (Q u ω)) G.P ∧
      (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (Q u ω) ∂G.P) ≤ ENNReal.ofReal (Real.sqrt M) := by
    intro u hu
    exact fp81s21_MomentRep_firstMoment Es G.P Q qs M hstrong u hu
  have hweak : fp81s21_MomentRep E G.P Q q M := by
    have hEmbed := fp81s21_MomentRep_embedField hP hPs Es' E G.P Q qs M hstrong'
    change fp81s21_MomentRep E G.P Q
      (fun u ω => fp81s21_embedField hP hPs Es' E (qs u ω)) M
    exact hEmbed
  have hfirstWeak : ∀ u : ℝ, 0 ≤ u →
      AEMeasurable (fun ω => dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
        (Q u ω)) G.P ∧
      (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
        (Q u ω) ∂G.P) ≤ ENNReal.ofReal (Real.sqrt M) := by
    intro u hu
    exact fp81s21_MomentRep_firstMoment E G.P Q q M hweak u hu
  refine ⟨qs, hstrong, hfirstStrong, ?_⟩
  refine ⟨hweak, hfirstWeak, ?_⟩
  intro a ha H hH
  obtain ⟨U, hcore⟩ := fp81s21_MomentRep_time_section E G.P Q q M a H hweak ha
    (le_of_lt hH)
  have hq : Measurable (Function.uncurry q) := hweak.1
  have htail : ∀ m u, 0 ≤ u →
      Integrable (fun ω => ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2) G.P ∧
      (∫ ω, ‖q u ω - fp81s21_projectField m (q u ω)‖ ^ 2 ∂G.P) ≤
        M * (ε m) ^ 2 := by
    intro m u hu
    obtain ⟨hi, hb, _⟩ := hprofile G.P Q qs M hstrong' m u hu
    exact ⟨by simpa [q, fp81s21_gaussian_embedFamily] using hi,
      by simpa [q, fp81s21_gaussian_embedFamily] using hb⟩
  have htails := fp81s21_time_projection_tails G.P q M a H U hq hcore hM ha
    (le_of_lt hH) ε hε htail
  refine ⟨U, hcore, ?_⟩
  intro m
  exact ⟨(htails m).1, (htails m).2⟩

#print axioms fp81s21_gaussian_embedFamily
#print axioms fp81s21_gaussian_weakChart_time_L2_tails

end HRS.Fp81.S21
