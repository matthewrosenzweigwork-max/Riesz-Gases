import HRS.Sections.QuenchAux13

/-!
# Packet QUENCH (Q27), part 14: Proposition 7.13, first part (`quench_modes`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

lemma isBrownian_sgn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B₀ : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B₀ P) (b : Bool) : IsBrownianReal (fun t ω => sgn b * B₀ t ω) P := by
  cases b
  · have := hB.neg
    have e : (fun t ω => sgn false * B₀ t ω) = -B₀ := by
      funext t ω; simp [sgn]
    rw [e]; exact this
  · have e : (fun t ω => sgn true * B₀ t ω) = B₀ := by
      funext t ω; simp [sgn]
    rw [e]; exact hB

theorem quench_modes_core (hd : 2 ≤ d) {s β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀)
    (D : DynData d) (hD : IsGradientData D s β (fun _ => 0)) (m : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZ : IsGaussianLimitField D (fun _ _ => 1) volume β₀ m P Z) :
    (∀ (k : PosHalf d) (b : Bool), ∃ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P ∧
        IndepFun (fun ω => NegSobolev.eval (Z 0 ω) (modeFn k.1 b)) (fun ω => fun t => B t ω) P ∧
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, NegSobolev.eval (Z t ω) (modeFn k.1 b) =
          NegSobolev.eval (Z 0 ω) (modeFn k.1 b) -
            lamMode d s β k.1 * (∫ u in Set.Icc (0 : ℝ) t, NegSobolev.eval (Z u ω) (modeFn k.1 b)) +
            Real.sqrt (2 / β) * (2 * Real.pi * Lattice.enorm k.1) * B t ω) ∧
    (∀ (k : PosHalf d) (b : Bool),
      ∫ ω, NegSobolev.eval (Z 0 ω) (modeFn k.1 b) ^ 2 ∂P = varMode d s β₀ k.1) ∧
    iIndepFun (fun (kb : PosHalf d × Bool) ω => fun t : ℝ≥0 =>
      NegSobolev.eval (Z t ω) (modeFn kb.1.1 kb.2)) P ∧
    (∀ (k : PosHalf d) (b : Bool) (a t r : ℝ), 0 ≤ a → 0 ≤ t → 0 ≤ r →
      ∫ ω, NegSobolev.eval (Z (a + t) ω) (modeFn k.1 b) * NegSobolev.eval (Z (a + r) ω) (modeFn k.1 b) ∂P =
        varMode d s β k.1 * Real.exp (-lamMode d s β k.1 * |t - r|) +
          deltaVar d s β β₀ k.1 * Real.exp (-2 * lamMode d s β k.1 * a) *
            Real.exp (-lamMode d s β k.1 * (t + r))) := by
  have hs0 : 0 ≤ s := hD.1 ▸ D.hs0
  have hsd : s < d := hD.1 ▸ D.hsd
  obtain ⟨Y, mf⟩ := modeField_of_limit hd hβ hβ₀ D hD P Z hZ
  have hev : ∀ (k : PosHalf d) (b : Bool) (t : ℝ) (ω : Ω), NegSobolev.eval (Z t ω) (modeFn k.1 b) =
      sgn b * NegSobolev.fourierCoeff (Z t ω) (idx k b) := by
    intro k b t ω; rw [modeFn_eq, eval_mode]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k b
    obtain ⟨B₀, hB, hind, hid⟩ := mode_bm hd hs0 hsd hβ mf (idx k b)
    refine ⟨fun t ω => sgn b * B₀ t ω, isBrownian_sgn hB b, ?_, ?_⟩
    · have h1 := hind.comp (φ := fun x : ℝ => sgn b * x) (ψ := fun p : ℝ≥0 → ℝ => fun t => sgn b * p t)
        (by fun_prop) (by fun_prop)
      refine h1.congr ?_ (ae_eq_refl _)
      filter_upwards [mf.init] with ω h
      simp only [Function.comp_apply]
      rw [hev, h]
    · filter_upwards [hid] with ω hω t
      simp only [hev]
      have := hω t
      rw [integral_const_mul]
      have e1 : sigmaMode β (idx k b) = Real.sqrt (2 / β) * (2 * Real.pi * Lattice.enorm k.1) := by
        unfold sigmaMode; rw [enorm_idx]
      have hl : lamMode d s β (idx k b).1 = lamMode d s β k.1 := by
        unfold lamMode; rw [enorm_idx, rieszCoeff_idx]
      rw [hl] at this
      rw [← e1]
      calc sgn b * NegSobolev.fourierCoeff (Z t ω) (idx k b)
          = sgn b * (NegSobolev.fourierCoeff (Z 0 ω) (idx k b) -
            lamMode d s β k.1 * (∫ u in Set.Icc (0 : ℝ) t, NegSobolev.fourierCoeff (Z u ω) (idx k b)) +
            sigmaMode β (idx k b) * B₀ t ω) := by rw [← this]
        _ = _ := by ring
  · intro k b
    have h1 : ∀ ω, NegSobolev.eval (Z 0 ω) (modeFn k.1 b) ^ 2 =
        (NegSobolev.fourierCoeff (Z 0 ω) (idx k b)) ^ 2 := by
      intro ω; rw [hev, mul_pow, sgn_sq, one_mul]
    simp_rw [h1]
    have h2 : ∫ ω, NegSobolev.fourierCoeff (Z 0 ω) (idx k b) ^ 2 ∂P =
        ∫ ω, NegSobolev.fourierCoeff (Y ω) (idx k b) ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [mf.init] with ω h
      rw [h]
    rw [h2]
    have := mf.covY (idx k b) (idx k b)
    simp only [if_true] at this
    simp_rw [sq]
    rw [this, varMode_idx]
  · exact indep_modes hd hs0 hsd hβ mf
  · intro k b a t r ha ht hr
    have := Z_cov hd hs0 hsd hβ mf (idx k b) (idx k b) (t := a + t) (r := a + r) (by linarith) (by linarith)
    simp only [if_true] at this
    have h1 : ∀ ω, NegSobolev.eval (Z (a + t) ω) (modeFn k.1 b) * NegSobolev.eval (Z (a + r) ω) (modeFn k.1 b) =
        NegSobolev.fourierCoeff (Z (a + t) ω) (idx k b) * NegSobolev.fourierCoeff (Z (a + r) ω) (idx k b) := by
      intro ω
      rw [hev, hev]
      have := sgn_sq b
      calc sgn b * NegSobolev.fourierCoeff (Z (a + t) ω) (idx k b) *
            (sgn b * NegSobolev.fourierCoeff (Z (a + r) ω) (idx k b))
          = sgn b ^ 2 * (NegSobolev.fourierCoeff (Z (a + t) ω) (idx k b) *
            NegSobolev.fourierCoeff (Z (a + r) ω) (idx k b)) := by ring
        _ = _ := by rw [this, one_mul]
    simp_rw [h1]
    have hl : lamMode d s β (idx k b).1 = lamMode d s β k.1 := by
      unfold lamMode; rw [enorm_idx, rieszCoeff_idx]
    rw [this, hl, ← varMode_idx β k b, ← deltaVar_idx β β₀ k b]
    have e1 : (a + t) - (a + r) = t - r := by ring
    have e2 : Real.exp (-lamMode d s β k.1 * ((a + t) + (a + r))) =
        Real.exp (-2 * lamMode d s β k.1 * a) * Real.exp (-lamMode d s β k.1 * (t + r)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1, e2]
    ring

end Qch

end HRS
