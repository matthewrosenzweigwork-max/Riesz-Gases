import HRS.Sections.QuenchAux12

/-!
# Packet QUENCH (Q27), part 13: the OU equation of a mode with its Brownian motion
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

/-- The noise amplitude `σ_j = √(2/β) (2π|j|)`. -/
def sigmaMode (β : ℝ) (j : NonzeroLattice d) : ℝ := Real.sqrt (2 / β) * (2 * Real.pi * Lattice.enorm j.1)

lemma sigmaMode_pos {β : ℝ} (hβ : 0 < β) (j : NonzeroLattice d) : 0 < sigmaMode β j := by
  unfold sigmaMode
  have : 1 ≤ Lattice.enorm j.1 := PDE.one_le_enorm_of_ne_zeroU j.2
  have : 0 < Lattice.enorm j.1 := by linarith
  positivity

lemma sigmaMode_sq {s β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (j : NonzeroLattice d) :
    sigmaMode β j ^ 2 = 2 * lamMode d s β j.1 * varMode d s β j.1 := by
  have hv := lamMode_mul_varMode hd hs0 hsd hβ j
  unfold sigmaMode
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have e : 2 * lamMode d s β j.1 * varMode d s β j.1 = 2 * (lamMode d s β j.1 * varMode d s β j.1) := by ring
  rw [e, hv]
  field_simp

section ModeBM

variable {s β β₀ m : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
theorem mode_bm (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) :
    ∃ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P ∧
      IndepFun (fun ω => NegSobolev.fourierCoeff (Y ω) j) (fun ω t => B t ω) P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, NegSobolev.fourierCoeff (Z t ω) j =
        NegSobolev.fourierCoeff (Z 0 ω) j -
          lamMode d s β j.1 * (∫ u in Set.Icc (0 : ℝ) t, NegSobolev.fourierCoeff (Z u ω) j) +
          sigmaMode β j * B t ω := by
  have hN := ouNoise_of_modeField hd hs0 hsd hβ mf j
  have hlam := lamMode_pos hd hs0 hsd hβ j
  have hv := varMode_pos hd hs0 hsd hβ j
  have hσ := sigmaMode_sq hd hs0 hsd hβ j
  refine ⟨fun t ω => bmProc (lamMode d s β j.1) (sigmaMode β j) (fun t ω => ncoord s β Y Z j t ω) (t : ℝ) ω,
    bm_isBrownian hN hv hlam hσ, bm_indep hN hv hlam hσ, ?_⟩
  filter_upwards [mf.cont, mf.init] with ω hc hinit t
  set lam := lamMode d s β j.1 with hlamdef
  set y := NegSobolev.fourierCoeff (Y ω) j with hy
  set f : ℝ → ℝ := fun u => NegSobolev.fourierCoeff (Z u ω) j with hf
  have hfc : ContinuousOn f (Set.Icc 0 (t : ℝ)) :=
    (HRS.FieldSingAux.coordCLM m j).continuous.comp_continuousOn (hc t)
  have hG : ∀ u, ncoord s β Y Z j u ω = f u - Real.exp (-lam * u) * y := fun u => rfl
  have hint1 : IntegrableOn f (Set.Icc 0 (t : ℝ)) := hfc.integrableOn_Icc
  have hint2 : IntegrableOn (fun u : ℝ => Real.exp (-lam * u) * y) (Set.Icc 0 (t : ℝ)) :=
    (Continuous.integrableOn_Icc (by fun_prop))
  have hexp : ∫ u in Set.Icc (0 : ℝ) t, Real.exp (-lam * u) * y = y * ((1 - Real.exp (-lam * t)) / lam) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
    have hd' : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun u => -(y / lam) * Real.exp (-lam * u))
        (Real.exp (-lam * x) * y) x := by
      intro x _
      have h1 : HasDerivAt (fun u : ℝ => -lam * u) (-lam) x := by
        simpa using (hasDerivAt_id x).const_mul (-lam)
      have := (h1.exp).const_mul (-(y / lam))
      convert this using 1
      field_simp [hlam.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd' (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [mul_zero, Real.exp_zero]
    field_simp [hlam.ne']
    ring
  have hsplit : ∫ u in Set.Icc (0 : ℝ) t, f u =
      (∫ u in Set.Icc (0 : ℝ) t, ncoord s β Y Z j u ω) + y * ((1 - Real.exp (-lam * t)) / lam) := by
    have : ∀ u, f u = ncoord s β Y Z j u ω + Real.exp (-lam * u) * y := fun u => by rw [hG]; ring
    simp_rw [this]
    rw [integral_add _ hint2, hexp]
    have h3 : IntegrableOn (fun u : ℝ => ncoord s β Y Z j u ω) (Set.Icc 0 (t : ℝ)) := by
      have := hint1.sub hint2
      refine this.congr_fun (fun u _ => ?_) measurableSet_Icc
      simp only [Pi.sub_apply, hG]
    exact h3
  have hσ0 := (sigmaMode_pos hβ j).ne'
  show f t = f 0 - lam * (∫ u in Set.Icc (0 : ℝ) t, f u) + sigmaMode β j * bmProc lam (sigmaMode β j)
    (fun t ω => ncoord s β Y Z j t ω) (t : ℝ) ω
  have hf0 : f 0 = y := by simp only [hf, hinit, hy]
  rw [hsplit, hf0]
  unfold bmProc
  have hf_t : f t = ncoord s β Y Z j t ω + Real.exp (-lam * t) * y := by rw [hG]; ring
  rw [hf_t]
  field_simp [hlam.ne']
  ring

end ModeBM

end Qch

end HRS
