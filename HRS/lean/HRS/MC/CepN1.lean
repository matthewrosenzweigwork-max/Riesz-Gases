import HRS.MC.CepN1Aux9
import HRS.Dynamics.Setup

/-!
# Packet CEPN1: Brownian tube (positivity of small tube probabilities)

Relocated proof of `HRS.MC.Cepa.cep_N1_bm_tube` (frozen in `HRS/MC/CepaSpec.lean`); the tie is in
`HRS/MC/CepN1Tie.lean`.

Route (no Cameron-Martin, no reflection principle, no Itô): approximate the target by a Lipschitz
function `g`; cut `[0,T']` into `M` pieces of length `h`; on each piece require that the increment tracks
the increment of `g` within `ε` and that the path stays within `ρ` on the dyadic grid (Kolmogorov/Doob
maximal inequality gives `P(sup > ρ) ≤ h/ρ²`, Gaussian density gives `P(increment) ≳ ε/√h`; for `h` small
the second beats the first); the weak Markov property multiplies the piece probabilities; independent
coordinates multiply.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN1

open HRS

theorem cepn1_tube1D {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0)
    {T' η : ℝ} (hT' : 0 < T') (hη : 0 < η) :
    ∃ S : Set (ℝ≥0 → ℝ), MeasurableSet S ∧ 0 < P ((fun ω t => B t ω) ⁻¹' S) ∧
      ∀ z ∈ S, Continuous z → ∀ t : ℝ≥0, (t : ℝ) ≤ T' → |z t - f t| < η := by
  obtain ⟨g, L, hL, hg0, hgL, hgf⟩ := cepn1_lip_approx hf hf0 hT' (half_pos hη)
  obtain ⟨S, hS, hpos, hSb⟩ := cepn1_oneD hB hg0 hL hgL hT' hη
  refine ⟨S, hS, hpos, fun z hz hzc t ht => ?_⟩
  have h1 := hSb z hz hzc t ht
  have h2 := hgf t ht
  calc |z t - f t| = |(z t - g t) + (g t - f t)| := by ring_nf
    _ ≤ |z t - g t| + |g t - f t| := abs_add_le _ _
    _ < η := by linarith

theorem cepn1_norm_euc1 (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cep_N1_bm_tube_proof [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    (hW : IsVectorBrownian P W)
    {w : ℝ → Fin N → Euc 1} (hw : Continuous w) (hw0 : w 0 = 0) {T' η : ℝ} (hT' : 0 < T') (hη : 0 < η) :
    0 < P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T' → ‖W t ω - w t‖ < η} := by
  -- coordinatewise targets
  have hfc : ∀ i : Fin N, Continuous fun x : ℝ => w x i 0 := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp ((continuous_apply i).comp hw)
  have hf0 : ∀ i : Fin N, w 0 i 0 = 0 := fun i => by simp [hw0]
  have hS := fun i : Fin N => cepn1_tube1D (P := P) (hW.1 i 0).toIsPreBrownianReal (hfc i) (hf0 i) hT' hη
  choose S hSm hSpos hSb using hS
  have hj : ∀ j : Fin 1, j = 0 := fun j => Subsingleton.elim _ _
  have hind := hW.2.measure_inter_preimage_eq_mul (Finset.univ : Finset (Fin N × Fin 1))
    (sets := fun ij => S ij.1) (fun ij _ => hSm ij.1)
  have hprod : 0 < ∏ ij ∈ (Finset.univ : Finset (Fin N × Fin 1)),
      P ((fun ω (t : ℝ≥0) => W t ω ij.1 ij.2) ⁻¹' S ij.1) := by
    refine pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun ij _ => ?_)
    obtain ⟨i, j⟩ := ij
    obtain rfl := hj j
    exact (hSpos i).ne'
  have hcont : ∀ᵐ ω ∂P, ∀ i : Fin N, Continuous fun t : ℝ≥0 => W t ω i 0 :=
    ae_all_iff.2 fun i => (hW.1 i 0).cont
  refine lt_of_lt_of_le (hind ▸ hprod) (measure_mono_ae ?_)
  filter_upwards [hcont] with ω hc hmem t ht
  rw [pi_norm_lt_iff hη]
  intro i
  have hmem' : (fun t : ℝ≥0 => W t ω i 0) ∈ S i := by
    have := Set.mem_iInter₂.1 hmem (i, 0) (Finset.mem_univ _)
    exact this
  have := hSb i _ hmem' (hc i) t ht
  rw [cepn1_norm_euc1]
  simpa using this

end HRS.MC.CepN1
