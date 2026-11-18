import HRS.MC.S7PIM1b

/-!
# Packet piM, M2: `s7_PIM_eta_bdd_proof` (namespace `HRS.MC.Sec7.S7PIM`)

The statement is copied verbatim from `HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PIM_eta_bdd`); the tie is in
`HRS/MC/S7PIMTie.lean`.  The `E_r` path is `zr u = ofSeq r (√N (μ_N^{u^+}(e_k) - μ^u(e_k)))_k`, with the density set
to `0` at negative times (`s7fcw12_rhoPos`) so that `u ↦ zr u` is measurable on all of `ℝ`; its coefficients are bounded
by `2√2 √N`, hence `‖zr u‖ ≤ 2√2 √N (∑ ⟨k⟩^{-2(r-2)})^{1/2}`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIM

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.S7FCW12

variable {d : ℕ}

/-- The coefficients of `√N (μ_N^{u^+} - μ^u)` (with the density `0` at negative times). -/
def S7PIM_etaCoef (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (ω : Ω) (u : ℝ)
    (k : NonzeroLattice d) : ℝ :=
  Real.sqrt N * ((N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X u.toNNReal ω i) -
    Torus.measureRealCoeff (withDensityReal fun y => s7fcw12_rhoPos R (u, y)) k)

theorem S7PIM_etaCoef_eq (R : Regime d) (m : ℝ) {N : ℕ} (hN : 0 < N) {Ω : Type} (X : ℝ≥0 → Ω → Config d N)
    (ω : Ω) {u : ℝ} (hu : 0 ≤ u) :
    etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u)) = NegSobolev.ofSeq m (S7PIM_etaCoef R X ω u) := by
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hμ : withDensityReal (R.ρ u) = withDensityReal fun y => s7fcw12_rhoPos R (u, y) := by
    congr 1
    funext y
    rw [s7fcw12_rhoPos_eq R hu y]
  unfold etaE flucE NegSobolev.ofMeasureDiff S7PIM_etaCoef
  rw [hμ, ← s7fcw12_ofSeq_smul m hs]
  congr 1
  funext k
  unfold Torus.measureRealCoeff
  rw [integral_empirical _ (continuous_realMode' k)]

theorem S7PIM_etaCoef_bound (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (ω : Ω) {u : ℝ}
    (hu : 0 ≤ u) (k : NonzeroLattice d) :
    |S7PIM_etaCoef R X ω u k| ≤ 2 * Real.sqrt 2 * Real.sqrt N * Lattice.jp k.1 ^ 2 := by
  have hρ : IsProbDensity (R.ρ u) := (R.mf (u + 1) (by linarith)).density u ⟨hu, by linarith⟩
  haveI : IsProbabilityMeasure (withDensityReal (R.ρ u)) := HRS.isProb_withDensityReal hρ
  have hμ : withDensityReal (R.ρ u) = withDensityReal fun y => s7fcw12_rhoPos R (u, y) := by
    congr 1
    funext y
    rw [s7fcw12_rhoPos_eq R hu y]
  have h1 := s7fcw12_abs_sum_le k (X u.toNNReal ω)
  have h2 := NegSobolev.abs_measureRealCoeff_le (withDensityReal (R.ρ u)) k
  simp only [measure_univ, ENNReal.toReal_one, mul_one] at h2
  rw [hμ] at h2
  have hj : 1 ≤ Lattice.jp k.1 ^ 2 := one_le_pow₀ (Torus.jp_ge_one _)
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  unfold S7PIM_etaCoef
  rw [abs_mul, abs_of_nonneg hs0]
  have h3 : |(N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X u.toNNReal ω i) -
      Torus.measureRealCoeff (withDensityReal fun y => s7fcw12_rhoPos R (u, y)) k| ≤ 2 * Real.sqrt 2 :=
    (abs_sub _ _).trans (by linarith)
  have h4 : Real.sqrt N * (2 * Real.sqrt 2) ≤ 2 * Real.sqrt 2 * Real.sqrt N * Lattice.jp k.1 ^ 2 := by
    have : 0 ≤ 2 * Real.sqrt 2 * Real.sqrt N := by positivity
    nlinarith
  exact (mul_le_mul_of_nonneg_left h3 hs0).trans h4

theorem S7PIM_etaCoef_meas (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    (hω : ∀ i, Continuous fun t : ℝ≥0 => X t ω i) (k : NonzeroLattice d) :
    Measurable fun u : ℝ => S7PIM_etaCoef R X ω u k := by
  unfold S7PIM_etaCoef
  refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) ?_)
  · refine Finset.measurable_sum _ fun i _ => ?_
    exact ((continuous_realMode' k).comp ((hω i).comp continuous_real_toNNReal)).measurable
  · unfold Torus.measureRealCoeff
    exact s7fcw12_meas_density_integral (fun u y => s7fcw12_rhoPos R (u, y))
      (s7fcw12_rhoPos_measurable R) (fun _ y => Torus.realMode k y)
      ((continuous_realMode' k).measurable.comp measurable_snd)

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

theorem s7_PIM_eta_bdd_proof :
    ∃ M : ℝ, ∀ᵐ ω ∂P, ∃ zr : ℝ → NegSobolev d (2 * (d : ℝ) + 6), Measurable zr ∧
      (∀ u ∈ Set.Icc (0 : ℝ) T, ‖zr u‖ ≤ M) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) T, etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u)) =
        NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) := by
  have hS := hreal.solution T
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr : (d : ℝ) < 2 * (2 * (d : ℝ) + 6 - 2) := by linarith
  have hN0 : 0 < N := hN
  refine ⟨|2 * Real.sqrt 2 * Real.sqrt N| *
    Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (2 * (d : ℝ) + 6 - 2)))), ?_⟩
  filter_upwards [hS.cont] with ω hω
  refine ⟨fun u => NegSobolev.ofSeq (2 * (d : ℝ) + 6) (S7PIM_etaCoef R X ω u),
    s7fcw12_measurable_ofSeq _ (S7PIM_etaCoef_meas R X ω hω), fun u hu => ?_, fun u hu => ?_⟩
  · exact S7PIM_ofSeq_norm_le hr _ _ (S7PIM_etaCoef_bound R X ω hu.1)
  · rw [S7PIM_etaCoef_eq R m hN0 X ω hu.1]
    congr 1
    funext k
    have hmem := S7PIM_ofSeq_mem hr _ _ (S7PIM_etaCoef_bound R X ω hu.1)
    unfold NegSobolev.fourierCoeff
    rw [NegSobolev.coord_ofSeq_of_mem _ hmem k, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp

end Prob

end HRS.MC.Sec7.S7PIM

end
