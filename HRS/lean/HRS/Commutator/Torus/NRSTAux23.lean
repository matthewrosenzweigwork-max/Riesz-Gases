import HRS.Commutator.Torus.NRSTAux22

/-!
# NRS-T, part 23: Fourier support of the cut-off lift
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_summable (f : NRST.TPA d) : Summable fun k : Lattice d => ‖f.coeff k‖ := by
  classical
  refine summable_of_ne_finset_zero (s := f.coeff.support) fun k hk => ?_
  have : f.coeff k = 0 := by simpa using hk
  simp [this]

lemma nrstr_fourierW (f : NRST.TPA d) {N : ℝ} (hN : 0 < N) (ξ : 𝔼) :
    HasSum (fun k : Lattice d => f.coeff k * (((N ^ d : ℝ) : ℂ) *
      nrstr_theta0 (d := d) (N • (ξ - Lattice.toEuc k)))) (𝓕 (⇑(nrstr_W f N hN)) ξ) := by
  have h := leibt_series_fourier (nrstr_phi (d := d)) hN (fun k : Lattice d => f.coeff k)
    (fun k => Lattice.toEuc k) (nrstr_summable f) (nrstr_W f N hN) (nrstr_W_hasSum f N hN) ξ
  rw [fourier_nrstr_phi] at h
  exact h

/-- The Fourier transform of the lift is supported in the `1/8`-neighbourhood of the frequencies. -/
lemma nrstr_fourierW_zero (f : NRST.TPA d) {N : ℝ} (hN : 1 ≤ N) (ξ : 𝔼)
    (hξ : ∀ k ∈ f.coeff.support, 1 / 8 ≤ ‖ξ - Lattice.toEuc k‖) :
    𝓕 (⇑(nrstr_W f N (by linarith))) ξ = 0 := by
  classical
  have hN0 : 0 < N := by linarith
  have h := nrstr_fourierW f hN0 ξ
  have : 𝓕 (⇑(nrstr_W f N hN0)) ξ = ∑ k ∈ f.coeff.support, f.coeff k * (((N ^ d : ℝ) : ℂ) *
      nrstr_theta0 (d := d) (N • (ξ - Lattice.toEuc k))) := by
    refine h.unique ?_
    refine hasSum_sum_of_ne_finset_zero (fun k hk => ?_)
    have : f.coeff k = 0 := by simpa using hk
    simp [this]
  rw [this]
  refine Finset.sum_eq_zero fun k hk => ?_
  have h1 : (1 / 8 : ℝ) ≤ ‖N • (ξ - Lattice.toEuc k)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hN0]
    calc (1 / 8 : ℝ) ≤ ‖ξ - Lattice.toEuc k‖ := hξ k hk
      _ = 1 * ‖ξ - Lattice.toEuc k‖ := (one_mul _).symm
      _ ≤ N * ‖ξ - Lattice.toEuc k‖ := by gcongr
  rw [nrstr_theta0_zero_of_far h1]
  simp

end HRS.Commutator.TorusNote
