import HRS.Uniform.Q54cAux52
import HRS.PDE.MeanFieldLinearLoss
import HRS.PDE.MeanFieldAprioriUpper
import HRS.PDE.MeanFieldPairing
import HRS.PDE.KernelInputsD1
import HRS.PDE.MeanFieldPairSeries
import HRS.Kernel.GradReg

/-!
# Q54c, part 53: measurability in time of a path of `C^{d+1}` densities from its real Fourier modes
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

theorem summable_fcoef_of_ck {φ : Torus d → ℝ} (hd : ContDiff ℝ ((d + 1 : ℕ) : WithTop ℕ∞) (Torus.lift φ)) :
    Summable fun k : Lattice d => ‖Torus.fcoef φ k‖ := by
  obtain ⟨B, hB⟩ := Torus.fcoef_pow_decay (n := d + 1) hd
  rw [Torus.summable_lattice_iff]
  have hs := summable_jp_rpow (d := d) (((d + 1 : ℕ) : ℝ) / 2)
    (by push_cast; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hs.mul_left B)
  have hj := Torus.jp_pos k.1
  have e : Lattice.jp k.1 ^ (-(2 * (((d + 1 : ℕ) : ℝ) / 2))) = (Lattice.jp k.1 ^ (d + 1))⁻¹ := by
    rw [show -(2 * (((d + 1 : ℕ) : ℝ) / 2)) = -((d + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hj.le,
      Real.rpow_natCast]
  rw [e]
  have := hB k
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hj _)]
  exact this

theorem isCk_realMode (k : NonzeroLattice d) (L : ℕ) : Torus.IsCk (L : WithTop ℕ∞) (Torus.realMode k) := by
  unfold Torus.realMode
  by_cases h : Lattice.IsPosHalf k.1
  · simp only [h, ite_true]
    exact HRS.PDE.MFPair.isCk_const_mul_ps (HRS.PDE.MFPair.isCk_cos_ps k.1 L) _
  · simp only [h, ite_false]
    exact HRS.PDE.MFPair.isCk_const_mul_ps (HRS.PDE.MFPair.isCk_sin_ps k.1 L) _

/-- pointwise measurability in time from the measurability of the real Fourier modes -/
theorem measurable_pt_of_modes (ρ : ℝ → Torus d → ℝ) (hc : ∀ r, Continuous (ρ r))
    (hs : ∀ r, Summable fun k : Lattice d => ‖Torus.fcoef (ρ r) k‖) (hmean : ∀ r, Torus.mean (ρ r) = 1)
    (hmk : ∀ k : NonzeroLattice d, Measurable fun r => ∫ x, Torus.realMode k x * ρ r x) (x : Torus d) :
    Measurable fun r => ρ r x := by
  have hexp : ∀ r, HasSum (fun k : NonzeroLattice d => (∫ y, Torus.realMode k y * ρ r y) * Torus.realMode k x)
      (ρ r x - 1) := by
    intro r
    have := Torus.hasSum_realExpansion (hc r) (hs r) x
    rw [hmean r] at this
    exact this
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (NonzeroLattice d)))
    (f := fun s r => 1 + ∑ k ∈ s, (∫ y, Torus.realMode k y * ρ r y) * Torus.realMode k x) ?_ ?_
  · intro s
    exact measurable_const.add (Finset.measurable_sum _ fun k _ => (hmk k).mul measurable_const)
  · refine tendsto_pi_nhds.2 fun r => ?_
    have h3 : Tendsto (fun s : Finset (NonzeroLattice d) =>
        1 + ∑ k ∈ s, (∫ y, Torus.realMode k y * ρ r y) * Torus.realMode k x) atTop (𝓝 (1 + (ρ r x - 1))) :=
      tendsto_const_nhds.add (hexp r)
    simpa using h3

end HRS.Uniform.Q54c
