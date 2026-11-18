import HRS.MS.SpecAux22
import HRS.MS.MovLinAux9
import HRS.MS.Mov63Aux1

/-!
# S8P: `Σ^∞ ⊂ 𝒮` (S8.7, packet E4b)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_schwartz_of_memOsc`: if `f ∈ Σ^m` for every `m : ℕ` (`d ≥ 1`), then `f` is
a.e. equal to a Schwartz function.  The continuous representative `ψ` is the limit of the Hermite partial sums in `C_b^J` for every
`J` (`s8p_osc_smooth_conv`); the weighted derivative bounds `‖x‖^k ‖D^n ψ(x)‖ ≤ C ‖f‖_{Σ^N}` pass to the limit from
`mov2d_seminorm_osc` applied to the (Schwartz) partial sums, whose `Σ^N` norms are at most `‖f‖_{Σ^N}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovLin

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_schwartz_of_memOsc (hd : 1 ≤ d) {f : Euc d → ℝ} (hf : ∀ m : ℕ, MemOsc (m : ℝ) f) :
    ∃ φ : 𝓢R, f =ᵐ[volume] ⇑φ := by
  have hex : ∀ J : ℕ, ∃ ψ' : Euc d → ℝ, ContDiff ℝ J ψ' ∧ ψ' =ᵐ[volume] f ∧ ∀ k ≤ J, ∀ x : Euc d,
      Tendsto (fun n : ℕ => iteratedFDeriv ℝ k (mo_pSum f n) x) atTop (𝓝 (iteratedFDeriv ℝ k ψ' x)) := by
    intro J
    obtain ⟨ψ', h1, -, h3, h4⟩ := s8p_osc_smooth_conv hd J (m := ((J + 2 * d + 1 : ℕ) : ℝ))
      (by push_cast; linarith) (hf (J + 2 * d + 1))
    exact ⟨ψ', h1, h3, h4⟩
  choose g hgc hga hgt using hex
  have hcont : ∀ J, Continuous (g J) := fun J => (hgc J).continuous
  have hg0 : ∀ J, g J = g 0 := fun J =>
    (Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) (hcont J) (hcont 0)).1 ((hga J).trans (hga 0).symm)
  have hsmooth : ContDiff ℝ ∞ (g 0) := by
    rw [contDiff_infty]
    intro J
    have := hgc J
    rwa [hg0 J] at this
  have hconv : ∀ k : ℕ, ∀ x : Euc d,
      Tendsto (fun n : ℕ => iteratedFDeriv ℝ k (mo_pSum f n) x) atTop (𝓝 (iteratedFDeriv ℝ k (g 0) x)) := by
    intro k x
    have := hgt k k le_rfl x
    rwa [hg0 k] at this
  have hdecay : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : Euc d, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g 0) x‖ ≤ C := by
    intro k n
    obtain ⟨C, N, hC0, hC⟩ := mov2d_seminorm_osc (d := d) k n
    refine ⟨C * oscNorm (N : ℝ) f, fun x => ?_⟩
    have hb : ∀ n' : ℕ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (mo_pSum f n') x‖ ≤ C * oscNorm (N : ℝ) f := by
      intro n'
      obtain ⟨φ, hφ⟩ := HRS.MS.Mov63.mn_pSum_schwartz f n'
      have h1 := hC φ x
      rw [hφ] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      exact (mo_pSum_oscNorm_le (N : ℝ) (hf N) n').2
    have hlim : Tendsto (fun n' : ℕ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (mo_pSum f n') x‖) atTop
        (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g 0) x‖)) :=
      tendsto_const_nhds.mul (hconv n x).norm
    exact le_of_tendsto' hlim hb
  refine ⟨⟨g 0, hsmooth, hdecay⟩, ?_⟩
  exact (hga 0).symm

end HRS.MS.Spec
