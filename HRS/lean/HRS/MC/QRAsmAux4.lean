import HRS.MC.QRVocab
import HRS.MC.QRAsmAux3

/-!
# QRAsm, auxiliary file 4: the per-mode estimate (two Wick tails plus the low-frequency part)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.Asm

variable {Ω : Type} [MeasurableSpace Ω]

/-- The per-mode estimate.  `Q`, `Qs` are the `k`-th coefficients of `ℬ`, `ℬs`; `T`, `T'` bound the two Wick tails
(`Q - (finite section)` on the cube of side `L`); `H` bounds the entries of the common matrix `A`;
`Nδ, Nx, Ny` bound the `L^{2p}(E_r)` norms of `η-ηs`, `η`, `ηs`. -/
lemma asm_mode_bound {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {r : ℝ} (hr : 0 ≤ r) {p : ℝ}
    (hp : 1 ≤ p) (η ηs : Ω → NegSobolev d r) (hη : Measurable η) (hηs : Measurable ηs)
    (A : NonzeroLattice d → NonzeroLattice d → ℝ) (Q Qs : Ω → ℝ) (Nδ Nx Ny : ℝ)
    (hNδ0 : 0 ≤ Nδ) (hNx0 : 0 ≤ Nx) (hNy0 : 0 ≤ Ny)
    (hNδ : eLpNorm (fun ω => ‖η ω - ηs ω‖) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal Nδ)
    (hNx : eLpNorm (fun ω => ‖η ω‖) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal Nx)
    (hNy : eLpNorm (fun ω => ‖ηs ω‖) (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal Ny)
    (H : ℝ) (hH0 : 0 ≤ H) (hH : ∀ a b, |A a b| ≤ H) (L : ℕ) (hL : 1 ≤ L) (T T' : ℝ)
    (hT : 0 ≤ T) (hT' : 0 ≤ T')
    (h1 : eLpNorm (fun ω => Q ω - asmSec P A (fun a ω => NegSobolev.fourierCoeff (η ω) a)
      (asmCube d L) ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal T)
    (h2 : eLpNorm (fun ω => Qs ω - asmSec P A (fun a ω => NegSobolev.fourierCoeff (ηs ω) a)
      (asmCube d L) ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal T') :
    eLpNorm (fun ω => Q ω - Qs ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (T + T' +
      H * Nδ * (Nx + Ny) * (((3 : ℝ) ^ d * (1 + 2 * Real.pi * Real.sqrt d) ^ r) ^ 2 *
        (L : ℝ) ^ (2 * (d : ℝ) + 2 * r))) := by
  set w : NonzeroLattice d → ℝ := fun a => Lattice.jp a.1 ^ r with hw
  have hw0 : ∀ a, 0 ≤ w a := fun a => Real.rpow_nonneg (Torus.jp_pos a.1).le _
  have hηm' : ∀ a, AEStronglyMeasurable (fun ω => NegSobolev.fourierCoeff (η ω) a) P :=
    fun a => (asm_meas_fc hη a).aestronglyMeasurable
  have hηsm' : ∀ a, AEStronglyMeasurable (fun ω => NegSobolev.fourierCoeff (ηs ω) a) P :=
    fun a => (asm_meas_fc hηs a).aestronglyMeasurable
  have hsubm : Measurable fun ω => η ω - ηs ω := hη.sub hηs
  have hδ : ∀ a, eLpNorm (fun ω => NegSobolev.fourierCoeff (η ω) a - NegSobolev.fourierCoeff (ηs ω) a)
      (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal (w a * Nδ) := by
    intro a
    have := asm_fc_eLpNorm (fun ω => η ω - ηs ω) hsubm (ENNReal.ofReal (2 * p)) Nδ a hNδ
    simpa only [Marg.qm_fc_sub] using this
  have hξ : ∀ a, eLpNorm (fun ω => NegSobolev.fourierCoeff (η ω) a) (ENNReal.ofReal (2 * p)) P ≤
      ENNReal.ofReal (w a * Nx) := fun a => asm_fc_eLpNorm η hη _ Nx a hNx
  have hζ : ∀ a, eLpNorm (fun ω => NegSobolev.fourierCoeff (ηs ω) a) (ENNReal.ofReal (2 * p)) P ≤
      ENNReal.ofReal (w a * Ny) := fun a => asm_fc_eLpNorm ηs hηs _ Ny a hNy
  have key := asm_mode_gen (P := P) A (asmCube d L) (fun a ω => NegSobolev.fourierCoeff (η ω) a)
    (fun a ω => NegSobolev.fourierCoeff (ηs ω) a) hp hηm' hηsm' (fun a => w a * Nδ)
    (fun a => w a * Nx) (fun a => w a * Ny) (fun a => mul_nonneg (hw0 a) hNδ0)
    (fun a => mul_nonneg (hw0 a) hNx0) (fun a => mul_nonneg (hw0 a) hNy0) hδ hξ hζ Q Qs T T' hT hT'
    h1 h2
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  set c : ℝ := Nδ * (Nx + Ny) with hc
  have hc0 : 0 ≤ c := mul_nonneg hNδ0 (add_nonneg hNx0 hNy0)
  have hsum : ∑ a ∈ asmCube d L, ∑ b ∈ asmCube d L, |A a b| *
      (w a * Nδ * (w b * Nx) + w a * Ny * (w b * Nδ)) ≤ H * c * (∑ a ∈ asmCube d L, w a) ^ 2 := by
    calc _ ≤ ∑ a ∈ asmCube d L, ∑ b ∈ asmCube d L, H * (w a * w b * c) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          have e : w a * Nδ * (w b * Nx) + w a * Ny * (w b * Nδ) = w a * w b * c := by
            simp only [hc]; ring
          rw [e]
          exact mul_le_mul_of_nonneg_right (hH a b) (mul_nonneg (mul_nonneg (hw0 a) (hw0 b)) hc0)
      _ = H * c * (∑ a ∈ asmCube d L, w a) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
  have hZ := asm_sum_w_sq (d := d) hL hr
  have hHc : 0 ≤ H * c := mul_nonneg hH0 hc0
  calc T + T' + ∑ a ∈ asmCube d L, ∑ b ∈ asmCube d L, |A a b| *
        (w a * Nδ * (w b * Nx) + w a * Ny * (w b * Nδ))
      ≤ T + T' + H * c * (∑ a ∈ asmCube d L, w a) ^ 2 := by linarith
    _ ≤ T + T' + H * c * (((3 : ℝ) ^ d * (1 + 2 * Real.pi * Real.sqrt d) ^ r) ^ 2 *
          (L : ℝ) ^ (2 * (d : ℝ) + 2 * r)) := by
        have := mul_le_mul_of_nonneg_left hZ hHc
        linarith
    _ = _ := by simp only [hc]; ring

end HRS.MC.QRSpec.Asm

end
