import HRS.MC.QRVocab
import HRS.MC.QRPMargAux1

/-!
# QRPMarg, helper 2: evaluation against a smooth test function is a continuous linear functional of `E_m`
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HRS.MC.QRSpec.Marg

variable {d : ℕ}

/-- `F ↦ F(ψ)` is a continuous linear functional on `E_m` for a test function `ψ` with finite `H^m` mass. -/
theorem qm_evCLM (m : ℝ) (ψ : Torus d → ℝ)
    (hψ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2) :
    ∃ ℓ : StrongDual ℝ (NegSobolev d m), ∀ F, ℓ F = NegSobolev.eval F ψ := by
  have hS : Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k) ^ 2 := by
    refine hψ.congr fun k => ?_
    rw [mul_pow, Torus.jp_rpow_sq]
  let yL : lp (fun _ : NonzeroLattice d => ℝ) 2 :=
    ⟨fun k => Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k, (Torus.memℓp_two_iff _).2 hS⟩
  let y : NegSobolev d m := yL
  refine ⟨innerSL ℝ y, fun F => ?_⟩
  change inner ℝ yL (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) = _
  rw [lp.inner_eq_tsum]
  unfold NegSobolev.eval NegSobolev.fourierCoeff
  refine tsum_congr fun k => ?_
  simp only [yL, RCLike.inner_apply, conj_trivial]
  change _ * (Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k) = _
  unfold NegSobolev.coord
  ring

/-- `F(e_k) = F̂(k)` for the real Fourier mode `e_k`. -/
theorem qm_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal k k]
    simp
  · intro l hl
    unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal l k, if_neg hl]
    simp

theorem qm_fc_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F - G) k = NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff NegSobolev.coord
  rw [← mul_sub]; rfl

end HRS.MC.QRSpec.Marg

end
