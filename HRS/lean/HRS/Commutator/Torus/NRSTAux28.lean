import HRS.Commutator.Torus.NRSTAux27
import HRS.Commutator.Whole.XBBAux5

/-!
# NRS-T, part 28: a compactly supported smooth Riesz symbol agreeing with `i ξ_a/|ξ|` on an annulus
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Bump `=1` on `‖ξ‖ ≤ 1/4`, `0` for `‖ξ‖ ≥ 1/2`. -/
def nrstr_b1 (d : ℕ) : ContDiffBump (0 : 𝔼) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- Bump `=1` on `‖ξ‖ ≤ R`, `0` for `‖ξ‖ ≥ 2R`. -/
def nrstr_b2 (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : 𝔼) := ⟨R, 2 * R, hR, by linarith⟩

lemma nrstr_riesz_contDiffAt (a : Fin d) (η : 𝔼) (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ (fun η : 𝔼 => HRS.Commutator.Whole.XBB.xbbRm a η) η := by
  have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
  have h1 : ContDiffAt ℝ ∞ (fun η : 𝔼 => (η a : ℝ)) η :=
    ((EuclideanSpace.proj a : 𝔼 →L[ℝ] ℝ).contDiff).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun η : 𝔼 => ‖η‖) η := contDiffAt_norm ℝ hη
  unfold HRS.Commutator.Whole.XBB.xbbRm
  exact contDiffAt_const.mul
    ((Complex.ofRealCLM.contDiff.contDiffAt).comp η (h1.div h2 hn.ne'))

lemma nrstr_theta_exists (hd : 1 ≤ d) (a : Fin d) {R : ℝ} (hR : 1 ≤ R) :
    ∃ θ : 𝔼 → ℂ, θ.HasTemperateGrowth ∧
      ∀ ξ : 𝔼, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ R → θ ξ = HRS.Commutator.Whole.XBB.xbbRm a ξ := by
  have hR0 : 0 < R := by linarith
  set b1 := nrstr_b1 d with hb1
  set b2 := nrstr_b2 R hR0 (d := d) with hb2
  set cut : 𝔼 → ℝ := fun ξ => (1 - b1 ξ) * b2 ξ with hcut
  set θ : 𝔼 → ℂ := fun ξ => HRS.Commutator.Whole.XBB.xbbRm a ξ * ((cut ξ : ℝ) : ℂ) with hθ
  have hcutsm : ContDiff ℝ ∞ cut := (contDiff_const.sub b1.contDiff).mul b2.contDiff
  have hsm : ContDiff ℝ ∞ θ := by
    refine HRS.Commutator.Whole.cmxMY_contDiff_of_away_real (r := 1 / 4) (by norm_num) (fun η hη => ?_) (fun η hη => ?_)
    · exact (nrstr_riesz_contDiffAt a η hη).mul
        ((Complex.ofRealCLM.contDiff.comp hcutsm).contDiffAt)
    · have : b1 η = 1 := b1.one_of_mem_closedBall (by
        simpa [hb1, nrstr_b1, mem_closedBall_zero_iff] using hη.le)
      simp [hθ, hcut, this]
  have hcs : HasCompactSupport θ := by
    have : HasCompactSupport (fun ξ : 𝔼 => ((cut ξ : ℝ) : ℂ)) := by
      have h2 : HasCompactSupport (fun ξ : 𝔼 => b2 ξ) := b2.hasCompactSupport
      have h3 : HasCompactSupport cut := h2.mul_left
      exact h3.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
    exact this.mul_left
  refine ⟨θ, hcs.hasTemperateGrowth hsm, fun ξ h1 h2 => ?_⟩
  have e1 : b1 ξ = 0 := b1.zero_of_le_dist (by
    simpa [hb1, nrstr_b1, dist_zero_right] using h1)
  have e2 : b2 ξ = 1 := b2.one_of_mem_closedBall (by
    simpa [hb2, nrstr_b2, mem_closedBall_zero_iff] using h2)
  simp [hθ, hcut, e1, e2]

end HRS.Commutator.TorusNote
