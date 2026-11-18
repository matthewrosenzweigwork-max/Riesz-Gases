import HRS.MC.S7FCDefs
import HRS.MC.S7FCA

/-!
# S7FCH1A: particle side of a finite-rank field (`s7_FC_H1a_particle`)

Proof of `HRS.MC.Sec7.FCPlan.s7_FC_H1a_particle` (statement copied verbatim from `HRS/MC/S7FCPlan.lean`; the tie
is `HRS/MC/S7FCH1Tie.lean`).  Route: the exact finite-rank identity `HRS.MC.Sec7.FCA.s7_FC_A_finite_rank_identity_proof`
(FC-A) for the kernel `K.toFun = ∑ c_ij f_i ⊗ f_j`, with `K.c` symmetric (`K.symm`) and smooth `K.f i`
(hence bounded, measurable, continuous with absolutely summable Fourier coefficients); and the evaluation
`NegSobolev.eval (etaE r X μ) (K.f i) = √N (μ_N(f_i) - μ(f_i))` from `NegSobolev.eval_ofMeasureDiff_of_summable`
(needs `d < 2r`, which holds for `r = 2d + 6`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH1

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-- A `C^∞` function on the torus is continuous and has absolutely summable Fourier coefficients. -/
theorem S7FCH1_smooth_props {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous φ ∧ Summable (fun k : Lattice d => ‖Torus.fcoef φ k‖) := by
  have hC : Torus.IsCk ((⊤ : ℕ∞) : WithTop ℕ∞) φ := hφ
  have hd : ∀ n : ℕ, ContDiff ℝ n (Torus.lift φ) := fun n => hC.of_le (by exact_mod_cast le_top)
  exact ⟨Torus.continuous_of_continuous_lift (hd 0).continuous, Torus.summable_fcoef_of_contDiff hd⟩

/-- A continuous function on the (compact) torus is bounded. -/
theorem S7FCH1_bounded {φ : Torus d → ℝ} (hc : Continuous φ) : ∃ M, ∀ x, |φ x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM x (Set.mem_univ x)⟩

/-- Coefficientwise scalar multiplication in `E_m`. -/
theorem S7FCH1_fourierCoeff_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (c • F) k = c * NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.fourierCoeff
  have h : NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl
  rw [h]; ring

/-- Pairing is linear in the scalar: `(c • F)(φ) = c F(φ)`. -/
theorem S7FCH1_eval_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (c • F) φ = c * NegSobolev.eval F φ := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [S7FCH1_fourierCoeff_smul]; ring

/-- **H1a (particle side of a finite-rank field)**: for smooth finite-rank symmetric `K` and any probability `μ`,
`N F_N^K(X, μ) = Φ_K(η_N) - ½ ∑ c_ij μ_N(f_i f_j)` exactly. -/
theorem s7_FC_H1a_particle_proof {N : ℕ} (hN : 1 ≤ N) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (K : FRKernel d) (X : Config d N) :
    (N : ℝ) * modulatedEnergy K.toFun X μ =
      K.quad (etaE r X μ) - (1 / 2) * ∑ i, ∑ j, K.c i j *
        pair (empirical X) (fun x => K.f i x * K.f j x) := by
  have hsm : ∀ i, Continuous (K.f i) ∧ Summable (fun k : Lattice d => ‖Torus.fcoef (K.f i) k‖) :=
    fun i => S7FCH1_smooth_props (K.smooth i)
  have hid := HRS.MC.Sec7.FCA.s7_FC_A_finite_rank_identity_proof hN μ K.f
    (fun i => (hsm i).1.measurable) (fun i => S7FCH1_bounded (hsm i).1) K.c K.symm X
  have hm : (d : ℝ) < 2 * r := by
    rw [hr]
    have h0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure (by omega) X
  have hev : ∀ i, NegSobolev.eval (etaE r X μ) (K.f i) =
      Real.sqrt N * (pair (empirical X) (K.f i) - pair μ (K.f i)) := by
    intro i
    unfold etaE flucE
    rw [S7FCH1_eval_smul, NegSobolev.eval_ofMeasureDiff_of_summable hm (empirical X) μ (K.f i) (hsm i).1 (hsm i).2]
  have hquad : HRS.MC.Sec7.FCPlan.FRKernel.quad K (etaE r X μ) = (1 / 2) * ∑ a, ∑ b, K.c a b *
      (Real.sqrt N * (pair (empirical X) (K.f a) - pair μ (K.f a))) *
      (Real.sqrt N * (pair (empirical X) (K.f b) - pair μ (K.f b))) := by
    unfold HRS.MC.Sec7.FCPlan.FRKernel.quad
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hev a, hev b]; ring
  rw [hquad]
  exact hid

end HRS.MC.Sec7.S7FCH1

end
