import HRS.MS.Fp81S21ParticleSixthSlices
import HRS.MS.R2S11Aux5

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole
open HRS.MS.R26T3

/-- A finite-rank kernel together with the smooth compactly supported symmetric data
that define it. -/
structure fp81s21_RankKernel (d : ℕ) where
  n : ℕ
  c : Fin n → Fin n → ℝ
  u : Fin n → Euc d → ℝ
  valid : IsR2FiniteRankData c u

/-- The kernel represented by `fp81s21_RankKernel`. -/
def fp81s21_RankKernel.kernel {d : ℕ} (D : fp81s21_RankKernel d) :
    Euc d → Euc d → ℝ := r2FiniteRankKernel D.c D.u

/-- Center a vector-valued random variable by its Bochner mean. -/
def fp81s21_center {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V]
    (P : Measure Ω) (f : Ω → V) (ω : Ω) : V :=
  f ω - ∫ ω', f ω' ∂P

/-- Mean-square error, including the integrability required for the real integral. -/
def fp81s21_SqErr {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
    (P : Measure Ω) (f g : Ω → V) (ε : ℝ) : Prop :=
  Integrable (fun ω => ‖f ω - g ω‖ ^ 2) P ∧
    (∫ ω, ‖f ω - g ω‖ ^ 2 ∂P) ≤ ε ^ 2

/-- The particle quadratic statistic formed from a pair kernel and centered under its
actual realization law. -/
def fp81s21_particleQuad {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {N : ℕ} (A : Particle R N) (u : ℝ)
    (h : Euc p.d → Euc p.d → ℝ) : A.Ω → ℝ :=
  fp81s21_center A.P
    (fun ω => (N : ℝ) * pairEnergy h (A.X u.toNNReal ω) (r26t3_mu R u))

/-- The definition of `r2QuadField` is exactly the centered particle statistic for
the commutator kernel, including the actual expectation under `A.P`. -/
theorem fp81s21_particleQuad_commutator_eq
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) (u : ℝ) (ω : A.Ω) (f : Euc p.d → ℝ) :
    fp81s21_particleQuad A u
        (commutatorKernel p.d p.s (fun x => gradient f x)) ω =
      r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f := by
  change (N : ℝ) * pairEnergy
      (commutatorKernel p.d p.s (fun x => gradient f x))
      (A.X u.toNNReal ω) (r26t3_mu R u) -
      ∫ ω', (N : ℝ) * pairEnergy
        (commutatorKernel p.d p.s (fun x => gradient f x))
        (A.X u.toNNReal ω') (r26t3_mu R u) ∂A.P =
    (N : ℝ) * (pairEnergy
        (commutatorKernel p.d p.s (fun x => gradient f x))
        (A.X u.toNNReal ω) (r26t3_mu R u) -
      ∫ ω', pairEnergy
        (commutatorKernel p.d p.s (fun x => gradient f x))
        (A.X u.toNNReal ω') (r26t3_mu R u) ∂A.P)
  rw [integral_const_mul]
  ring

/-- Package the compiled S11 uniform velocity approximation with explicit finite-rank
data for each velocity and approximation index. -/
theorem fp81s21_rankKernel_velocity_approx
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
      ∃ B C : ℝ,
      0 ≤ B ∧ 0 ≤ C ∧
      IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
        (fun θ => commutatorKernel p.d p.s θ.1)
        (fun θ k => (D θ k).kernel) := by
  obtain ⟨B, C₂, hj, _hbounded, happrox⟩ :=
    HRS.MS.R2S11.s11_velocity_uniform_approx p.hd p.hs0 p.hs p.ha p.hβ
      R.thermal Λ
  choose n c u hvalid hkernel using happrox.finiteRank
  let D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d :=
    fun θ k => ⟨n θ k, c θ k, u θ k, hvalid θ k⟩
  let C : ℝ := max C₂ 0
  have hB : 0 ≤ B := by
    let θ0 : HRS.MS.R2S11.s11V p.d Λ :=
      ⟨fun _ => 0, ⟨contDiff_const, by simp [cbNormVecE]⟩⟩
    have hdp : 0 < p.d := lt_of_lt_of_le (by decide : 0 < 2) p.hd
    letI : NeZero p.d := ⟨Nat.ne_of_gt hdp⟩
    letI : Nontrivial (Euc p.d) := inferInstance
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Euc p.d)
    have hz : commutatorKernel p.d p.s θ0.1 x y = 0 := by
      simp [θ0, commutatorKernel]
    have hbound := (_hbounded θ0).bound x y hxy
    rw [hz, abs_zero] at hbound
    have hweight : 0 < 1 + rieszWeight p.s (x - y) := by
      have hw := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y)
      linarith
    nlinarith
  refine ⟨D, B, C, ?_, ?_, ?_⟩
  · exact hB
  · dsimp [C]
    exact le_max_right _ _
  · refine ⟨?_, ?_, ?_⟩
    · intro θ k
      refine ⟨n θ k, c θ k, u θ k, hvalid θ k, ?_⟩
      rfl
    · intro θ k x y hxy
      have h := happrox.envelope θ k x y hxy
      have hEq : (D θ k).kernel = hj θ k := by
        dsimp [D, fp81s21_RankKernel.kernel]
        exact (hkernel θ k).symm
      rw [hEq]
      have hcoeff : C₂ * B ≤ C * B :=
        mul_le_mul_of_nonneg_right (le_max_left C₂ 0) hB
      exact h.trans (mul_le_mul_of_nonneg_right hcoeff (by
        have hw := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y)
        linarith))
    · intro r hr hrs
      have hconv := happrox.converges r hr hrs
      simpa [D, fp81s21_RankKernel.kernel, hkernel] using hconv

#print axioms fp81s21_particleQuad_commutator_eq
#print axioms fp81s21_rankKernel_velocity_approx

end HRS.Fp81.S21
