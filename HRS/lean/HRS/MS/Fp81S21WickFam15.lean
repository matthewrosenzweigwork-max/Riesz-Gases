import HRS.MS.Fp81S21WickFam14

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- The finite-rank oscillator half-Wick polynomial has a continuous L² class. -/
theorem fp81s21_wickFam_oscillator_polynomial_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (G : GaussianRealization R)
    (T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P)
    (hJoint : ∀ u : ℝ, 0 ≤ u → ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
      HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω))
    (hag : ∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
      (T u (hφ.toLp φ) : G.Ω → ℝ) =ᵐ[G.P] fun ω => OscDual.eval (G.Z u ω) φ)
    (hcont : ∀ f, ContinuousOn (fun u => T u f) (Ici (0 : ℝ)))
    {n : ℕ} (φ : Fin n → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i))
    (hφLp : ∀ i, MemLp (φ i) 2 (HRS.Whole.withDensityReal R.ρβ))
    (c : Fin n → Fin n → ℝ) :
    ∃ W : ℝ → Lp ℝ 2 G.P, ContinuousOn W (Ici (0 : ℝ)) ∧
      ∀ u : ℝ, 0 ≤ u → (W u : G.Ω → ℝ) =ᵐ[G.P]
        fp81s21_wickG_finite_rank_polynomial (T u) φ hφLp c := by
  classical
  let ex (i : Fin n) := fp81s21_wickFam_oscillator_L4_continuous p R G T (φ i) (hφ i) (hφLp i)
    hJoint (fun u hu => hag u hu (φ i) (hφ i) (hφLp i)) (hcont ((hφLp i).toLp (φ i)))
  let F := fun i : Fin n => Classical.choose (ex i)
  have hF (i : Fin n) := Classical.choose_spec (ex i)
  obtain ⟨W, hW, hWa⟩ := fp81s21_wickFam_polynomial_L4_continuous G.P (Ici (0 : ℝ))
    F (fun i => (hF i).1) c
  refine ⟨W, hW, ?_⟩
  intro u hu
  have heq (i : Fin n) : (F i u : G.Ω → ℝ) =ᵐ[G.P]
      (T u ((hφLp i).toLp (φ i)) : G.Ω → ℝ) :=
    ((hF i).2 u hu).trans (hag u hu (φ i) (hφ i) (hφLp i)).symm
  have hint (i j : Fin n) :
      (∫ ω, F i u ω * F j u ω ∂G.P) =
        ∫ ω, (T u ((hφLp i).toLp (φ i))) ω * (T u ((hφLp j).toLp (φ j))) ω ∂G.P := by
    apply integral_congr_ae
    filter_upwards [heq i, heq j] with ω hi hj
    rw [hi, hj]
  have hall : ∀ᵐ ω ∂G.P, ∀ i : Fin n, F i u ω = (T u ((hφLp i).toLp (φ i))) ω := by
    rw [ae_all_iff]
    exact heq
  filter_upwards [hWa u (Set.mem_Ici.mpr hu), hall] with ω hω hωi
  rw [hω]
  simp [fp81s21_wickG_finite_rank_polynomial, hωi, hint]

#print axioms fp81s21_wickFam_oscillator_polynomial_continuous
end HRS.Fp81.S21
end
