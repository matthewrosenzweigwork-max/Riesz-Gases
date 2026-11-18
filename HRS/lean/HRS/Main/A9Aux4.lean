import HRS.Main.A9Aux3
import HRS.Main.A9Aux2

/-!
# Packet A9, part 4: coordinates in `E_γ = NegSobolev d γ`: unit vectors, `ℓ¹`-bound of the norm,
Gaussian laws of finitely many coordinates
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33

variable {d : ℕ}

section Gauss

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- the law of finitely many coordinates of a centred Gaussian is the multivariate Gaussian with the
covariance matrix of the coordinates. -/
theorem a9_gauss_coord {q : ℕ} {γ : Measure H} [IsProbabilityMeasure γ] (hγ : IsCenteredGaussian γ)
    (b : Fin q → H) :
    γ.map (hmCoordCLM b) = ProbabilityTheory.multivariateGaussian 0
      (Matrix.of fun i j => ∫ z, inner ℝ (b i) z * inner ℝ (b j) z ∂γ) := by
  have hG : IsGaussian γ := hγ.1
  have hmem : MemLp id 2 γ := IsGaussian.memLp_two_id
  have h0 : ∫ x, x ∂γ = 0 := HilbertCLTAux.gaussian_mean_zero hγ
  have hcovE : ∀ x y : H, covarianceBilin γ x y = ∫ z, inner ℝ x z * inner ℝ y z ∂γ := by
    intro x y
    rw [covarianceBilin_apply hmem]
    simp [h0]
  set S : Matrix (Fin q) (Fin q) ℝ := Matrix.of fun i j => ∫ z, inner ℝ (b i) z * inner ℝ (b j) z ∂γ
    with hSdef
  have hS : S = Matrix.of fun i j => covarianceBilin γ (b i) (b j) := by
    ext i j; simp [hSdef, hcovE]
  have hSpsd : S.PosSemidef := by
    rw [hS]
    exact posSemidef_gram (B := covarianceBilin γ) (covarianceBilin_comm) (covarianceBilin_self_nonneg) b
  refine IsGaussian.ext ?_ ?_
  · rw [integral_id_multivariateGaussian']
    show ∫ x, x ∂(γ.map (hmCoordCLM b)) = 0
    rw [ContinuousLinearMap.integral_id_map (hmem.integrable (by simp))]
    rw [h0, map_zero]
  · ext u v
    rw [covarianceBilin_multivariateGaussian hSpsd, covarianceBilin_map hmem, adjoint_hmCoordCLM,
      adjoint_hmCoordCLM, embedCLM_apply, embedCLM_apply]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hS, Matrix.of_apply,
      dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring

end Gauss

section Units

variable {m : ℝ}

/-- the unit vector of the coordinate `k` of `E_m`. -/
def a9unit (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m :=
  (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem a9unit_inner (k : NonzeroLattice d) (F : NegSobolev d m) :
    inner ℝ (a9unit m k) F = NegSobolev.coord F k := by
  classical
  have h := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ) k (1 : ℝ)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F)
  refine h.trans ?_
  simp [NegSobolev.coord]

theorem a9unit_orthonormal {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k) :
    Orthonormal ℝ (fun a => a9unit m (k a)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [a9unit_inner]
  show (lp.single 2 (k b) (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2) (k a) = _
  rw [lp.single_apply]
  by_cases h : a = b
  · subst h; simp
  · have : k b ≠ k a := fun e => h (hk e).symm
    simp [this, h]

theorem a9_coordCLM_apply {q : ℕ} (k : Fin q → NonzeroLattice d) (F : NegSobolev d m) (a : Fin q) :
    hmCoordCLM (fun a => a9unit m (k a)) F a = NegSobolev.coord F (k a) := by
  rw [hmCoordCLM_apply, a9unit_inner]

end Units

section L1

theorem a9_norm_le_tsum {m : ℝ} (F : NegSobolev d m)
    (hs : Summable fun k => |NegSobolev.coord F k|) : ‖F‖ ≤ ∑' k, |NegSobolev.coord F k| := by
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq F
  have hT0 : 0 ≤ ∑' k, |NegSobolev.coord F k| := tsum_nonneg fun _ => abs_nonneg _
  have hsq : ‖F‖ ^ 2 ≤ (∑' k, |NegSobolev.coord F k|) ^ 2 := by
    rw [h2]
    refine h1.tsum_le_of_sum_le fun s => ?_
    calc ∑ k ∈ s, NegSobolev.coord F k ^ 2 = ∑ k ∈ s, |NegSobolev.coord F k| ^ 2 := by
          simp_rw [sq_abs]
      _ ≤ (∑ k ∈ s, |NegSobolev.coord F k|) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => abs_nonneg _)
      _ ≤ _ := by
          have := hs.sum_le_tsum s (fun k _ => abs_nonneg _)
          exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) this 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hT0 two_ne_zero).mp hsq

theorem a9_ofReal_norm_le_tsum {m : ℝ} (F : NegSobolev d m) :
    ENNReal.ofReal ‖F‖ ≤ ∑' k, ENNReal.ofReal |NegSobolev.coord F k| := by
  by_cases hs : Summable fun k => |NegSobolev.coord F k|
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) hs]
    exact ENNReal.ofReal_le_ofReal (a9_norm_le_tsum F hs)
  · have : ∑' k, ENNReal.ofReal |NegSobolev.coord F k| = ⊤ := by
      by_contra hne
      apply hs
      have := ENNReal.summable_toReal hne
      simpa [ENNReal.toReal_ofReal (abs_nonneg _)] using this
    rw [this]; exact le_top

end L1

end HRS.Main.A9
