import HRS.Sections.Q41Aux21
import HRS.MD.EQInitGauss
import HRS.MD.EQStrongChain

/-!
# EQ-STRONG, Gaussian clause, coordinatewise inputs

For a stationary Gaussian field `Z` and a real Fourier mode `k`, the coordinate `Y_t = ⟨Z^t, e_k⟩`:
* `E Y_0² ≤ 8`;
* the increment `Y_t - Y_s` (`0 ≤ s ≤ t`) is a centred Gaussian of variance
  `≤ 2 β⁻¹ C_c² ⟨k⟩² (t-s)` (Lyapunov/energy bound `q41_inc_bound`), hence
  `E (Y_t - Y_s)⁴ ≤ 48 e^{1/2} (2 β⁻¹ C_c² ⟨k⟩² (t-s))²`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MD.EQStrong

open HRS HRS.Q41 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.PDE.MFPair

variable {d : ℕ}

/-- The increment of a centred Gaussian pair is a centred Gaussian. -/
theorem eqstrong_diff_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Fin 2 → Ω → ℝ)
    (hf : ∀ a, Measurable (f a)) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.PosSemidef)
    (h : P.map (fun ω => (WithLp.toLp 2 fun a => f a ω : EuclideanSpace ℝ (Fin 2))) =
      multivariateGaussian 0 S) :
    P.map (fun ω => f 1 ω - f 0 ω) = gaussianReal 0 (S 0 0 + S 1 1 - 2 * S 0 1).toNNReal := by
  set W : Ω → EuclideanSpace ℝ (Fin 2) := fun ω => WithLp.toLp 2 fun a => f a ω with hW
  have hWm : Measurable W :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp (measurable_pi_iff.2 hf)
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin 2)) :=
    EuclideanSpace.proj 1 - EuclideanSpace.proj 0 with hL
  have hLfun : (⇑L : EuclideanSpace ℝ (Fin 2) → ℝ) = fun x => x 1 - x 0 := by
    funext x; simp [hL]
  have e : (fun ω => f 1 ω - f 0 ω) = L ∘ W := by
    funext ω; simp [hLfun, hW]
  have hmem : ∀ i : Fin 2, MemLp (fun x : EuclideanSpace ℝ (Fin 2) => x i) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S) := by
    intro i
    have := (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S))
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp_memLp' this
  rw [e, ← Measure.map_map L.continuous.measurable hWm, h, IsGaussian.map_eq_gaussianReal L]
  have hmean : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S)[L] = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id]
    simp
  have hherm : S 1 0 = S 0 1 := by
    have := hS.1
    simpa using Matrix.IsHermitian.apply this 0 1
  have hvar : Var[L; multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S] =
      S 0 0 + S 1 1 - 2 * S 0 1 := by
    rw [hLfun, variance_fun_sub (hmem 1) (hmem 0), variance_eval_multivariateGaussian hS,
      variance_eval_multivariateGaussian hS, covariance_eval_multivariateGaussian hS, hherm]
    ring
  rw [hmean, hvar]

variable {s β c₀ Λ₀ : ℝ} {V ρβ : Torus d → ℝ}

/-- The explicit increment bound for the kernel `q41_r` (copy of the last clause of
`q41_modeKernel`, with the constant `2 β⁻¹ C_c²` kept explicit). -/
theorem eqstrong_key (hd : 1 ≤ d) (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ)
    (hβ : 0 < β) {Cc : ℝ} (hCc : ∀ k : NonzeroLattice d,
      Torus.cbNorm 1 (Torus.realMode k) ≤ Cc * Lattice.jp k.1 ^ 1) (k : NonzeroLattice d)
    {u u' : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') :
    q41_r H u u k k + q41_r H u' u' k k - 2 * q41_r H u u' k k ≤
      2 * β⁻¹ * Cc ^ 2 * Lattice.jp k.1 ^ 2 * (u' - u) := by
  have hmc := q41_realMode_cont (d := d)
  have hsm := fun k : NonzeroLattice d => HRS.FieldSingAux.isSmooth_realMode k
  have hdiag : ∀ v : ℝ, q41_r H v v k k = susceptibilityCov (periodicRiesz d s)
      (withDensityReal ρβ) β (Torus.realMode k) (Torus.realMode k) := by
    intro v
    simp only [q41_r, q41_cov2, if_pos le_rfl, sub_self]
    exact q41_Cv_S0 H hd (hmc k) (hsm k)
  have hcb : Torus.cbNorm 1 (Torus.realMode k) ^ 2 ≤ Cc ^ 2 * Lattice.jp k.1 ^ 2 := by
    have h0 := cbNorm_nonneg_ps (d := d) 1 (Torus.realMode k)
    have := hCc k
    calc Torus.cbNorm 1 (Torus.realMode k) ^ 2 ≤ (Cc * Lattice.jp k.1 ^ 1) ^ 2 :=
          pow_le_pow_left₀ h0 this 2
      _ = Cc ^ 2 * Lattice.jp k.1 ^ 2 := by ring
  have hh : 0 ≤ u' - u := by linarith
  have hinc := q41_inc_bound H hd (hsm k) hh
  have e2 : q41_r H u u' k k = susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
      (Torus.realMode k) (Sg H (u' - u) (Torus.realMode k)) := by
    simp only [q41_r, q41_cov2, if_pos huu']
  have hνpos : 0 < β⁻¹ := inv_pos.2 hβ
  have hlip : q41_r H u u k k - q41_r H u u' k k ≤ β⁻¹ * (Cc ^ 2 * Lattice.jp k.1 ^ 2) * (u' - u) := by
    rw [hdiag u, e2]
    refine hinc.trans ?_
    have := mul_le_mul_of_nonneg_left hcb hνpos.le
    nlinarith
  have e3 := hdiag u'
  have e4 := hdiag u
  linarith [hlip, e3, e4]

end HRS.MD.EQStrong
