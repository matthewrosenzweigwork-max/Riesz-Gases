import HRS.Sections.ScrnAux6
import HRS.PDE.WellPosed
import HRS.PDE.MeanFieldPairing
import HRS.PDE.MeanFieldDefs

/-!
# Packet SCRN, part 7: the Haar mean-field solution `ρ ≡ 1` for `V = 0` and its adjoint package

* `coeffOf 1 = δ_0`, `convGradConv ∇g 1 = 0`, hence `ρ ≡ 1` is a weak mean-field solution
  (`scrn_isMeanFieldSolution_one`) with `IsRegularMF 3 Λ T 1`;
* `AdjointData` for `(mfData .. 0 β, ρ ≡ 1)`: regime `R1` if `s ≤ d-2`, `R3` (with `ν₀ = β⁻¹`) otherwise;
* `forwardGen D 1 c k = -λ_k c k` (`λ_k = (2π|k|)²(β⁻¹ + ĝ(k))`).
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

section Haar

open PDE PDE.ClassicalAux

lemma scrn_coeffOf_one (k : Lattice d) :
    coeffOf (fun _ : Torus d => (1 : ℝ)) k = if k = 0 then 1 else 0 := by
  rw [coeffOf_apply]
  simp only [Complex.ofReal_one, mul_one]
  rw [Torus.integral_mode]
  simp

lemma scrn_convGradConv_one (hd : 1 ≤ d) (D : DynData d) :
    convGradConv (periodicRieszGrad d D.s) (fun _ : Torus d => (1 : ℝ)) = fun _ => 0 := by
  have hK := convKernelFacts hd D
  have h1 : Torus.IsCk 1 (fun _ : Torus d => (1 : ℝ)) := by
    unfold Torus.IsCk Torus.lift
    exact contDiff_const
  have hc := hK.cont _ h1
  funext x
  ext i
  have hi : (fun y => convGradConv (periodicRieszGrad d D.s) (fun _ : Torus d => (1 : ℝ)) y i) =
      fun _ => 0 := by
    refine eq_of_coeffOf_eq ?_ continuous_const ?_
    · exact (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp hc)
    · rw [hK.coeff _ h1 i]
      funext k
      have h0 : coeffOf (fun _ : Torus d => (0 : ℝ)) k = 0 := by
        rw [coeffOf_apply]; simp
      rw [h0]
      simp only [gradRieszCoeff, derivCoeff, rieszMult]
      rw [scrn_coeffOf_one]
      by_cases hk : k = 0
      · subst hk; simp
      · simp [hk]
  have := congrFun hi x
  simpa using this


lemma scrn_withDensityReal_one : withDensityReal (fun _ : Torus d => (1 : ℝ)) = volume := by
  simp [withDensityReal]

lemma scrn_integral_laplacian (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) :
    ∫ x, Torus.laplacian ψ x = 0 := by
  have h := congrFun (coeffOf_laplacian ψ hψ) 0
  rw [coeffOf_apply] at h
  simp only [neg_zero, Torus.mode_zero, one_mul] at h
  have hn0 : Lattice.enorm (0 : Lattice d) = 0 := by
    unfold Lattice.enorm
    have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    rw [this, norm_zero]
  have h2 : laplaceCoeff (coeffOf ψ) 0 = 0 := by
    simp [laplaceCoeff, hn0]
  rw [h2] at h
  have : ((∫ x, Torus.laplacian ψ x : ℝ) : ℂ) = 0 := by
    rw [← h]; exact integral_ofReal.symm
  exact_mod_cast this

lemma scrn_grad_zero : Torus.grad (fun _ : Torus d => (0 : ℝ)) = fun _ => 0 := by
  funext x
  unfold Torus.grad Torus.lift
  have : ((fun _ : Torus d => (0 : ℝ)) ∘ Torus.mk) = fun _ : Euc d => (0 : ℝ) := rfl
  rw [this]
  simp

theorem scrn_isMeanFieldSolution_one (hd : 1 ≤ d) (D : DynData d) (hV : D.V = fun _ => 0)
    (T : ℝ) : IsMeanFieldSolution D T (fun _ _ => (1 : ℝ)) := by
  have hdens : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  refine ⟨fun t ht => hdens, fun ψ hψ t ht => ?_⟩
  simp only [sub_self]
  symm
  rw [integral_eq_zero_of_ae]
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Pi.zero_apply]
  rw [scrn_withDensityReal_one]
  have h1 : pair (volume : Measure (Torus d))
      (fun x => D.invβ * Torus.laplacian ψ x - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) = 0 := by
    unfold pair
    rw [hV, scrn_grad_zero]
    simp only [inner_zero_left, sub_zero]
    rw [integral_const_mul, scrn_integral_laplacian ψ hψ, mul_zero]
  have h2 : interactionPairing D ψ (volume : Measure (Torus d)) volume = 0 := by
    rw [← scrn_withDensityReal_one]
    have hρ1 : Torus.IsCk 1 (fun _ : Torus d => (1 : ℝ)) := by
      unfold Torus.IsCk Torus.lift; exact contDiff_const
    rw [PDE.MFPairing.interactionPairing_eq_of_isCk hd D _ hρ1 (fun _ => zero_le_one) ψ hψ,
      scrn_convGradConv_one hd D]
    have hm0 : Torus.matVec D.M (0 : Euc d) = 0 := by simp [Torus.matVec]
    simp [hm0]
  rw [h1, h2, zero_add]


/-- The multiplier `λ_k = 4π²|k|²(β⁻¹ + ĝ(k))` of the Haar linearisation. -/
def scrnLam (d : ℕ) (s invβ : ℝ) (k : Lattice d) : ℝ :=
  4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * (invβ + rieszCoeff d s k)

lemma scrn_mulCoeff_delta (c : Coeff d) (k : Lattice d) :
    mulCoeff (coeffOf (fun _ : Torus d => (1 : ℝ))) c k = c k := by
  unfold mulCoeff
  rw [tsum_eq_single k]
  · rw [sub_self, scrn_coeffOf_one]; simp
  · intro j hj
    rw [scrn_coeffOf_one]
    have : k - j ≠ 0 := sub_ne_zero.2 (Ne.symm hj)
    simp [this]

lemma scrn_mulCoeff_zero_left (c : Coeff d) (k : Lattice d) :
    mulCoeff (fun _ => (0 : ℂ)) c k = 0 := by
  unfold mulCoeff; simp

lemma scrn_gradRieszCoeff_one (D : DynData d) (i : Fin d) (k : Lattice d) :
    gradRieszCoeff d D.s i (coeffOf (fun _ : Torus d => (1 : ℝ))) k = 0 := by
  simp only [gradRieszCoeff, derivCoeff, rieszMult]
  rw [scrn_coeffOf_one]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]

lemma scrn_coeffOf_zero (k : Lattice d) : coeffOf (fun _ : Torus d => (0 : ℝ)) k = 0 := by
  rw [coeffOf_apply]; simp

lemma scrn_forwardGen_one {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (c : Coeff d) (k : Lattice d) :
    forwardGen (mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ => (1 : ℝ)) c k =
      -((scrnLam d s β⁻¹ k : ℝ) : ℂ) * c k := by
  set D := mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  have hDs : D.s = s := rfl
  have hDM : D.M = -1 := rfl
  have hDi : D.invβ = β⁻¹ := rfl
  have hDV : D.V = fun _ => 0 := rfl
  have hdrift : ∀ j, driftCoeff D (fun _ => (1 : ℝ)) j = fun _ => 0 := by
    intro j
    funext k'
    simp only [driftCoeff]
    simp only [scrn_gradRieszCoeff_one, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero]
    rw [hDV]
    simp [derivCoeff, scrn_coeffOf_zero]
  have htrans : transportCoeff D (fun _ => (1 : ℝ)) c k = 0 := by
    simp only [transportCoeff, hdrift, scrn_mulCoeff_zero_left, Finset.sum_const_zero]
  have hnl : nonlocalCoeff D (fun _ => (1 : ℝ)) c k =
      ((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * rieszCoeff d s k : ℝ) : ℂ) * c k := by
    simp only [nonlocalCoeff, scrn_mulCoeff_delta, gradRieszCoeff, derivCoeff, rieszMult, hDM, hDs]
    have hen : Lattice.enorm k ^ 2 = ∑ i, ((k i : ℤ) : ℝ) ^ 2 := by
      unfold Lattice.enorm Lattice.toEuc
      rw [EuclideanSpace.norm_sq_eq]
      simp
    simp only [Matrix.neg_apply, Matrix.one_apply, Complex.ofReal_neg]
    simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, neg_mul,
      ite_mul, one_mul, zero_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [hen]
    push_cast
    rw [show (4 * (↑Real.pi : ℂ) ^ 2 * ∑ x, ((k x : ℤ) : ℂ) ^ 2) * (rieszCoeff d s k : ℂ) * c k =
        ∑ x, (4 * (↑Real.pi : ℂ) ^ 2 * ((k x : ℤ) : ℂ) ^ 2 * (rieszCoeff d s k : ℂ) * c k) by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul], ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-(↑Real.pi : ℂ) ^ 2 * 4 * ((k i : ℤ) : ℂ) ^ 2 * (rieszCoeff d s k : ℂ) * c k) * hI
  simp only [forwardGen, htrans, hnl, hDi, laplaceCoeff, scrnLam]
  push_cast
  ring

end Haar

end HRS
