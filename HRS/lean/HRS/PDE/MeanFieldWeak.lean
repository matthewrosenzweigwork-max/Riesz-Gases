import HRS.PDE.MeanFieldGlobal
import HRS.PDE.MeanFieldAprioriLower
import HRS.PDE.MeanFieldThermal
import HRS.PDE.MeanFieldOneLe
import HRS.PDE.MeanFieldPairing
import HRS.PDE.MeanFieldAprioriPhi

/-!
# The weak form of the finite-regularity mean-field equation, packet P8c (package MF-01;
`MeanFieldDecayPlan.md`, section P8c)

Proves `finite_reg_isMeanFieldSolution` (the body, with the verbatim conclusion): the density path
of any `IsMFSolutionHK` solution is a weak solution `IsMeanFieldSolution` on every `[0,T]`.

Route: `isProbDensity_mfPath` (positivity from the uniform bounds, mass one from the zero mode);
`weak_integrand_eq` (two integrations by parts plus `MFPairing.interactionPairing_eq_of_isCk`);
`hasDerivAt_pairing` / `continuousOn_pairings` (time calculus of `∫ ψ ρ^τ`); then the fundamental
theorem of calculus.

NOTE: `convGradConv_eq_grad_riesz` (a statement of packet P7a1, `MeanFieldDecayGap.lean`) is proved
here under the name `weak_convGradConv_eq_grad_riesz`, to be deduplicated by the integrator.
Like `MeanFieldGlobal.lean`, the main theorem depends on the scaffold
`MFApriori.mf_apriori_bound_real_on` (AP7) through `finite_reg_uniform_bounds`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFWeak

open MFApriori

variable {d : ℕ}

/-- The Riesz potential `g ⋆ ρ` of a function is the coefficient-multiplier `riesz`
(continuous `ρ` with `H^K` coefficients, `K > d/2`). -/
theorem weak_riesz_coeffOf_eq_convFun (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 < K) (ρ : Torus d → ℝ) (hρ : Continuous ρ) (hmem : MemHs K (coeffOf ρ)) :
    riesz d s (coeffOf ρ) = convFun (periodicRiesz d s) ρ := by
  have hρi : Integrable ρ := hρ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hreal : IsRealCoeff (coeffOf ρ) := isRealCoeff_coeffOf ρ hρi
  have hmem' := (hs_rieszMult s hsd K _ hmem).1
  have hrr := isRealCoeff_rieszMult s _ hreal
  have hs' : Summable fun k => ‖rieszMult d s (coeffOf ρ) k‖ := summable_norm_of_memHs K hK _ hmem'
  refine MFAux.eq_of_funFourierCoeff_eq (HRS.PDE.MFProduct.continuous_toFun _ hs')
    (MFAux.continuous_convFun (MFOneLe.integrable_periodicRiesz hd s hs0 hsd) hρ) (fun k => ?_)
  have h1 := congrFun (coeffOf_toFun _ hrr hs') k
  have h3 := MFOneLe.coeffOf_convFun hd s hs0 hsd hρ k
  have h4 : coeffOf (toFun (rieszMult d s (coeffOf ρ))) k = coeffOf (convFun (periodicRiesz d s) ρ) k := by
    rw [h1, h3]; rfl
  exact h4

/-- (A2b) The force `∇g⋆ρ` (cancellation convention) is the gradient of `riesz d s (coeffOf ρ)`. -/
theorem weak_convGradConv_eq_grad_riesz (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (ρ : Torus d → ℝ) (hρ : Torus.IsCk 1 ρ)
    (hmem : MemHs K (coeffOf ρ)) (x : Torus d) :
    convGradConv (periodicRieszGrad d s) ρ x = Torus.grad (riesz d s (coeffOf ρ)) x := by
  have hρc := MFAux.continuous_of_isCk hρ
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hreal : IsRealCoeff (coeffOf ρ) := isRealCoeff_coeffOf ρ hρi
  have hR1 : Torus.IsCk 1 (riesz d s (coeffOf ρ)) :=
    (riesz_isCk hd s hs0 hsd 1 K (by simpa using hK) _ hmem hreal).1
  have heq := weak_riesz_coeffOf_eq_convFun hd s hs0 hsd K (by linarith) ρ hρc hmem
  have hφ : Torus.IsCk 1 (convFun (periodicRiesz d s) ρ) := heq ▸ hR1
  ext j
  rw [MFOneLe.convGradConv_eq_partialDeriv hd s hs0 hsd hρ hφ j, MFAux.grad_apply, heq]


/-- (F1) The solution is a probability density at every time. -/
theorem isProbDensity_mfPath (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρc : ℝ → Coeff d)
    (hρc : IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc) (t : ℝ) (ht : 0 ≤ t) :
    IsProbDensity (mfPath ρc t) := by
  have hKd : (d : ℝ) / 2 < K := by linarith [H.hK]
  obtain ⟨c, C, hc, hbd⟩ := MFGlobal.finite_reg_uniform_bounds hd s βm βp K V ρ₀ H
  have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd s βm βp K V ρ₀ H β hβ ρc hρc t ht
  have hmem : MemHs (K : ℝ) (ρc t) := hρc.cont.1 t ht
  have hsum : Summable fun k => ‖ρc t k‖ := summable_norm_of_memHs K hKd _ hmem
  have h0 : ρc t 0 = 1 := by
    have := coeff_zero_eq_on hd s V ρ₀ β⁻¹ K ρc (IsMFSolutionHK.toSolOn hρc t) (t := t) ⟨ht, le_rfl⟩
    rw [this, coeffOf_zero_eq_integral', H.hρ₀.integral_one]
    simp
  refine ⟨fun x => ?_, ?_, ?_⟩
  · exact ((hbd β hβ ρc hρc t ht).1 x).1.trans' hc.le
  · exact (HRS.PDE.MFProduct.continuous_toFun _ hsum).measurable
  · exact integral_toFun_eq_one K hKd _ hmem hreal h0

/-- (F2) The weak-form integrand: for a positive real `H^K` coefficient `c` and a `C²` test `ψ`,
`∫ ψ 𝒩(ρ) = ν ∫ ρ Δψ - ∫ ρ ∇V·∇ψ + interactionPairing` (with `M = -I`). -/
theorem weak_integrand_eq (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) (hVK : MemHs K (coeffOf V))
    (β : ℝ) (hβ : 0 < β) (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c)
    (hnn : ∀ x, 0 ≤ toFun c x) (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) :
    ∫ x, ψ x * toFun (mfRhsCoeff d s V β⁻¹ c) x =
      pair (withDensityReal (toFun c)) (fun x => (mfData d s hs0 hsd V β hβ).invβ *
          Torus.laplacian ψ x - inner ℝ (Torus.grad (mfData d s hs0 hsd V β hβ).V x) (Torus.grad ψ x)) +
        interactionPairing (mfData d s hs0 hsd V β hβ) ψ (withDensityReal (toFun c))
          (withDensityReal (toFun c)) := by
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith
  have hKd : (d : ℝ) / 2 < K := by linarith
  obtain ⟨C₂, -, hC₂⟩ := exists_mfPath_isCk (d := d) 2 K (by simpa using hK)
  have hρ2 : Torus.IsCk 2 (toFun c) := (hC₂ c hc hreal).1
  have hρ1 : Torus.IsCk 1 (toFun c) := hρ2.of_le (by norm_num)
  have hR2 : Torus.IsCk 2 (riesz d s c) :=
    (riesz_isCk hd s hs0 hsd 2 K (by simpa using hK) c hc hreal).1
  have hR1 : Torus.IsCk 1 (riesz d s c) := hR2.of_le (by norm_num)
  have hV1 : Torus.IsCk 1 V := hV.of_le (by norm_num)
  have hW2 := isCk_two_Wpot hd s hs0 hsd K hK V hV c hc hreal
  have hψ1 : Torus.IsCk 1 ψ := hψ.of_le (by norm_num)
  have hsc : Summable fun k => ‖c k‖ := summable_norm_of_memHs K hKd c hc
  have hcoρ : coeffOf (toFun c) = c := coeffOf_toFun c hreal hsc
  set ρ := toFun c with hρdef
  set W := Wpot d s V c with hWdef
  set R := riesz d s c with hRdef
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpρ : ∀ j, Continuous (Torus.partialDeriv j ρ) := fun j => continuous_partialDeriv j _ hρ1
  have hpρ1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ρ) := fun j => isCk_one_partialDeriv j _ hρ2
  have hpψ : ∀ j, Continuous (Torus.partialDeriv j ψ) := fun j => continuous_partialDeriv j _ hψ1
  have hpψ1 : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ψ) := fun j => isCk_one_partialDeriv j _ hψ
  have hpV : ∀ j, Continuous (Torus.partialDeriv j V) := fun j => continuous_partialDeriv j _ hV1
  have hpR : ∀ j, Continuous (Torus.partialDeriv j R) := fun j => continuous_partialDeriv j _ hR1
  have hpW : ∀ j, Torus.partialDeriv j W = fun y => Torus.partialDeriv j V y + Torus.partialDeriv j R y :=
    fun j => by funext y; exact partialDeriv_add j V _ hV1 hR1 y
  have hP1 : ∀ j, Torus.IsCk 1 (fun y => ρ y * Torus.partialDeriv j W y) := fun j =>
    MFAux.isCk_mul_partialDeriv _ _ hρ1 hW2 j
  have hpP : ∀ j, Continuous (Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y)) :=
    fun j => continuous_partialDeriv j _ (hP1 j)
  have hpp : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j ρ)) := fun j =>
    continuous_partialDeriv j _ (hpρ1 j)
  have hppψ : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j ψ)) := fun j =>
    continuous_partialDeriv j _ (hpψ1 j)
  have hψc : Continuous ψ := MFAux.continuous_of_isCk hψ1
  have hlapρ : ∀ x, Torus.laplacian ρ x = ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ρ) x :=
    fun x => laplacian_eq_sum _ hρ2 x
  have hlapψ : ∀ x, Torus.laplacian ψ x = ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ψ) x :=
    fun x => laplacian_eq_sum _ hψ x
  have hmul : ∀ f g : Torus d → ℝ, ∀ x, f x * g x = g x * f x := fun f g x => mul_comm _ _
  -- integrations by parts
  have ibp1 : ∀ j, ∫ x, ψ x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x =
      ∫ x, ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x := by
    intro j
    have h1 := integral_partialDeriv_mul j (Torus.partialDeriv j ρ) ψ (hpρ1 j) hψ1
    have h2 := integral_partialDeriv_mul j (Torus.partialDeriv j ψ) ρ (hpψ1 j) hρ1
    calc ∫ x, ψ x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x
        = ∫ x, Torus.partialDeriv j (Torus.partialDeriv j ρ) x * ψ x := by
          congr 1; funext x; ring
      _ = -∫ x, Torus.partialDeriv j ρ x * Torus.partialDeriv j ψ x := h1
      _ = -∫ x, Torus.partialDeriv j ψ x * Torus.partialDeriv j ρ x := by
          congr 1; congr 1; funext x; ring
      _ = ∫ x, Torus.partialDeriv j (Torus.partialDeriv j ψ) x * ρ x := h2.symm
      _ = _ := by congr 1; funext x; ring
  have ibp2 : ∀ j, ∫ x, ψ x * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x =
      -∫ x, ρ x * (Torus.partialDeriv j W x * Torus.partialDeriv j ψ x) := by
    intro j
    have h1 := integral_partialDeriv_mul j (fun y => ρ y * Torus.partialDeriv j W y) ψ (hP1 j) hψ1
    calc ∫ x, ψ x * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x
        = ∫ x, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x * ψ x := by
          congr 1; funext x; ring
      _ = _ := by
          rw [h1]; congr 1; congr 1; funext x; ring
  -- the left-hand side
  have hF : ∀ x, toFun (mfRhsCoeff d s V β⁻¹ c) x =
      β⁻¹ * ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ρ) x +
        ∑ j, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x := by
    intro x
    rw [toFun_mfRhsCoeff_eq' hd s hs0 hsd K hK V hV hVK β⁻¹ c hc hreal x, hlapρ x]
  have c1 : ∀ j, Continuous fun x => ψ x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x :=
    fun j => hψc.mul (hpp j)
  have c2 : ∀ j, Continuous fun x =>
      ψ x * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x :=
    fun j => hψc.mul (hpP j)
  have hLHS : ∫ x, ψ x * toFun (mfRhsCoeff d s V β⁻¹ c) x =
      β⁻¹ * (∑ j, ∫ x, ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x) +
        ∑ j, -∫ x, ρ x * (Torus.partialDeriv j W x * Torus.partialDeriv j ψ x) := by
    have e0 : ∀ x, ψ x * toFun (mfRhsCoeff d s V β⁻¹ c) x =
        β⁻¹ * (∑ j, ψ x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x) +
          ∑ j, ψ x * Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x := by
      intro x
      rw [hF x, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e0]
    have i1 : Integrable fun x => β⁻¹ * (∑ j, ψ x * Torus.partialDeriv j (Torus.partialDeriv j ρ) x) :=
      hint _ (continuous_const.mul (continuous_finsetSum _ fun j _ => c1 j))
    have i2 : Integrable fun x => ∑ j, ψ x *
        Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j W y) x :=
      hint _ (continuous_finsetSum _ fun j _ => c2 j)
    rw [integral_add i1 i2, integral_const_mul, integral_finsetSum _ (fun j _ => hint _ (c1 j)),
      integral_finsetSum _ (fun j _ => hint _ (c2 j))]
    simp_rw [ibp1, ibp2]
  -- the right-hand side
  have hρm : Measurable ρ := hρc.measurable
  have hpair : pair (withDensityReal ρ) (fun x => (mfData d s hs0 hsd V β hβ).invβ *
          Torus.laplacian ψ x - inner ℝ (Torus.grad (mfData d s hs0 hsd V β hβ).V x) (Torus.grad ψ x)) =
      β⁻¹ * (∑ j, ∫ x, ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x) -
        ∑ j, ∫ x, ρ x * (Torus.partialDeriv j V x * Torus.partialDeriv j ψ x) := by
    unfold pair
    rw [MFPairing.integral_withDensityReal hρm hnn]
    have e0 : ∀ x, ρ x * ((mfData d s hs0 hsd V β hβ).invβ * Torus.laplacian ψ x -
        inner ℝ (Torus.grad (mfData d s hs0 hsd V β hβ).V x) (Torus.grad ψ x)) =
        β⁻¹ * (∑ j, ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x) -
          ∑ j, ρ x * (Torus.partialDeriv j V x * Torus.partialDeriv j ψ x) := by
      intro x
      have : (mfData d s hs0 hsd V β hβ).invβ = β⁻¹ := rfl
      have h2 : (mfData d s hs0 hsd V β hβ).V = V := rfl
      rw [this, h2, inner_grad_grad, hlapψ x, mul_sub, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    simp_rw [e0]
    have d1 : ∀ j, Continuous fun x => ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x :=
      fun j => hρc.mul (hppψ j)
    have d2 : ∀ j, Continuous fun x => ρ x * (Torus.partialDeriv j V x * Torus.partialDeriv j ψ x) :=
      fun j => hρc.mul ((hpV j).mul (hpψ j))
    have i1 : Integrable fun x => β⁻¹ * (∑ j, ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x) :=
      hint _ (continuous_const.mul (continuous_finsetSum _ fun j _ => d1 j))
    have i2 : Integrable fun x => ∑ j, ρ x * (Torus.partialDeriv j V x * Torus.partialDeriv j ψ x) :=
      hint _ (continuous_finsetSum _ fun j _ => d2 j)
    rw [integral_sub i1 i2, integral_const_mul,
      integral_finsetSum _ (fun j _ => hint _ (d1 j)),
      integral_finsetSum _ (fun j _ => hint _ (d2 j))]
  have hint2 : interactionPairing (mfData d s hs0 hsd V β hβ) ψ (withDensityReal ρ)
      (withDensityReal ρ) = -∑ j, ∫ x, ρ x * (Torus.partialDeriv j ψ x * Torus.partialDeriv j R x) := by
    rw [MFPairing.interactionPairing_eq_of_isCk hd _ ρ hρ1 hnn ψ hψ]
    have e0 : ∀ x, ρ x * inner ℝ (Torus.grad ψ x)
        (Torus.matVec (mfData d s hs0 hsd V β hβ).M
          (convGradConv (periodicRieszGrad d (mfData d s hs0 hsd V β hβ).s) ρ x)) =
        -∑ j, ρ x * (Torus.partialDeriv j ψ x * Torus.partialDeriv j R x) := by
      intro x
      have h1 : (mfData d s hs0 hsd V β hβ).M = -1 := rfl
      have h2 : (mfData d s hs0 hsd V β hβ).s = s := rfl
      rw [h1, h2, MFAux.matVec_negOne, weak_convGradConv_eq_grad_riesz hd s hs0 hsd K hK1 ρ hρ1
        (hcoρ ▸ hc) x, inner_neg_right, inner_grad_grad, mul_neg, Finset.mul_sum, hcoρ]
    simp_rw [e0]
    have d3 : ∀ j, Continuous fun x => ρ x * (Torus.partialDeriv j ψ x * Torus.partialDeriv j R x) :=
      fun j => hρc.mul ((hpψ j).mul (hpR j))
    rw [integral_neg, integral_finsetSum _ (fun j _ => hint _ (d3 j))]
  rw [hLHS, hpair, hint2]
  have hsplit : ∀ j, ∫ x, ρ x * (Torus.partialDeriv j W x * Torus.partialDeriv j ψ x) =
      (∫ x, ρ x * (Torus.partialDeriv j V x * Torus.partialDeriv j ψ x)) +
        ∫ x, ρ x * (Torus.partialDeriv j ψ x * Torus.partialDeriv j R x) := by
    intro j
    have i1 : Integrable fun x => ρ x * (Torus.partialDeriv j V x * Torus.partialDeriv j ψ x) :=
      hint _ (hρc.mul ((hpV j).mul (hpψ j)))
    have i2 : Integrable fun x => ρ x * (Torus.partialDeriv j ψ x * Torus.partialDeriv j R x) :=
      hint _ (hρc.mul ((hpψ j).mul (hpR j)))
    rw [← integral_add i1 i2]
    congr 1; funext x
    rw [hpW j]
    ring
  simp_rw [hsplit]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  ring


/-- Continuity of a parameter integral over the torus, from joint continuity on `[0,T] × 𝕋^d`. -/
theorem continuousOn_integral_prod {T : ℝ} (f : ℝ → Torus d → ℝ)
    (hf : ContinuousOn (fun p : ℝ × Torus d => f p.1 p.2) (Icc 0 T ×ˢ univ)) :
    ContinuousOn (fun τ => ∫ x, f τ x) (Icc 0 T) := by
  have hK : IsCompact (Icc 0 T ×ˢ (univ : Set (Torus d))) := isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  have hcf : ∀ τ ∈ Icc 0 T, Continuous fun x : Torus d => f τ x := fun τ hτ =>
    hf.comp_continuous (Continuous.prodMk_right τ) (fun x => ⟨hτ, mem_univ _⟩)
  refine continuousOn_of_dominated (bound := fun _ => C)
    (fun τ hτ => (hcf τ hτ).aestronglyMeasurable)
    (fun τ hτ => Eventually.of_forall fun x => by
      simpa using hC (τ, x) ⟨hτ, mem_univ _⟩)
    (integrable_const C) (Eventually.of_forall fun x => ?_)
  exact hf.comp (Continuous.prodMk_left x).continuousOn (fun τ hτ => ⟨hτ, mem_univ _⟩)

/-- (F3) Differentiating the pairing with a test function along a real solution on `[0,T]`. -/
theorem hasDerivAt_pairing (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) (ψ : Torus d → ℝ)
    (hψ : Continuous ψ) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (fun τ => ∫ x, ψ x * mfPath ρc τ x)
      (∫ x, ψ x * toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  obtain ⟨h1, h2⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  have hψs : ContinuousOn (fun p : ℝ × Torus d => ψ p.2) (Icc 0 T ×ˢ univ) :=
    (hψ.comp continuous_snd).continuousOn
  exact hasDerivAt_integral_param (fun τ x => ψ x * mfPath ρc τ x)
    (fun τ x => ψ x * toFun (mfRhsCoeff d s V ν (ρc τ)) x) ht (hψs.mul h1) (hψs.mul h2)
    (fun τ hτ x => (hasDerivAt_mfPath_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H x hτ).const_mul (ψ x))

/-- (F4) Continuity on `[0,T]` of the pairing and of the right-hand-side pairing. -/
theorem continuousOn_pairings (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) (ψ : Torus d → ℝ)
    (hψ : Continuous ψ) :
    ContinuousOn (fun τ => ∫ x, ψ x * mfPath ρc τ x) (Set.Icc 0 T) ∧
    ContinuousOn (fun τ => ∫ x, ψ x * toFun (mfRhsCoeff d s V ν (ρc τ)) x) (Set.Icc 0 T) := by
  obtain ⟨h1, h2⟩ := continuousOn_mfPath_prod_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H
  have hψs : ContinuousOn (fun p : ℝ × Torus d => ψ p.2) (Icc 0 T ×ˢ univ) :=
    (hψ.comp continuous_snd).continuousOn
  exact ⟨continuousOn_integral_prod (fun τ x => ψ x * mfPath ρc τ x) (hψs.mul h1),
    continuousOn_integral_prod (fun τ x => ψ x * toFun (mfRhsCoeff d s V ν (ρc τ)) x) (hψs.mul h2)⟩

/-- (F5) = the body of `finite_reg_isMeanFieldSolution` (verbatim conclusion). -/
theorem finite_reg_isMeanFieldSolution (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp), ∀ ρc : ℝ → Coeff d, IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc →
      ∀ T, 0 < T →
        IsMeanFieldSolution (mfData d s H.hs0 H.hsd V β (H.hβm.trans_le hβ.1)) T (mfPath ρc) := by
  intro β hβ ρc hρc T hT
  have hK2 : (d : ℝ) / 2 + 2 < K := by linarith [H.hK]
  have hβpos : 0 < β := H.hβm.trans_le hβ.1
  have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd s βm βp K V ρ₀ H β hβ ρc hρc
  have Hs : MFSolRealOn d s V β⁻¹ K ρ₀ ρc T := ⟨IsMFSolutionHK.toSolOn hρc T, fun τ hτ => hreal τ hτ.1⟩
  have hprob := fun t (ht : 0 ≤ t) => isProbDensity_mfPath hd s βm βp K V ρ₀ H β hβ ρc hρc t ht
  refine ⟨fun t ht => hprob t ht.1, fun ψ hψ t ht => ?_⟩
  have hψ1 : Torus.IsCk 1 ψ := hψ.of_le (by norm_num)
  have hψc : Continuous ψ := MFAux.continuous_of_isCk hψ1
  have hV2 : Torus.IsCk 2 V := H.hV.of_le (by exact_mod_cast (show 2 ≤ K + 2 by omega))
  have hVK : MemHs (K : ℝ) (coeffOf V) := MFApriori.Aux.memHs_of_isCk_nat K V H.hV
  have hKd : (d : ℝ) / 2 < K := by linarith
  have hPair : ∀ τ ∈ Icc 0 T, pair (withDensityReal (mfPath ρc τ)) ψ =
      ∫ x, ψ x * mfPath ρc τ x := by
    intro τ hτ
    unfold pair
    rw [MFPairing.integral_withDensityReal (hprob τ hτ.1).measurable (hprob τ hτ.1).nonneg]
    congr 1; funext x; ring
  have hW : ∀ τ ∈ Icc 0 T,
      pair (withDensityReal (mfPath ρc τ)) (fun x => (mfData d s H.hs0 H.hsd V β hβpos).invβ *
          Torus.laplacian ψ x - inner ℝ (Torus.grad (mfData d s H.hs0 H.hsd V β hβpos).V x)
            (Torus.grad ψ x)) +
        interactionPairing (mfData d s H.hs0 H.hsd V β hβpos) ψ (withDensityReal (mfPath ρc τ))
          (withDensityReal (mfPath ρc τ)) =
      ∫ x, ψ x * toFun (mfRhsCoeff d s V β⁻¹ (ρc τ)) x := by
    intro τ hτ
    exact (weak_integrand_eq hd s H.hs0 H.hsd K hK2 V hV2 hVK β hβpos (ρc τ) (hρc.cont.1 τ hτ.1)
      (hreal τ hτ.1) (fun x => (hprob τ hτ.1).nonneg x) ψ hψ).symm
  obtain ⟨hc1, hc2⟩ := continuousOn_pairings hd s H.hs0 H.hsd K hK2 V ρ₀ H.hV β⁻¹ ρc Hs ψ hψc
  have htT : t ∈ Icc 0 T := ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := 0) (b := t)
    (f := fun τ => ∫ x, ψ x * mfPath ρc τ x)
    (f' := fun τ => ∫ x, ψ x * toFun (mfRhsCoeff d s V β⁻¹ (ρc τ)) x) ht.1 (hc1.mono hsub)
    (fun x hx => (hasDerivAt_pairing hd s H.hs0 H.hsd K hK2 V ρ₀ H.hV β⁻¹ ρc Hs ψ hψc
      ⟨hx.1, hx.2.trans_le ht.2⟩).hasDerivWithinAt)
    ((hc2.mono (by rw [Set.uIcc_of_le ht.1]; exact hsub)).intervalIntegrable)
  show pair (withDensityReal (mfPath ρc t)) ψ - pair (withDensityReal (mfPath ρc 0)) ψ = _
  rw [hPair t htT, hPair 0 ⟨le_rfl, hT.le⟩, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht.1]
  rw [intervalIntegral.integral_congr (g := fun r => ∫ x, ψ x * toFun (mfRhsCoeff d s V β⁻¹ (ρc r)) x)
    (fun r hr => by
      rw [Set.uIcc_of_le ht.1] at hr
      exact hW r (hsub hr))]
  exact hFTC.symm

end HRS.PDE.MFWeak
