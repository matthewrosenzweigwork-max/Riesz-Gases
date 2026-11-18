import HRS.PDE.MeanFieldGlobal
import HRS.PDE.MeanFieldAprioriLower
import HRS.PDE.MeanFieldThermal
import HRS.PDE.MeanFieldOneLe
import HRS.PDE.MeanFieldPairing
import HRS.PDE.Toolbox.CoeffBounds

/-!
# Decay of the finite-regularity mean-field solution, packet P7a1 (package MF-01)
(plan `MeanFieldDecayPlan.md`, §1 P7a1)

Static facts: two-sided bounds on thermal densities uniform in `β`, identification of
`g ⋆ ρ` with the coefficient multiplier `riesz`, the Euler-Lagrange equation in `Wpot` form,
Parseval identities, the free-energy gap identity, and the pointwise inequalities for
`a log (a/b) - (a-b)`.

**Statement problem (reported).**  The packet statement `freeEnergy'_sub_thermal` is mis-parsed
(`β⁻¹ * ∫ x, f x + (1/2) * ∑' …` is `β⁻¹ * ∫ x, (f x + (1/2) * ∑' …)`, false for `β ≠ 1`).  It is
replaced by `freeEnergy'_sub_thermal'` (integral parenthesised), proved below.

This file has no `sorry` and does not depend on the scaffold `mf_apriori_bound_real_on`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFDecay

open MFApriori

variable {d : ℕ}

/-! ### P7a1 — `MeanFieldDecayGap.lean`: thermal bounds, identifications, pointwise inequalities,
the gap identity -/

/-- (A1) Two-sided bounds on every continuous positive thermal density, uniform in `β ∈ [β₋,β₊]`. -/
theorem exists_thermal_bounds (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (V : Torus d → ℝ) (hV : Continuous V) :
    ∃ lam Lam : ℝ, 0 < lam ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → Continuous ρβ → (∀ x, 0 < ρβ x) →
      ∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam := by
  have F := MFThermalAssembly.kernelFacts hd s hs0 hsd
  obtain ⟨lam, Lam, hlam, hex⟩ := MFThermalExist.thermal_exists_of_truncated hd s hs0 hsd F V hV
    βm βp hβm hββ (fun β hβ N hN => MFThermalExist.exists_truncated_thermal hd s hs0 hsd F V hV β
      (lt_of_lt_of_le hβm hβ.1) N hN)
  refine ⟨lam, Lam, hlam, fun β hβ ρβ hρβ hc hp x => ?_⟩
  obtain ⟨ρ', hρ', hc', hb⟩ := hex β hβ
  have hpos' : ∀ x, 0 < ρ' x := fun x => lt_of_lt_of_le hlam (hb x).1
  have := MFThermalExist.thermal_unique' hd s hs0 hsd F β (lt_of_lt_of_le hβm hβ.1) V ρβ ρ'
    hρβ hc hp hρ' hc' hpos'
  rw [← this]
  exact hb x

/-- (A2) `g ⋆ ρ` (function convolution) is `riesz d s (coeffOf ρ)` (coefficient multiplier). -/
theorem riesz_coeffOf_eq_convFun (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 < K) (ρ : Torus d → ℝ) (hρ : Continuous ρ) (hmem : MemHs K (coeffOf ρ)) :
    riesz d s (coeffOf ρ) = convFun (periodicRiesz d s) ρ := by
  have hrc : IsRealCoeff (coeffOf ρ) :=
    isRealCoeff_coeffOf ρ (MFThermalReg.integrable_of_cont hρ)
  have hRm : MemHs K (rieszMult d s (coeffOf ρ)) := (hs_rieszMult s hsd K _ hmem).1
  have hRr : IsRealCoeff (rieszMult d s (coeffOf ρ)) := isRealCoeff_rieszMult s _ hrc
  have hsum : Summable fun k => ‖rieszMult d s (coeffOf ρ) k‖ := summable_norm_of_memHs K hK _ hRm
  have hcont : Continuous (riesz d s (coeffOf ρ)) := MFProduct.continuous_toFun _ hsum
  have hcont2 : Continuous (convFun (periodicRiesz d s) ρ) :=
    MFAux.continuous_convFun (MFOneLe.integrable_periodicRiesz hd s hs0 hsd) hρ
  refine MFAux.eq_of_funFourierCoeff_eq hcont hcont2 fun k => ?_
  have h1 : coeffOf (riesz d s (coeffOf ρ)) = rieszMult d s (coeffOf ρ) :=
    coeffOf_toFun _ hRr hsum
  have h2 := MFOneLe.coeffOf_convFun hd s hs0 hsd hρ k
  have h3 := congrFun h1 k
  unfold coeffOf at h2 h3 ⊢
  rw [h3, h2]
  rfl

/-- (A3) The Euler–Lagrange equation in the `Wpot` form: `β⁻¹ log ρ_β + V + g⋆ρ_β` is constant. -/
theorem thermal_log_add_Wpot_const (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 < K) (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hc : Continuous ρβ)
    (hp : ∀ x, 0 < ρβ x) (hmem : MemHs K (coeffOf ρβ)) :
    ∃ μ : ℝ, ∀ x, β⁻¹ * Real.log (ρβ x) + Wpot d s V (coeffOf ρβ) x = μ := by
  obtain ⟨c, hc'⟩ := MFThermal.log_thermal hρβ hp
  have hβ0 : β ≠ 0 := hβ.ne'
  have hK' : (d : ℝ) / 2 < K := hK
  refine ⟨β⁻¹ * c, fun x => ?_⟩
  have h1 := hc' x
  have h2 := riesz_coeffOf_eq_convFun hd s hs0 hsd K hK' ρβ hc hmem
  unfold Wpot
  rw [h1, congrFun h2 x]
  field_simp
  ring

/-- (A2b) The force `∇g⋆ρ` (cancellation convention) is the gradient of `riesz d s (coeffOf ρ)`. -/
theorem convGradConv_eq_grad_riesz (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 1 < K) (ρ : Torus d → ℝ) (hρ : Torus.IsCk 1 ρ)
    (hmem : MemHs K (coeffOf ρ)) (x : Torus d) :
    convGradConv (periodicRieszGrad d s) ρ x = Torus.grad (riesz d s (coeffOf ρ)) x := by
  have hK0 : (d : ℝ) / 2 < K := by linarith
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ
  have hreal : IsRealCoeff (coeffOf ρ) := isRealCoeff_coeffOf ρ (MFThermalReg.integrable_of_cont hρc)
  have heq := riesz_coeffOf_eq_convFun hd s hs0 hsd K hK0 ρ hρc hmem
  have hCk : Torus.IsCk 1 (convFun (periodicRiesz d s) ρ) := by
    rw [← heq]
    exact (riesz_isCk hd s hs0 hsd 1 K (by simpa using hK) _ hmem hreal).1
  ext j
  rw [MFOneLe.convGradConv_eq_partialDeriv hd s hs0 hsd hρ hCk j x, MFAux.grad_apply, heq]

/-- Real Parseval: for a real coefficient `c = coeffOf w` with `w` continuous,
`∑ ‖c k‖² = ∫ w²`. -/
theorem hasSum_norm_sq_coeffOf (w : Torus d → ℝ) (hw : Continuous w) :
    HasSum (fun k : Lattice d => ‖coeffOf w k‖ ^ 2) (∫ x, w x ^ 2) := by
  have h := hasSum_pairing' hw hw
  have hr := isRealCoeff_coeffOf w (MFThermalReg.integrable_of_cont hw)
  have e : ∀ k : Lattice d, coeffOf w (-k) * coeffOf w k = ((‖coeffOf w k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [hr k, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e] at h
  have h2 : HasSum (fun k : Lattice d => ‖coeffOf w k‖ ^ 2) (∫ x, w x * w x) :=
    Complex.hasSum_ofReal.mp h
  simpa [sq] using h2

/-- (A4a) `∫ (a - b)² = ‖â - b̂‖²_{H⁰}` for continuous `a, b` (Parseval). -/
theorem hsNormSq_zero_coeffOf_sub (a b : Torus d → ℝ) (ha : Continuous a) (hb : Continuous b) :
    MemHs 0 (coeffOf a - coeffOf b) ∧
      hsNormSq 0 (coeffOf a - coeffOf b) = ∫ x, (a x - b x) ^ 2 := by
  have hw : Continuous (fun x => a x - b x) := ha.sub hb
  have hco : coeffOf (fun x => a x - b x) = coeffOf a - coeffOf b := by
    funext k
    exact coeffOf_sub a b ha hb k
  rw [← hco]
  have h := hasSum_norm_sq_coeffOf _ hw
  have h0 : ∀ k : Lattice d, sobWeight 0 k * ‖coeffOf (fun x => a x - b x) k‖ ^ 2 =
      ‖coeffOf (fun x => a x - b x) k‖ ^ 2 := fun k => by
    rw [Aux.sobWeight_zero_aux, one_mul]
  refine ⟨?_, ?_⟩
  · unfold MemHs
    simp_rw [h0]
    exact h.summable
  · unfold hsNormSq
    simp_rw [h0]
    exact h.tsum_eq

/-- The bilinear Parseval pairing: for real `H^K` coefficient sequences `a, b`
(`K > d/2`), `∑_k ĝ(k) Re(conj(a k) b k) = ∫ toFun a · riesz b`. -/
theorem hasSum_cross (s : ℝ) (hsd : s < d) (K : ℝ) (hK : (d : ℝ) / 2 < K) (a b : Coeff d)
    (ha : MemHs K a) (hb : MemHs K b) (hareal : IsRealCoeff a) (hbreal : IsRealCoeff b) :
    HasSum (fun k : Lattice d => rieszCoeff d s k * (conj (a k) * b k).re)
      (∫ x, toFun a x * riesz d s b x) := by
  have hsa : Summable fun k => ‖a k‖ := summable_norm_of_memHs K hK a ha
  have hRm : MemHs K (rieszMult d s b) := (hs_rieszMult s hsd K b hb).1
  have hRr : IsRealCoeff (rieszMult d s b) := isRealCoeff_rieszMult s b hbreal
  have hsR : Summable fun k => ‖rieszMult d s b k‖ := summable_norm_of_memHs K hK _ hRm
  have hu : Continuous (toFun a) := MFProduct.continuous_toFun _ hsa
  have hv : Continuous (riesz d s b) := MFProduct.continuous_toFun _ hsR
  have h := hasSum_pairing' hu hv
  have e1 : coeffOf (toFun a) = a := coeffOf_toFun a hareal hsa
  have e2 : coeffOf (riesz d s b) = rieszMult d s b := coeffOf_toFun _ hRr hsR
  rw [e1, e2] at h
  have h2 := Complex.hasSum_re h
  rw [Complex.ofReal_re] at h2
  convert h2 using 2 with k
  rw [hareal k]
  simp only [rieszMult]
  rw [show conj (a k) * ((rieszCoeff d s k : ℝ) * b k : ℂ) =
      (rieszCoeff d s k : ℝ) * (conj (a k) * b k) by ring, Complex.re_ofReal_mul]

/-- The Parseval form of the interaction energy: `∑ ĝ(k) ‖c k‖² = ∫ toFun c · riesz c`. -/
theorem hasSum_interaction (s : ℝ) (hsd : s < d) (K : ℝ) (hK : (d : ℝ) / 2 < K) (c : Coeff d)
    (hc : MemHs K c) (hreal : IsRealCoeff c) :
    HasSum (fun k : Lattice d => rieszCoeff d s k * ‖c k‖ ^ 2)
      (∫ x, toFun c x * riesz d s c x) := by
  have h := hasSum_cross s hsd K hK c c hc hc hreal hreal
  convert h using 2 with k
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- (A4b) The interaction form of a real coefficient sequence is `∫ u (g⋆u)`:
`∑ ĝ(k)|ĉ(k)|² = ∫ toFun c · riesz c`. -/
theorem interaction_eq_integral (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 < K) (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) :
    ∑' k, rieszCoeff d s k * ‖c k‖ ^ 2 = ∫ x, toFun c x * riesz d s c x := by
  exact (hasSum_interaction s hsd K hK c hc hreal).tsum_eq

/-- Integration of `V ρ` when `V = μ - ν L - R` pointwise. -/
theorem integral_V_mul (V ρ L R : Torus d → ℝ) (μ ν : ℝ)
    (hV : ∀ x, V x = μ - ν * L x - R x) (hρ : Continuous ρ) (hL : Continuous L)
    (hR : Continuous R) :
    ∫ x, V x * ρ x = μ * (∫ x, ρ x) - ν * (∫ x, ρ x * L x) - ∫ x, ρ x * R x := by
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e : ∀ x, V x * ρ x = μ * ρ x - ν * (ρ x * L x) - ρ x * R x := fun x => by
    rw [hV x]; ring
  simp_rw [e]
  have h1 : Integrable fun x => μ * ρ x := hint _ (by fun_prop)
  have h2 : Integrable fun x => ν * (ρ x * L x) := hint _ (by fun_prop)
  have h3 : Integrable fun x => ρ x * R x := hint _ (by fun_prop)
  have h12 : Integrable fun x => μ * ρ x - ν * (ρ x * L x) := h1.sub h2
  rw [integral_sub h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul]

/-- (A4, corrected) The free-energy gap: `F(ρ) - F(ρ_β) = ν ∫ ρ log(ρ/ρ_β) + ½ ∑ ĝ |ρ̂ - ρ̂_β|²`
(`ν = β⁻¹`; the EL equation (A3) and mass one of both densities).

The packet statement `freeEnergy'_sub_thermal` was **mis-parsed**: its right-hand side
`β⁻¹ * ∫ x, toFun c x * (…) + (1 / 2 : ℝ) * ∑' …` parses as `β⁻¹ * ∫ x, (… + (1/2) * ∑' …)`, i.e.
`β⁻¹ * (∫ ρ log(ρ/ρ_β) + ½ ∑ …)` (the torus has volume one), which differs from the intended
identity by the factor `β⁻¹` on the interaction term and is false for `β ≠ 1`.  The statement below
is the intended one, with the integral parenthesised. -/
theorem freeEnergy'_sub_thermal' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℝ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) (β : ℝ) (hβ : 0 < β)
    (c : Coeff d) (hc : MemHs K c) (hreal : IsRealCoeff c) (hpos : ∀ x, 0 < toFun c x)
    (h0 : c 0 = 1) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hρc : Continuous ρβ) (hρp : ∀ x, 0 < ρβ x) (hmem : MemHs K (coeffOf ρβ)) :
    freeEnergy' d s V β⁻¹ c - freeEnergy' d s V β⁻¹ (coeffOf ρβ) =
      β⁻¹ * (∫ x, toFun c x * (Real.log (toFun c x) - Real.log (ρβ x))) +
        (1 / 2 : ℝ) * ∑' k, rieszCoeff d s k * ‖c k - coeffOf ρβ k‖ ^ 2 := by
  have hK0 : (d : ℝ) / 2 < K := by linarith
  have hint : ∀ f : Torus d → ℝ, Continuous f → Integrable f := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Summable fun k => ‖c k‖ := summable_norm_of_memHs K hK0 c hc
  have hsb : Summable fun k => ‖coeffOf ρβ k‖ := summable_norm_of_memHs K hK0 _ hmem
  have hρ : Continuous (toFun c) := MFProduct.continuous_toFun c hs
  have hVc : Continuous V := MFAux.continuous_of_isCk (hV.of_le (by norm_num))
  have hrealβ : IsRealCoeff (coeffOf ρβ) := isRealCoeff_coeffOf ρβ (hint _ hρc)
  have hρβeq : toFun (coeffOf ρβ) = ρβ := toFun_coeffOf ρβ hρc hsb
  have hRm : MemHs K (rieszMult d s (coeffOf ρβ)) := (hs_rieszMult s hsd K _ hmem).1
  have hsR : Summable fun k => ‖rieszMult d s (coeffOf ρβ) k‖ := summable_norm_of_memHs K hK0 _ hRm
  have hRc : Continuous (riesz d s (coeffOf ρβ)) := MFProduct.continuous_toFun _ hsR
  have hlogρ : Continuous fun x => Real.log (toFun c x) := hρ.log fun x => (hpos x).ne'
  have hlogβ : Continuous fun x => Real.log (ρβ x) := hρc.log fun x => (hρp x).ne'
  obtain ⟨μ, hμ⟩ := thermal_log_add_Wpot_const hd s hs0 hsd K hK0 V β hβ ρβ hρβ hρc hρp hmem
  have hVx : ∀ x, V x = μ - β⁻¹ * Real.log (ρβ x) - riesz d s (coeffOf ρβ) x := fun x => by
    have := hμ x
    unfold Wpot at this
    linarith
  have hmass : ∫ x, toFun c x = 1 := integral_toFun_eq_one K hK0 c hc hreal h0
  have hmassβ : ∫ x, ρβ x = 1 := hρβ.1.integral_one
  have e1 := integral_V_mul V (toFun c) _ _ μ β⁻¹ hVx hρ hlogβ hRc
  have e2 := integral_V_mul V ρβ _ _ μ β⁻¹ hVx hρc hlogβ hRc
  rw [hmass] at e1
  rw [hmassβ] at e2
  have hI := hasSum_interaction s hsd K hK0 c hc hreal
  have hIβ := hasSum_interaction s hsd K hK0 _ hmem hrealβ
  rw [hρβeq] at hIβ
  have hP := hasSum_cross s hsd K hK0 c _ hc hmem hreal hrealβ
  have hD : HasSum (fun k : Lattice d => rieszCoeff d s k * ‖c k - coeffOf ρβ k‖ ^ 2)
      ((∫ x, toFun c x * riesz d s c x) - 2 * (∫ x, toFun c x * riesz d s (coeffOf ρβ) x) +
        ∫ x, ρβ x * riesz d s (coeffOf ρβ) x) := by
    have := (hI.sub (hP.mul_left 2)).add hIβ
    convert this using 2 with k
    have hre : (c k * conj (coeffOf ρβ k)).re = (conj (c k) * coeffOf ρβ k).re := by
      rw [← Complex.conj_re (c k * conj (coeffOf ρβ k))]
      simp
    have hn : ‖c k - coeffOf ρβ k‖ ^ 2 = ‖c k‖ ^ 2 - 2 * (conj (c k) * coeffOf ρβ k).re +
        ‖coeffOf ρβ k‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_sub, hre]
      ring
    rw [hn]; ring
  rw [hD.tsum_eq]
  have hsplit : ∫ x, toFun c x * (Real.log (toFun c x) - Real.log (ρβ x)) =
      (∫ x, toFun c x * Real.log (toFun c x)) - ∫ x, toFun c x * Real.log (ρβ x) := by
    simp_rw [mul_sub]
    exact integral_sub (hint _ (hρ.mul hlogρ)) (hint _ (hρ.mul hlogβ))
  rw [hsplit]
  unfold freeEnergy'
  rw [interaction_re_eq, interaction_re_eq, hρβeq, e1, e2, hI.tsum_eq, hIβ.tsum_eq]
  ring

/-- (A5a) `a log(a/b) - (a - b) ≥ (a-b)²/(2M)` for `0 < a, b ≤ M`. -/
theorem mulLog_sub_ge {a b M : ℝ} (ha : 0 < a) (hb : 0 < b) (haM : a ≤ M) (hbM : b ≤ M) :
    (a - b) ^ 2 / (2 * M) ≤ a * (Real.log a - Real.log b) - (a - b) := by
  have hM : 0 < M := lt_of_lt_of_le hb hbM
  set f : ℝ → ℝ := fun r => r * (Real.log r - Real.log b) - (r - b) - (r - b) ^ 2 / (2 * M) with hf
  have hfd : ∀ r, 0 < r → HasDerivAt f (Real.log r - Real.log b - (r - b) / M) r := by
    intro r hr
    have h1 : HasDerivAt (fun r : ℝ => r * (Real.log r - Real.log b))
        (1 * (Real.log r - Real.log b) + r * r⁻¹) r :=
      (hasDerivAt_id r).mul (((Real.hasDerivAt_log hr.ne')).sub_const _)
    have h2 : HasDerivAt (fun r : ℝ => r - b) 1 r := (hasDerivAt_id r).sub_const b
    have h3 : HasDerivAt (fun r : ℝ => (r - b) ^ 2 / (2 * M)) (2 * (r - b) / (2 * M)) r := by
      have := (h2.pow 2).div_const (2 * M)
      simpa using this
    have := (h1.sub h2).sub h3
    convert this using 1
    field_simp
    ring
  have hf0 : f b = 0 := by simp [hf]
  have key : 0 ≤ f a := by
    rcases le_total b a with hba | hab
    · have hmono : MonotoneOn f (Set.Icc b M) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc b M) ?_ ?_ ?_
        · exact fun r hr => (hfd r (lt_of_lt_of_le hb hr.1)).continuousAt.continuousWithinAt
        · intro r hr
          rw [interior_Icc] at hr
          exact (hfd r (lt_trans hb hr.1)).differentiableAt.differentiableWithinAt
        · intro r hr
          rw [interior_Icc] at hr
          have hr0 : 0 < r := lt_trans hb hr.1
          rw [(hfd r hr0).deriv]
          have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hr0 hb)
          have h2 : Real.log (r / b) = Real.log r - Real.log b := Real.log_div hr0.ne' hb.ne'
          have h3 : 1 - (r / b)⁻¹ = (r - b) / r := by field_simp
          rw [h2, h3] at h1
          have h4 : (r - b) / M ≤ (r - b) / r :=
            div_le_div_of_nonneg_left (by linarith [hr.1]) hr0 hr.2.le
          linarith
      have := hmono ⟨le_rfl, hbM⟩ ⟨hba, haM⟩ hba
      linarith
    · have hanti : AntitoneOn f (Set.Ioc 0 b) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 b) ?_ ?_ ?_
        · exact fun r hr => (hfd r hr.1).continuousAt.continuousWithinAt
        · intro r hr
          rw [interior_Ioc] at hr
          exact (hfd r hr.1).differentiableAt.differentiableWithinAt
        · intro r hr
          rw [interior_Ioc] at hr
          rw [(hfd r hr.1).deriv]
          have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hb hr.1)
          have h2 : Real.log (b / r) = Real.log b - Real.log r := Real.log_div hb.ne' hr.1.ne'
          have h3 : 1 - (b / r)⁻¹ = (b - r) / b := by field_simp [hr.1.ne']
          rw [h2] at h1
          have h5 : 1 - (b / r)⁻¹ = (b - r) / b := by field_simp [hr.1.ne']
          have h4 : (b - r) / M ≤ (b - r) / b :=
            div_le_div_of_nonneg_left (by linarith [hr.2]) hb hbM
          have : (b - r) / M ≤ Real.log b - Real.log r := by linarith
          have e : (r - b) / M = -((b - r) / M) := by ring
          rw [e]
          linarith
      have := hanti ⟨ha, hab⟩ ⟨hb, le_rfl⟩ hab
      linarith
  simp only [hf] at key
  linarith

/-- (A5b) `a log(a/b) - (a - b) ≤ (a-b)²/b`. -/
theorem mulLog_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * (Real.log a - Real.log b) - (a - b) ≤ (a - b) ^ 2 / b := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h1
  have h2 : a * (Real.log a - Real.log b) ≤ a * (a / b - 1) :=
    mul_le_mul_of_nonneg_left h1 ha.le
  have h3 : a * (a / b - 1) - (a - b) = (a - b) ^ 2 / b := by field_simp
  linarith

/-- (A5c) `(log a - log b)(a - b) ≥ (a-b)²/M` for `0 < a, b ≤ M`. -/
theorem log_sub_mul_ge {a b M : ℝ} (ha : 0 < a) (hb : 0 < b) (haM : a ≤ M) (hbM : b ≤ M) :
    (a - b) ^ 2 / M ≤ (Real.log a - Real.log b) * (a - b) := by
  have hM : 0 < M := lt_of_lt_of_le hb hbM
  rcases le_total b a with h | h
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos ha hb)
    rw [Real.log_div ha.ne' hb.ne'] at h1
    have h3 : 1 - (a / b)⁻¹ = (a - b) / a := by field_simp
    rw [h3] at h1
    have h4 : (a - b) / M ≤ (a - b) / a :=
      div_le_div_of_nonneg_left (by linarith) ha haM
    have h5 : (a - b) / M ≤ Real.log a - Real.log b := h4.trans h1
    calc (a - b) ^ 2 / M = ((a - b) / M) * (a - b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h5 (by linarith)
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
    rw [Real.log_div hb.ne' ha.ne'] at h1
    have h3 : 1 - (b / a)⁻¹ = (b - a) / b := by field_simp
    rw [h3] at h1
    have h4 : (b - a) / M ≤ (b - a) / b :=
      div_le_div_of_nonneg_left (by linarith) hb hbM
    have h5 : (b - a) / M ≤ Real.log b - Real.log a := h4.trans h1
    calc (a - b) ^ 2 / M = ((b - a) / M) * (b - a) := by ring
      _ ≤ (Real.log b - Real.log a) * (b - a) := mul_le_mul_of_nonneg_right h5 (by linarith)
      _ = _ := by ring

/-- (A5d) The uniform bound `ĝ(k) ≤ gmax := |rieszConst| · 2^{(d-s)/2}` for all `k`. -/
theorem rieszCoeff_le_gmax (s : ℝ) (hsd : s < d) (k : Lattice d) :
    rieszCoeff d s k ≤ |rieszConst d s| * 2 ^ (((d : ℝ) - s) / 2) := by
  have h1 := MFThermalReg.abs_rieszCoeff_le_sobWeight s hsd k
  have h2 : sobWeight (-(((d : ℝ) - s) / 2)) k ≤ 1 := by
    have := sobWeight_le_of_le (d := d) (m := -(((d : ℝ) - s) / 2)) (n := 0)
      (by have : (0 : ℝ) < d - s := by linarith
          linarith) k
    simpa [sobWeight] using this
  have h3 : 0 ≤ |rieszConst d s| * (2 : ℝ) ^ (((d : ℝ) - s) / 2) := by positivity
  calc rieszCoeff d s k ≤ |rieszCoeff d s k| := le_abs_self _
    _ ≤ _ := h1
    _ ≤ |rieszConst d s| * (2 : ℝ) ^ (((d : ℝ) - s) / 2) * 1 :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = _ := mul_one _

end HRS.PDE.MFDecay
