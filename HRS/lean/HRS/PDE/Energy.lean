import HRS.PDE.ForwardEq
import HRS.PDE.EnergyAux
import HRS.PDE.EnergyTransport
import HRS.PDE.EnergyNonlocal
import HRS.PDE.EnergyR3
import HRS.PDE.GStructure
import HRS.PDE.EnergyR2Main

/-!
# Torus PDE layer V: algebraic structure of the nonlocal term and the a priori energy estimate

Sources (HRS periodic main paper, `B:sec:adjoint-algebra` and `B:sec:adjoint-apriori`):
* diagonalisation `B:eq:S-diag` (lines 1826–1829): `S = -∑_l λ_l q_l q_lᵀ`, `λ_l ≥ 0`,
  `(q_l)` orthonormal, `M^* = S - A` (`A = ½(M - Mᵀ)` antisymmetric);
  `D_l = q_l·∇`, `K_l = -g * D_l²` with symbol `𝔪_l` (`B:eq:Kl-def`, 1831–1834),
  `B_l(u,v) = ⟨K_l u, v⟩` (1835);
* Lemma 3.12 `B:lem:G-structure` (1837–1843);
* coefficient bounds `B:eq:coeff-bounds` (1861–1863; Lemma C.1);
* Proposition 3.13 `B:prop:energy-torus` (1865–1871) with the regime-wise proof
  (`B:eq:transport-est` 1880, `B:eq:R1-est` 1885, `B:eq:R2-total` 1930, `B:eq:R3-est` 1935);
* Proposition 3.14 `B:prop:R2c` (1942–1944), energy half.

## Representation decisions (SPEC_NOTES §1–2)

* Lemma 3.12 is an identity in `L²`, i.e. an identity of Fourier coefficients; it is stated for
  the coefficient operators of `ForwardEq.lean` for `μ ∈ C²` and `F ∈ H²`.
* Proposition 3.13 concerns `d/dτ ½‖F(τ)‖²_{H^m}` along the solution.  Its content is split into
  (a) the **form estimate** `energy_form_estimate` for real trigonometric polynomials (the only
  input the Fourier–Galerkin proof route needs; stated for every `m ∈ ℕ`, including `m = 0` which
  Step 4 of the proof of Prop 3.9 uses, line 1974), and
  (b) the **derivative statement** `energy_torus` for solutions regular enough for the derivative
  to exist (`F ∈ C([0,t];H^{m+2})`), which is the literal display `B:eq:energy-torus`.
  The `H^m` inner product of `B:eq:sobolev-def` is `∑_{|α|≤m} w_α ⟨∂^α·,∂^α·⟩` with multinomial
  weights `w_α ≥ 1` (`hsNormSq_eq_sum_derivL2Sq`), so the unweighted dissipation sums of the
  display are implied by the weighted ones.
* The retained weighted dissipation `B_l(√μ ∂^αF, √μ ∂^αF)` is `quadForm (symbolK q_l)` of the
  coefficients of `√μ ∂^αF`; its summability is part of the conclusion (no junk `tsum`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- The antisymmetric part `A = ½(M - Mᵀ)` (`M^* = S - A`, line 1828). -/
def antisymPart (M : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 / 2 : ℝ) • (M - M.transpose)

/-- A diagonalisation `S = -∑_l λ_l q_l q_lᵀ` of the symmetric part with `λ_l ≥ 0` and an
orthonormal basis `(q_l)` (`B:eq:S-diag`, line 1828; exists iff `S ≤ 0`). -/
structure IsSymDiag (M : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ) (q : Fin d → Euc d) : Prop where
  nonneg : ∀ l, 0 ≤ lam l
  orthonormal : Orthonormal ℝ q
  diag : ∀ i j, Torus.symPart M i j = -∑ l, lam l * q l i * q l j

/-- `D_q u = q·∇u` as a multiplier `2πi (q·k)`. -/
def dirDerivCoeff (q : Euc d) (c : Coeff d) : Coeff d :=
  fun k => (2 * Real.pi * Complex.I * (inner ℝ q (Lattice.toEuc k) : ℂ)) * c k

/-- `K_q u = -g * D_q² u`: the multiplier `𝔪_q(k) = (2π q·k)² ĝ(k)` (`B:eq:Kl-def`). -/
def KlCoeff (d : ℕ) (s : ℝ) (q : Euc d) (c : Coeff d) : Coeff d :=
  fun k => ((symbolK d s q k : ℝ) : ℂ) * c k

/-- `D_q g * u`: the multiplier `2πi (q·k) ĝ(k)`. -/
def dirGradRieszCoeff (d : ℕ) (s : ℝ) (q : Euc d) (c : Coeff d) : Coeff d :=
  dirDerivCoeff q (rieszMult d s c)

/-- The right-hand side of `B:eq:G-structure` (line 1840) in coefficients:
`∑_l λ_l (K_l(μF) + D_l g*(F D_lμ)) + ∑_{i,j} A_{ij} ∂_i g*(F ∂_jμ)`. -/
def GStructureRHS (D : DynData d) (lam : Fin d → ℝ) (q : Fin d → Euc d) (μ : Torus d → ℝ)
    (F : Coeff d) : Coeff d :=
  fun k => (∑ l : Fin d, ((lam l : ℝ) : ℂ) *
      (KlCoeff d D.s (q l) (mulCoeff (coeffOf μ) F) k +
        dirGradRieszCoeff d D.s (q l) (mulCoeff F (dirDerivCoeff (q l) (coeffOf μ))) k)) +
    ∑ i : Fin d, ∑ j : Fin d, ((antisymPart D.M i j : ℝ) : ℂ) *
      gradRieszCoeff d D.s i (mulCoeff F (derivCoeff j (coeffOf μ))) k

/-- Lemma 3.12 `B:lem:G-structure` (lines 1837–1843): for `μ ∈ C²(𝕋^d)`, `F ∈ H²(𝕋^d)` and a
diagonalisation `S = -∑ λ_l q_l q_lᵀ`, as an identity in `L²` (= identity of all Fourier
coefficients),
`𝒢[F] = ∑_l λ_l (K_l(μF) + D_l g*(F D_lμ)) + ∑_{i,j} A_{ij} ∂_i g*(F ∂_jμ)`.
(The lemma's standing frame is regime R2, `S ≤ 0`; the identity is algebraic and is stated for any
diagonalisation.)  The antisymmetric part contributes only through operators of order `θ-1 < 1`
applied to `F` times first derivatives of `μ` (line 1842). -/
theorem G_structure (hd : 1 ≤ d) (D : DynData d) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hdiag : IsSymDiag D.M lam q) (μ : Torus d → ℝ) (hμ : Torus.IsCk 2 μ) (F : Coeff d)
    (hF : MemHs 2 F) :
    nonlocalCoeff D μ F = GStructureRHS D lam q μ F := by
  have ha : MemHs 1 (coeffOf μ) :=
    (memHs_one_coeffOf_cbNorm 2 (by norm_num) μ (by exact_mod_cast hμ)).1
  have hF1 : MemHs 1 F := hF.mono (by norm_num)
  have hM : ∀ i j, D.M j i = -(∑ l, lam l * q l i * q l j) - antisymPart D.M i j := by
    intro i j
    have := hdiag.diag i j
    simp only [Torus.symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul] at this
    simp only [antisymPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply,
      smul_eq_mul]
    linarith
  have hA : ∀ i j, antisymPart D.M i j = -antisymPart D.M j i := by
    intro i j
    simp only [antisymPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply,
      smul_eq_mul]
    ring
  funext k
  exact gstruct_mode D.s D.M (antisymPart D.M) lam q hM hA (coeffOf μ) F ha hF1 k

/-! ### The a priori estimate -/

/-- The retained weighted dissipation of `B:eq:energy-torus`:
`∑_{|α|≤m} ∑_l λ_l B_l(√μ ∂^αF, √μ ∂^αF)` in Fourier form. -/
def weightedDissipation (D : DynData d) (m : ℕ) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (μ : Torus d → ℝ) (F : Coeff d) : ℝ :=
  ∑ α ∈ multiIndices d m, ∑ l : Fin d, lam l *
    quadForm (symbolK d D.s (q l)) (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F))

/-- Summability of every term of `weightedDissipation` (so that it is not a junk `tsum`). -/
def WeightedDissipationFinite (D : DynData d) (m : ℕ) (q : Fin d → Euc d) (μ : Torus d → ℝ)
    (F : Coeff d) : Prop :=
  ∀ α ∈ multiIndices d m, ∀ l : Fin d,
    Summable fun k => symbolK d D.s (q l) k *
      ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F) k‖ ^ 2

/-- The right-hand side of `B:eq:energy-torus` (line 1868) evaluated at `F` with density `μ`:
`Λ_m ‖F‖²_{H^m} - (ν/2) ∑_{|α|≤m} ‖∇∂^αF‖²_{L²} - ½ ∑_{|α|≤m} ∑_l λ_l B_l(√μ∂^αF, √μ∂^αF)`,
the last sum present only in regime R2 (void in R2a since all `λ_l = 0`; not used in R1/R3). -/
def energyRHS (R : Regime) (Λm : ℝ) (D : DynData d) (m : ℕ) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (μ : Torus d → ℝ) (F : Coeff d) : ℝ :=
  Λm * hsNormSq m F - (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α F -
    (if R.IsR2 then (1 / 2) * weightedDissipation D m lam q μ F else 0)

/-! ### Auxiliary estimates of the proof of Prop 3.13 (one sorried lemma per group; all for real
trigonometric polynomials `F`, `w = ∂^αF`) -/

/-- `B:eq:transport-est` (line 1880): `|⟨∂^α(b·∇F), ∂^αF⟩| ≤ C ‖F‖²_{H^m}` for `|α| ≤ m`, with
`C = C(d,m,‖b‖_{C^{m+1}})`. -/
theorem transport_form_bound (hd : 1 ≤ d) (m : ℕ) (B : ℝ) :
    ∃ C : ℝ, ∀ (b : Fin d → Torus d → ℝ), (∀ j, Torus.IsCk (m + 1) (b j)) →
      (∀ j, Torus.cbNorm (m + 1) (b j) ≤ B) →
      ∀ (α : Fin d → ℕ), α ∈ multiIndices d m →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        |(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
            (fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j F) k) F).re| ≤ C * hsNormSq m F := by
  classical
  set K : ℝ := max B 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  refine ⟨∑ α ∈ multiIndices d m,
    ((d : ℝ) * (K / 2 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * K)), ?_⟩
  intro b hb hB α hα n F _ hF
  have hαm : ∑ i, α i ≤ m := (Finset.mem_filter.mp hα).2
  have h := transport_bound_fixed m K hK0 b
    (fun j => by have := hb j; unfold Torus.IsCk at this; push_cast; exact this)
    (fun j => (hB j).trans (le_max_left _ _)) α hαm F hF
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (hsNormSq_nonnegE _ _))
  refine Finset.single_le_sum (f := fun α : Fin d → ℕ =>
    ((d : ℝ) * (K / 2 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * K)))
    (fun α _ => ?_) hα
  positivity


/-- `B:eq:R1-est` (line 1885), regime R1 (`θ ≤ 0`): `‖∂^α 𝒢[F]‖_{L²} ≤ C ‖F‖_{H^m}`, hence
`|⟨∂^α𝒢[F], ∂^αF⟩| ≤ C ‖F‖²_{H^m}`. -/
theorem nonlocal_R1_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ (d : ℝ) - 2) (m : ℕ)
    (MB Λ : ℝ) :
    ∃ C : ℝ, ∀ (D : DynData d), D.s = s → MatBound MB D.M → ∀ (μ : Torus d → ℝ),
      Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∀ (α : Fin d → ℕ), α ∈ multiIndices d m →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        derivL2Sq α (nonlocalCoeff D μ F) ≤ C * hsNormSq m F := by
  classical
  refine ⟨∑ α' ∈ multiIndices d m, r1Const d s MB Λ α', ?_⟩
  intro D hDs hM μ hμ hΛ α hα n F _ hF
  have hαm : ∑ i, α i ≤ m := (Finset.mem_filter.mp hα).2
  have hμ' : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (Torus.lift μ) := by
    unfold Torus.IsCk at hμ; push_cast; exact hμ
  have e : derivL2Sq α (nonlocalCoeff D μ F) =
      ∑' k, ‖multiDerivCoeff α (nonlocalCoeff D μ F) k‖ ^ 2 := by
    unfold derivL2Sq
    refine tsum_congr fun k => ?_
    rw [norm_sq_multiDerivCoeff]
  rw [e]
  refine le_trans (Real.tsum_le_of_sum_le (fun k => sq_nonneg _) fun S =>
    nonlocal_R1_fixed s hs m MB Λ D hDs hM μ hμ' hΛ α hαm F hF S) ?_
  refine mul_le_mul_of_nonneg_right ?_ (hsNormSq_nonnegE _ _)
  exact Finset.single_le_sum (f := fun α' => r1Const d s MB Λ α') (fun α' _ => r1Const_nonneg s MB Λ α') hα


/-- `B:eq:R2-total` (line 1930), regime R2 (`0 < θ < 2`, `S ≤ 0`; cases R2a, R2b with `λ₀`):
`-⟨∂^α𝒢[F], w⟩ ≤ -½∑_l λ_l B_l(√μ w, √μ w) + C(1 + λ₀⁻¹ 1_{S≠0}) ‖F‖²_{H^m}`, `w = ∂^αF`. -/
theorem nonlocal_R2_bound (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d) (m : ℕ)
    (MB Λ : ℝ) (lam0 : ℝ) (hlam0 : 0 < lam0) :
    ∃ C : ℝ, ∀ (D : DynData d), D.s = s → MatBound MB D.M → Torus.SymNonpos D.M →
      ∀ (lam : Fin d → ℝ) (q : Fin d → Euc d), IsSymDiag D.M lam q →
      ∀ (μ : Torus d → ℝ), IsProbDensity μ → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      (Torus.symPart D.M = 0 ∨ ∀ x, lam0 ≤ μ x) →
      ∀ (α : Fin d → ℕ), α ∈ multiIndices d m →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        (∀ l, Summable fun k => symbolK d D.s (q l) k *
          ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F) k‖ ^ 2) ∧
        -(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
            (nonlocalCoeff D μ F) F).re ≤
          -(1 / 2) * ∑ l, lam l * quadForm (symbolK d D.s (q l))
              (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F)) +
            C * (1 + (if Torus.symPart D.M = 0 then 0 else lam0⁻¹)) * hsNormSq m F := by
  by_cases hs0 : 0 ≤ s
  · have hK : R2Aux.R2KernelFacts d s := by
      by_cases hd2 : 2 ≤ d
      · exact R2Aux.r2KernelFacts_of_two_le hd2 hs0 hsd
      · exact R2Aux.r2KernelFacts_one (by omega) hs0 hsd
    obtain ⟨C, hC0, hC⟩ := R2Aux.r2_main hd s hs0 hK hs1 hsd m MB Λ lam0 hlam0
    refine ⟨C, fun D hDs hM _ lam q hdiag μ hμ hμ3 hΛ hcase α hα n F hF hFt => ?_⟩
    obtain ⟨hsum, h⟩ := hC D hDs hM lam q hdiag.nonneg hdiag.orthonormal hdiag.diag μ hμ.nonneg
      hμ3 hΛ hcase α hα n F hF hFt
    refine ⟨hsum, h.trans ?_⟩
    have hN := hsNormSq_nonnegE (m : ℝ) F
    have hite : 0 ≤ (if Torus.symPart D.M = 0 then (0 : ℝ) else lam0⁻¹) := by
      split_ifs
      · exact le_rfl
      · exact (inv_pos.mpr hlam0).le
    nlinarith [mul_nonneg hC0 hN, mul_nonneg (mul_nonneg hC0 hite) hN]
  · -- no `DynData` with `D.s = s < 0` exists (`D.hs0`)
    refine ⟨0, fun D hDs => ?_⟩
    exact absurd (hDs ▸ D.hs0) hs0

/-- Regime R2c (Prop 3.14, proof lines 1946–1951), per-multi-index estimate with the weighted
dissipation retained: for `d-2 < s ≤ d-1` (`0 < θ ≤ 1`), `S ≤ 0` and **no lower bound on `μ`**,
`-⟨∂^α𝒢[F], w⟩ ≤ -½∑_l λ_l B_l(√μ w, √μ w) + C ‖F‖²_{H^m}`, `w = ∂^αF`.  The source proof expands
the Leibniz rule before the rewriting of Lemma 3.12, bounds the `γ ≠ 0` terms by `C‖F‖²_{H^m}`
(order `θ-1 ≤ 0`), and the leading parts by Lemma C.3(iii) (`-λ_l B_l(μw,w) = -λ_l B_l(√μw,√μw)
- λ_l E` with `|E| ≤ C‖w‖²`) and Lemma C.4; it then drops the nonnegative `B_l` terms, which gives
`energy_form_estimate_R2c`.  Keeping half of them gives this form, which is what the conclusion of
Prop 3.13 (invoked by Prop 3.14) requires in regime R2. -/
theorem nonlocal_R2c_bound (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 2 < s) (hs2 : s ≤ (d : ℝ) - 1)
    (m : ℕ) (MB Λ : ℝ) :
    ∃ C : ℝ, ∀ (D : DynData d), D.s = s → MatBound MB D.M → Torus.SymNonpos D.M →
      ∀ (lam : Fin d → ℝ) (q : Fin d → Euc d), IsSymDiag D.M lam q →
      ∀ (μ : Torus d → ℝ), IsProbDensity μ → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∀ (α : Fin d → ℕ), α ∈ multiIndices d m →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        (∀ l, Summable fun k => symbolK d D.s (q l) k *
          ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F) k‖ ^ 2) ∧
        -(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
            (nonlocalCoeff D μ F) F).re ≤
          -(1 / 2) * ∑ l, lam l * quadForm (symbolK d D.s (q l))
              (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F)) +
            C * hsNormSq m F := by
  by_cases hs0 : 0 ≤ s
  · have hsd : s < d := by linarith
    have hK : R2Aux.R2KernelFacts d s := by
      by_cases hd2 : 2 ≤ d
      · exact R2Aux.r2KernelFacts_of_two_le hd2 hs0 hsd
      · exact R2Aux.r2KernelFacts_one (by omega) hs0 hsd
    obtain ⟨C, hC⟩ := R2Aux.r2c_main hd s hs0 hK hs1 hs2 m MB Λ
    refine ⟨C, fun D hDs hM _ lam q hdiag μ hμ hμ3 hΛ α hα n F hF hFt => ?_⟩
    exact hC D hDs hM lam q hdiag.nonneg hdiag.orthonormal hdiag.diag μ hμ.nonneg hμ3 hΛ α hα n F
      hF hFt
  · -- no `DynData` with `D.s = s < 0` exists (`D.hs0`)
    refine ⟨0, fun D hDs => ?_⟩
    exact absurd (hDs ▸ D.hs0) hs0

/-- `B:eq:R3-est` (line 1935), regime R3: for `ν₀ > 0`,
`|⟨∂^α𝒢[F], w⟩| ≤ ν₀/(4(m+1)^d) ‖F‖²_{H^{m+1}} + C ν₀^{-θ/(2-θ)} ‖F‖²_{H^m}`, `C` independent of
`ν₀`. -/
theorem nonlocal_R3_bound (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d) (m : ℕ)
    (MB Λ : ℝ) :
    ∃ C : ℝ, ∀ (D : DynData d), D.s = s → MatBound MB D.M → ∀ (μ : Torus d → ℝ),
      Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ → ∀ (ν₀ : ℝ), 0 < ν₀ →
      ∀ (α : Fin d → ℕ), α ∈ multiIndices d m →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        |(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
            (nonlocalCoeff D μ F) F).re| ≤
          ν₀ / (4 * ((m : ℝ) + 1) ^ d) * hsNormSq (m + 1) F +
            C * ν₀ ^ (-(thetaOrder d s / (2 - thetaOrder d s))) * hsNormSq m F := by
  classical
  have hθ0 : 0 < s + 2 - d := by linarith
  have hθ2 : s + 2 - d < 2 := by linarith
  have hθ : thetaOrder d s = s + 2 - d := rfl
  set lam : ℝ := (s + 2 - d) / 2 with hlam
  have hl0 : 0 < lam := by rw [hlam]; linarith
  have hl1 : lam < 1 := by rw [hlam]; linarith
  set C₃ : ℝ := (∑ α' ∈ multiIndices d m, r3Const d s MB Λ α') + 1 with hC₃def
  have hC₃ : 0 < C₃ := by
    have : 0 ≤ ∑ α' ∈ multiIndices d m, r3Const d s MB Λ α' :=
      Finset.sum_nonneg fun α' _ => r3Const_nonneg s MB Λ α'
    rw [hC₃def]; linarith
  set K : ℝ := 4 * ((m : ℝ) + 1) ^ d with hK
  have hK0 : 0 < K := by positivity
  set e : ℝ := thetaOrder d s / (2 - thetaOrder d s) with he
  have hee : e = lam / (1 - lam) := by
    rw [he, hθ, hlam]
    have : (2 : ℝ) - (s + 2 - d) ≠ 0 := by linarith
    have h2 : (1 : ℝ) - (s + 2 - d) / 2 ≠ 0 := by linarith
    field_simp
  refine ⟨K ^ e * (C₃ * C₃ ^ e), ?_⟩
  intro D hDs hM μ hμ hΛ ν₀ hν₀ α hα n F _ hF
  have hαm : ∑ i, α i ≤ m := (Finset.mem_filter.mp hα).2
  have hμ' : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (Torus.lift μ) := by
    unfold Torus.IsCk at hμ; push_cast; exact hμ
  have key := nonlocal_R3_key s hθ0 hθ2 m MB Λ D hDs hM μ hμ' hΛ α hαm F hF
  set A := hsNormSq (m : ℝ) F with hAdef
  set Bq := hsNormSq ((m + 1 : ℕ) : ℝ) F with hBdef
  have hAB : A ≤ Bq := hsNormSq_mono_nat m F hF
  have hA0 : 0 ≤ A := hsNormSq_nonnegE _ _
  have hR0 : 0 ≤ A ^ (1 - lam) * Bq ^ lam :=
    mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg (hA0.trans hAB) _)
  have hr3 : r3Const d s MB Λ α ≤ C₃ := by
    have := Finset.single_le_sum (f := fun α' => r3Const d s MB Λ α')
      (fun α' _ => r3Const_nonneg s MB Λ α') hα
    rw [hC₃def]; linarith
  have h1 : |(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
        (nonlocalCoeff D μ F) F).re| ≤ C₃ * (A ^ (1 - lam) * Bq ^ lam) :=
    key.trans (mul_le_mul_of_nonneg_right hr3 hR0)
  have hε : 0 < ν₀ / K := div_pos hν₀ hK0
  have h2 := r3_absorb C₃ (A ^ (1 - lam) * Bq ^ lam) A Bq (ν₀ / K) lam e hC₃ hA0 hAB hε hl0 hl1
    hee rfl
  refine h1.trans (h2.trans ?_)
  have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hinv : (ν₀ / K)⁻¹ ^ e = K ^ e * ν₀ ^ (-e) := by
    rw [inv_div, Real.div_rpow hK0.le hν₀.le, Real.rpow_neg hν₀.le]
    ring
  rw [hinv, hcast]
  refine le_of_eq ?_
  ring


/-- The dissipation lower bound used to absorb `B:eq:R3-est` (line 1937):
`∑_{|α|≤m} ‖∇∂^αF‖²_{L²} ≥ c_{d,m} (‖F‖²_{H^{m+1}} - ‖F‖²_{H^m})`. -/
theorem gradDeriv_sum_lower (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : Coeff d, MemHs (m + 1) F →
      c * (hsNormSq (m + 1) F - hsNormSq m F) ≤ ∑ α ∈ multiIndices d m, gradDerivL2Sq α F := by
  refine ⟨(((d : ℝ) + 1) ^ m)⁻¹, by positivity, fun F hF => ?_⟩
  have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  set x : Lattice d → ℝ := fun k => 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hx
  have hx0 : ∀ k, 0 ≤ x k := fun k => enormSq_nonneg k
  have hFm : Summable fun k => sobWeight (m : ℝ) k * ‖F k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right (sobWeight_monoE (by linarith) k) (sq_nonneg _)) hF
  have hdiff : hsNormSq ((m : ℝ) + 1) F - hsNormSq (m : ℝ) F =
      ∑' k, (x k * (1 + x k) ^ m * ‖F k‖ ^ 2) := by
    unfold hsNormSq
    rw [← hF.tsum_sub hFm]
    refine tsum_congr fun k => ?_
    rw [hcast, sobWeight_natCast, sobWeight_natCast]
    simp only [hx]
    ring
  -- summability of the gradient terms
  have hterm : ∀ α ∈ multiIndices d m,
      Summable fun k => x k * (∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) * ‖F k‖ ^ 2 := by
    intro α hα
    have hαm : ∑ i, α i ≤ m := (Finset.mem_filter.mp hα).2
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hF
    · exact mul_nonneg (mul_nonneg (hx0 k) (weight_nonneg α k)) (sq_nonneg _)
    · rw [hcast, sobWeight_natCast]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h1 := weight_le_pow α k
      have h2 : (1 + x k) ^ (∑ i, α i) ≤ (1 + x k) ^ m :=
        pow_le_pow_right₀ (one_le_sobBaseE k) hαm
      calc x k * (∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
          ≤ (1 + x k) * (1 + x k) ^ m :=
            mul_le_mul (by linarith) (h1.trans h2) (weight_nonneg α k) (by linarith [hx0 k])
        _ = (1 + x k) ^ (m + 1) := by ring
  have hsum : ∑ α ∈ multiIndices d m, gradDerivL2Sq α F =
      ∑' k, ∑ α ∈ multiIndices d m,
        x k * (∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) * ‖F k‖ ^ 2 := by
    rw [Summable.tsum_finsetSum hterm]
    rfl
  rw [hsum, hdiff, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ (summable_sum hterm)
  · have hp := pow_le_sum_weight (d := d) m k
    have hxF : 0 ≤ x k * ‖F k‖ ^ 2 := mul_nonneg (hx0 k) (sq_nonneg _)
    have hpos : (0 : ℝ) < ((d : ℝ) + 1) ^ m := by positivity
    calc ((((d : ℝ) + 1) ^ m)⁻¹) * (x k * (1 + x k) ^ m * ‖F k‖ ^ 2)
        = ((((d : ℝ) + 1) ^ m)⁻¹ * (1 + x k) ^ m) * (x k * ‖F k‖ ^ 2) := by ring
      _ ≤ (∑ α ∈ multiIndices d m, ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) *
            (x k * ‖F k‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hxF
          rw [inv_mul_le_iff₀ hpos]; exact hp
      _ = _ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => by ring
  · refine (Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hF).mul_left _
    · exact mul_nonneg (mul_nonneg (hx0 k) (pow_nonneg (by linarith [hx0 k]) _)) (sq_nonneg _)
    · rw [hcast, sobWeight_natCast]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      calc x k * (1 + x k) ^ m ≤ (1 + x k) * (1 + x k) ^ m :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith [hx0 k]) _)
        _ = (1 + x k) ^ (m + 1) := by ring

end HRS.PDE
