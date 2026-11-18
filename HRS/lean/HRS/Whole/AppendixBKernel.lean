import HRS.Whole.Adjoint
import HRS.Whole.AppendixBEnergy

/-!
# Appendix S.B (whole-space supplement): screened kernel bounds and same-function symmetrization
(SPEC-WB)

Source: HRS whole-space supplement (S), Appendix S.B:

* S.B.4 `B:lem:screened` (S L11310-11331): `screened_far` (item (i)), `screened_local` and
  `screened_local_global` (item (ii)), `screened_pairing` and `screened_pairing_pos` (item (iii)), `screened_comm_local`,
  `screened_comm_cell` (item (iv));
* S.B.8 `B:lem:same-function` (S L11504-11512): `same_function_rd`, `same_function_rd_weighted`
  (items (i), (ii)).

## Representation decisions

* `K_g ∈ {∂_i g *}` (order `θ - 1 = s + 1 - d`) acts on functions through the distributional
  convolution `∂_i g * v := ∂_i (g * v)`: `IsGradKernelRep d s i v w` says `w` represents it
  (`∫ w φ = -∫ v (g * ∂_iφ)` for Schwartz `φ`); for `s < d-1` this is the absolutely convergent
  integral.  Far-field terms (kernel nonsingular) use the plain Bochner integral `gradGConvPlain`
  with integrability asserted in the conclusion.
* The *advected cutoffs* `χ_z^τ, χ̂_z^τ` (`B:eq:advected-cutoffs`, S L10082-10090) are
  `advCutoff χ Ψ τ z = χ(Ψ_τ^{-1}(·) - z)` where `Ψ` is any flow of `-b` (`IsNegDriftFlow`) of a drift
  `b` satisfying the bounds `B:eq:drift-bounds-rd` (`IsAdvectingDrift`, with constant `Cb`).  The drift
  of the supplement, `b^τ = M ∇g * μ^{t-τ} - ∇V`, satisfies these bounds with `Cb = Cb(d, s, m, |M|, Λ,
  Λ_V, |∇V(0)|)` (Lemma `B:lem:coefficient-bounds`), so the constants "`C_T` depending on
  `(d,s,m,|M|,Λ,Λ_V,|∇V(0)|,ν̄,T)`" are represented as constants depending on `(d, s, m, Λ, Cb, T)`; the
  statements hold for every drift with these bounds (the proof uses nothing else).  The lattice
  `z ∈ ℤ^d` indexes the cells (`latticePt`).  `ω_z = ⟨z⟩^{-(d+3)}` is `cellWeight`.
* Norms are in `ℝ≥0∞` where the quantity may be infinite (`sobolevNormE`, `eLpNorm`); the weighted sup
  `‖⟨·⟩^{d+3}a‖_∞ ≤ Λ` is the pointwise bound.
* `θ - 1 = s + 1 - d` is the order of `∂_i g *`, so `(θ-1)^+ = max (s + 1 - d) 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### Definitions -/

/-- `w` represents `∂_i g * v = ∂_i (g * v)` in the sense of distributions: for every Schwartz `φ`,
`∫ w φ = -∫ v (g * ∂_iφ)` (both integrals absolutely convergent), `g` the Riesz kernel `rieszKernel d s`
(even, so `(g * ∂_iφ)(y) = ∫ g(x-y) ∂_iφ(x) dx`). -/
def IsGradKernelRep (d : ℕ) (s : ℝ) (i : Fin d) (v w : Euc d → ℝ) : Prop :=
  ∀ φ : SchwartzMap (Euc d) ℝ,
    Integrable (fun x => w x * φ x) ∧
    Integrable (fun y => v y * convFun (rieszKernel d s)
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y) ∧
    ∫ x, w x * φ x = -∫ y, v y * convFun (rieszKernel d s)
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y

/-- The drift bounds `B:eq:drift-bounds-rd` (S L10078-10080) of the advecting drift `b^τ` on `[0,T]`:
`b` continuous in `(τ,x)`, `C^{m+1}` in `x`, `‖∇^{⊗j}b^τ‖_∞ ≤ Cb` for `1 ≤ j ≤ m+1`,
`|b^τ(x)| ≤ Cb (1+|x|)`. -/
structure IsAdvectingDrift (m : ℕ) (Cb T : ℝ) (b : ℝ → Euc d → Euc d) : Prop where
  cont : ContinuousOn (fun p : ℝ × Euc d => b p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ)
  smooth : ∀ τ ∈ Set.Icc 0 T, ContDiff ℝ (m + 1) (b τ)
  deriv_bdd : ∀ τ ∈ Set.Icc 0 T, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x,
    ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Cb
  growth : ∀ τ ∈ Set.Icc 0 T, ∀ x, ‖b τ x‖ ≤ Cb * (1 + ‖x‖)

/-- `Ψ` is the flow of `-b` on `[0,T]`: `∂_τ Ψ_τ(x) = -b^τ(Ψ_τ(x))`, `Ψ_0 = id`, each `Ψ_τ` a
bijection (a bi-Lipschitz diffeomorphism by `B:lem:uloc-bilip`). -/
structure IsNegDriftFlow (T : ℝ) (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) : Prop where
  init : ∀ x, Ψ 0 x = x
  ode : ∀ x, ∀ τ ∈ Set.Icc 0 T,
    HasDerivWithinAt (fun τ' => Ψ τ' x) (-(b τ (Ψ τ x))) (Set.Icc 0 T) τ
  bij : ∀ τ ∈ Set.Icc 0 T, Function.Bijective (Ψ τ)

/-- The cutoff pair of `B:eq:advected-cutoffs` (S L10083): `χ ∈ C_c^∞(B(0,2);[0,1])` with `χ ≡ 1` on
`B̄(0,1)` and `χ̂ ∈ C_c^∞(B(0,8);[0,1])` with `χ̂ ≡ 1` on `B̄(0,6)`. -/
def IsCutoffPair (χ χh : Euc d → ℝ) : Prop :=
  (ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Metric.ball 0 2 ∧
    (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ Metric.closedBall (0 : Euc d) 1, χ x = 1) ∧
  (ContDiff ℝ ∞ χh ∧ HasCompactSupport χh ∧ tsupport χh ⊆ Metric.ball 0 8 ∧
    (∀ x, χh x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ Metric.closedBall (0 : Euc d) 6, χh x = 1)

/-- The advected cutoff `χ_z^τ(x) = χ(Ψ_τ^{-1}(x) - z)` (`B:eq:advected-cutoffs`). -/
def advCutoff (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Euc d) (x : Euc d) : ℝ :=
  χ (Function.invFun (Ψ τ) x - z)

/-- The cell weight `ω_z = ⟨z⟩^{-(d+3)}`, `z ∈ ℤ^d` (`B:eq:screened-cell-kernel`). -/
def cellWeight (d : ℕ) (z : Fin d → ℤ) : ℝ := jbracket (latticePt z) ^ (-((d : ℝ) + 3))

/-- The cell `Q_{z'}^τ = Ψ_τ(z' + [0,1]^d)` of the bounded-overlap cover of `ℝ^d`
(`B:lem:uloc-bilip`(iv), S L11013-11020; `B:lem:screened` proof, S L11336-11338). -/
def flowCell (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Fin d → ℤ) : Set (Euc d) :=
  Ψ τ '' {y | ∀ i, 0 ≤ (y - latticePt z) i ∧ (y - latticePt z) i ≤ 1}

/-- The order `(θ-1)^+ = max (s+1-d) 0` of `∂_i g *`. -/
def kgOrder (d : ℕ) (s : ℝ) : ℝ := max (s + 1 - d) 0

/-! ### S.B.4 -/

/-- Lemma S.B.4(i) (`B:lem:screened`, `B:item:screened-far`, TeX S L11313-11326): far field and weighted
cell kernel.  `0 ≤ s < d`, `m ≥ 0`, `μ` satisfying `S:eq:mf-regularity-whole` at level `m+3` (the
decay part is what is used; `IsRegularDensityW (m+3) Λ μ`), an advecting drift `b` with its flow `Ψ`,
`0 ≤ τ ≤ T`, and the cutoffs `χ_z^τ, χ̂_z^τ`.  There are nonnegative coefficients `K^τ_{zz'}`
(`z,z' ∈ ℤ^d`) with `sup_z ∑_{z'} K^τ_{zz'} ≤ C_T`, `∑_z ω_z K^τ_{zz'} ≤ C_T ω_{z'}`
(`B:eq:screened-cell-kernel`) such that for every `0 ≤ j ≤ m+1`, every derivative `∂^α` of order `j`
and every `ψ`,
`‖χ_z^τ K_g((1-χ̂_z^τ) ∂^αμ ψ)‖₂² ≤ C_T Λ² ∑_{z'} K^τ_{zz'} ‖1_{Q_{z'}^τ} ψ‖₂²` (TeX: `‖χ_{z'}^τ ψ‖₂²`, see SUSPECTED ISSUE)
(`B:eq:screened-cell-estimate`), `K_g = ∂_i g *` (plain absolutely convergent integral on the support of
`χ_z^τ`: integrability is part of the conclusion whenever the right side is finite).  `C_T` depends only
on `d, s, m, Λ, Cb, T` (quantified first); `K^τ` depends on `τ` and the data but not on `j, α, ψ, i`.
Technical hypotheses: `ψ` measurable; `Λ ≥ 0` (implied).  The cutoff pair `χ, χ̂` is fixed *before* the
constant (TeX S L10081: the cutoffs are fixed once, `C_T` may depend on them).  The "in particular"
clause (`LHS ≤ C_T Λ² sup_{z'} ‖ψ‖_{L²(cell z')}²`) follows from the row-sum bound and is not restated.
SUSPECTED ISSUE (S L11322-11326, proof L11336-11346): the TeX right side is `∑_{z'} K^τ_{zz'}
‖χ_{z'}^τ ψ‖₂²` with `χ_{z'}^τ` supported in `Ψ_τ(z'+B(0,2))`, but the proof applies Cauchy-Schwarz on the
*cells* `Q_{z'}^τ = Ψ_τ(z'+[0,1]^d)` (S L11337-11340), which are not contained in `{χ_{z'}^τ = 1}` (the
cube `[0,1]^d` has diameter `√d`), and for `d ≥ 16` the supports `B(z',2)`, `z' ∈ ℤ^d`, do not even cover
`ℝ^d` (`√d/2 ≥ 2`), so the cutoff form fails (take `ψ` supported in a gap).  The statement is therefore
drafted with what the proof proves: `‖1_{Q_{z'}^τ} ψ‖₂²` (`flowCell`) on the right.  (A lattice fine
enough for the cutoff would also repair it.) -/
theorem screened_far (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ Cb T : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ →
      ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal C) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal C * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (i : Fin d) (ψ : Euc d → ℝ), Measurable ψ →
          ∀ z : Fin d → ℤ,
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z) x *
                gradGConvPlain d s (fun y => (1 - advCutoff χh Ψ τ (latticePt z) y) *
                  (partialDeriv idx μ y * ψ y)) x i) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 ∧
            (ENNReal.ofReal (C * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 < ⊤ →
              ∀ x ∈ tsupport (advCutoff χ Ψ τ (latticePt z)),
                Integrable (fun y => rieszKernelGrad d s (x - y) i *
                  ((1 - advCutoff χh Ψ τ (latticePt z) y) * (partialDeriv idx μ y * ψ y)))) := by
  sorry

/-- Lemma S.B.4(ii), first assertion (`B:lem:screened`, `B:item:screened-local`, TeX S L11327-11328):
local bounds.  For `v` supported in a ball of radius `ρ ≥ 1` and any ball `B ⊂ ℝ^d` of radius `≤ ρ`,
`‖1_B K_g v‖_{L²} ≤ C ρ^{C₀} ‖v‖_{H^{(θ-1)^+}}`, `C₀ = C₀(d,s)`, `C = C(d,s)`
(`kgOrder d s = (θ-1)^+`, `K_g = ∂_i g *`); the existence of the `L²_{loc}` function `K_g v`
(`IsGradKernelRep`) is part of the conclusion. -/
theorem screened_local (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, ∀ (i : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (v : Euc d → ℝ),
      Function.support v ⊆ Metric.closedBall c ρ → sobolevNormE (kgOrder d s) v < ⊤ →
      ∃ w : Euc d → ℝ, IsGradKernelRep d s i v w ∧
        ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
          eLpNorm ((Metric.closedBall c' r').indicator w) 2 volume ≤
            ENNReal.ofReal (C * ρ ^ C₀) * sobolevNormE (kgOrder d s) v := by
  sorry

/-- Lemma S.B.4(ii), second assertion (`B:lem:screened`, `B:item:screened-local`, TeX S L11328-11329):
if `s ≥ d - 1` the global bound `‖K_g v‖_{L²(ℝ^d)} ≤ C ‖v‖_{H^{θ-1}}` holds with no support restriction
(`H^{θ-1} = H^{s+1-d}`; existence of the `L²` function `K_g v` is part of the conclusion). -/
theorem screened_local_global (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (hs1 : (d : ℝ) - 1 ≤ s) :
    ∃ C : ℝ, ∀ (i : Fin d) (v : Euc d → ℝ), sobolevNormE (s + 1 - d) v < ⊤ →
      ∃ w : Euc d → ℝ, IsGradKernelRep d s i v w ∧ MemLp w 2 volume ∧
        eLpNorm w 2 volume ≤ ENNReal.ofReal C * sobolevNormE (s + 1 - d) v := by
  sorry

/-- Lemma S.B.4(iii) (`B:lem:screened`, `B:item:screened-global`, TeX S L11329-11330), the case
`s ≤ d-1` (`2(s+1) > d`; `θ - 1 ≤ 0`): screened pairing, unweighted decaying scale.  For `a` with
`‖⟨·⟩^{d+3}a‖_{L^∞} ≤ Λ` and `ψ, w ∈ L²`: `|⟨K_g(aψ), w⟩| ≤ C Λ ‖ψ‖_{L²} ‖w‖_{L²}`, `C = C(d,s)`
(`sobolevNormE (kgOrder d s) ψ` is the `L²` norm here).  `K_g(aψ)` is a representative `u`
(`IsGradKernelRep`) of the `L²` function (technical hypothesis `u ∈ L²`, so that the pairing with
`w ∈ L²` is the genuine integral; automatic for `s < d-1`).  (The "false if `2(s+1) ≤ d`" sentence refers
to `B:prop:low-frequency-obstruction`, S.A.14.)  The case `s > d-1` is `screened_pairing_pos`. -/
theorem screened_pairing (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 1)
    (h2 : (d : ℝ) < 2 * (s + 1)) :
    ∃ C : ℝ, ∀ (Λ : ℝ) (a : Euc d → ℝ), (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) →
      ∀ (i : Fin d) (ψ w u : Euc d → ℝ), MemLp ψ 2 volume → MemLp w 2 volume →
      sobolevNormE (kgOrder d s) ψ < ⊤ → MemLp u 2 volume →
      IsGradKernelRep d s i (fun y => a y * ψ y) u →
        ENNReal.ofReal |∫ x, u x * w x| ≤
          ENNReal.ofReal (C * Λ) * sobolevNormE (kgOrder d s) ψ * eLpNorm w 2 volume := by
  sorry

/-- Lemma S.B.4(iii) (`B:lem:screened`, `B:item:screened-global`, TeX S L11329-11330), the case
`s > d-1` (`θ - 1 > 0`, `K_g` of positive order `s+1-d ∈ (0,1)`), with the repair: the constant contains
`‖a‖_{W^{1,∞}}` (`≤ La + Λ`: Lipschitz constant `La` and weighted bound `Λ`), since multiplication by a
`W^{1,∞}` function is bounded on `H^{θ-1}`, `0 ≤ θ - 1 < 1`.  For `ψ ∈ H^{θ-1}`, `w ∈ L²`, every
representative `u` of `K_g(aψ)` lies in `L²` and
`|⟨K_g(aψ), w⟩| ≤ C (La + Λ) ‖ψ‖_{H^{θ-1}} ‖w‖_{L²}`, `C = C(d,s)` (no `u ∈ L²` hypothesis).
SUSPECTED ISSUE (S L11327-11330, proof L11362): the TeX asserts the bound with `Λ` alone
(`‖⟨·⟩^{d+3}a‖_∞ ≤ Λ`) also for `s > d-1`, applying the local estimate (ii) to `aψ`; for rough `a` this
fails (`a = Λ⟨x⟩^{-d-3} cos(λ x_1)`, `ψ` fixed: `‖K_g(aψ)‖ ~ λ^{θ-1}` as `λ → ∞`), because `aψ ∈ H^{θ-1}`
does not follow from `ψ ∈ H^{θ-1}` and `a ∈ L^∞`.  In the application `a = ∂^αμ` is smooth. -/
theorem screened_pairing_pos (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (hs1 : (d : ℝ) - 1 < s) :
    ∃ C : ℝ, ∀ (La Λ : ℝ) (a : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La a →
      (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) →
      ∀ (i : Fin d) (ψ w u : Euc d → ℝ), MemLp ψ 2 volume → MemLp w 2 volume →
      sobolevNormE (s + 1 - d) ψ < ⊤ →
      IsGradKernelRep d s i (fun y => a y * ψ y) u →
        MemLp u 2 volume ∧
        ENNReal.ofReal |∫ x, u x * w x| ≤
          ENNReal.ofReal (C * (La + Λ)) * sobolevNormE (s + 1 - d) ψ * eLpNorm w 2 volume := by
  sorry

/-- Lemma S.B.4(iv), local part (`B:lem:screened`, `B:item:screened-comm`, TeX S L11331): cutoff
commutators.  The kernels `∂_ig(x-y) χ_z^τ(x)(χ̂_z^τ(y) - χ_z^τ(y))` and `∂_ig(x-y)(χ_z^τ(x) - χ_z^τ(y))`
obey the local bounds of (ii) with constants `C(τ) = C e^{Cdτ}`: for `v` supported in a ball of radius
`ρ ≥ 1` and any ball `B` of radius `≤ ρ` (any `z ∈ ℝ^d`, `0 ≤ τ ≤ T`), writing `T₁v = χ_z K_g((χ̂_z -
χ_z) v)` and `T₂v = χ_z K_g v - K_g(χ_z v)` (the operators with the two kernels),
`‖1_B T_k v‖_{L²} ≤ C e^{Cdτ} ρ^{C₀} ‖v‖_{H^{(θ-1)^+}}` (`k = 1, 2`); the `L²_{loc}` representatives
`K_g(·)` exist.  AMBIGUITY: "obey the same `L² → L²` sup-cell bounds as (i)-(ii)" is vague; it is
drafted as the local bound (ii) (this statement) and, for `s < d-1` where the kernels are locally
integrable, the cell-sum bound of (i) (`screened_comm_cell`).  The constants `C, C₀` depend on the
drift bounds `(m, Cb, T)`. -/
theorem screened_comm_local (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Cb T : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C₀ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : Euc d, ∀ (i : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (v : Euc d → ℝ),
      Function.support v ⊆ Metric.closedBall c ρ → sobolevNormE (kgOrder d s) v < ⊤ →
      ∃ w₁ w₂ w₃ : Euc d → ℝ,
        IsGradKernelRep d s i (fun y => (advCutoff χh Ψ τ z y - advCutoff χ Ψ τ z y) * v y) w₁ ∧
        IsGradKernelRep d s i v w₂ ∧
        IsGradKernelRep d s i (fun y => advCutoff χ Ψ τ z y * v y) w₃ ∧
        ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
          eLpNorm ((Metric.closedBall c' r').indicator
              (fun x => advCutoff χ Ψ τ z x * w₁ x)) 2 volume ≤
            ENNReal.ofReal (C * Real.exp (C * d * τ) * ρ ^ C₀) * sobolevNormE (kgOrder d s) v ∧
          eLpNorm ((Metric.closedBall c' r').indicator
              (fun x => advCutoff χ Ψ τ z x * w₂ x - w₃ x)) 2 volume ≤
            ENNReal.ofReal (C * Real.exp (C * d * τ) * ρ ^ C₀) * sobolevNormE (kgOrder d s) v := by
  sorry

/-- Lemma S.B.4(iv), cell-sum part (`B:lem:screened`, `B:item:screened-comm`, TeX S L11331), for
`s < d - 1` (kernels locally integrable, so the plain integrals converge absolutely): for the kernels
`χ_z^τ(x)(χ̂_z^τ(y) - χ_z^τ(y))` and `(χ_z^τ(x) - χ_z^τ(y))` applied to `∂^αμ ψ`, the same cell estimate as
`screened_far` holds with coefficients `K^τ_{zz'}` satisfying `B:eq:screened-cell-kernel` and constant
`C(τ) = C e^{Cdτ}`.  Same hypotheses, quantifiers (the cutoff pair `χ, χ̂` is fixed first, S L10081) and
cell convention as `screened_far` (the coefficients are those of the respective kernel; the right side
uses the cells `Ψ_τ(z'+[0,1]^d)`, see `SUSPECTED ISSUE` there).  Both outputs are localised to the cell
`χ_z^τ(x)` (the sup-cell bound of S L11329, as in (i)): the global `L²(dx)` norm of the commutator
`(χ_z(x)-χ_z(y))`-operator is infinite when `2(s+1) ≤ d` (its far tail is `χ_z(y)`-weighted
`|x|^{-s-1}`), so it is not asserted.

Statement repair MH-REPAIRS-3 (docs/ISSUES.md, 2026-10-19): the two integrability conjuncts hold for almost every `x`, not for
every `x` (the kernel `|x-y|^{-s-1}` is not locally `L²`-integrable against an `L²` datum at every point). -/
theorem screened_comm_cell (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (m : ℕ)
    (Λ Cb T : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ →
      ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ∃ Kc : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z', (Kc z z' : ℝ≥0∞) ≤ ENNReal.ofReal (C * Real.exp (C * d * τ))) ∧
        (∀ z', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kc z z' : ℝ≥0∞) ≤
          ENNReal.ofReal (C * Real.exp (C * d * τ)) * ENNReal.ofReal (cellWeight d z')) ∧
        ∀ (j : ℕ), j ≤ m + 1 → ∀ (idx : Fin j → Fin d) (i : Fin d) (ψ : Euc d → ℝ), Measurable ψ →
          ∀ z : Fin d → ℤ,
            ENNReal.ofReal (C * Real.exp (C * d * τ) * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 < ⊤ →
            (∀ᵐ x ∂volume, x ∈ tsupport (advCutoff χ Ψ τ (latticePt z)) →
              Integrable (fun y => (advCutoff χh Ψ τ (latticePt z) y -
                advCutoff χ Ψ τ (latticePt z) y) * (partialDeriv idx μ y * ψ y) *
                rieszKernelGrad d s (x - y) i)) ∧
            (∀ᵐ x ∂volume, x ∈ tsupport (advCutoff χ Ψ τ (latticePt z)) →
              Integrable (fun y => (advCutoff χ Ψ τ (latticePt z) x -
                advCutoff χ Ψ τ (latticePt z) y) * (partialDeriv idx μ y * ψ y) *
                rieszKernelGrad d s (x - y) i)) ∧
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z) x *
                ∫ y, (advCutoff χh Ψ τ (latticePt z) y - advCutoff χ Ψ τ (latticePt z) y) *
                  (partialDeriv idx μ y * ψ y) * rieszKernelGrad d s (x - y) i) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Real.exp (C * d * τ) * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 ∧
            (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt z) x *
                ∫ y, (advCutoff χ Ψ τ (latticePt z) x - advCutoff χ Ψ τ (latticePt z) y) *
                  (partialDeriv idx μ y * ψ y) * rieszKernelGrad d s (x - y) i) 2 volume) ^ 2 ≤
              ENNReal.ofReal (C * Real.exp (C * d * τ) * Λ ^ 2) * ∑' z', (Kc z z' : ℝ≥0∞) *
                (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 := by
  sorry

/-! ### S.B.8: weighted same-function symmetrization -/

/-- The symmetrized pairing `⟨ς κ*(aw), w⟩ := ½ ∬ κ(x-y) w(x) w(y) [a(y) ς(x) - a(x) ς(y)] dx dy`
(the displayed identity of the proof of `B:lem:same-function`, S L11516-11520, `ς ≡ 1` in (i) and
`ς = χ²` in (ii)). -/
def symPairing (κ a w ς : Euc d → ℝ) : ℝ :=
  (1 / 2) * ∫ p : Euc d × Euc d, κ (p.1 - p.2) * w p.1 * w p.2 *
    (a p.2 * ς p.1 - a p.1 * ς p.2)

/-- The `ε`-truncation `∬_{|x-y|>ε} κ(x-y) a(y) w(y) ς(x) w(x) dy dx` of `⟨ς κ*(aw), w⟩`
(by oddness of `κ` it equals the symmetrized truncated integral). -/
def truncPairing (ε : ℝ) (κ a w ς : Euc d → ℝ) : ℝ :=
  ∫ p : Euc d × Euc d, if ε < ‖p.1 - p.2‖ then κ (p.1 - p.2) * a p.2 * w p.2 * ς p.1 * w p.1 else 0

/-- Lemma S.B.8(i) (`B:lem:same-function`, `B:item:sf-rd`, TeX S L11506-11508): `κ` an odd kernel on `ℝ^d`,
smooth away from `0`, `s > d-1` (and `s < d`), `|κ(z)| ≤ K₀ |z|^{-s-1}`, `a ∈ C^{0,1}(ℝ^d)` with
`‖⟨·⟩^{d+3} a‖_{L^∞} < ∞` (Lipschitz constant `La`, weighted bound `Λ`; `‖a‖_{C^{0,1}} + ‖⟨·⟩^{d+3}a‖_∞ ≤
La + 2Λ`, absorbed in `C`), and `w ∈ L²(ℝ^d)`: the symmetrized integral is absolutely convergent, is the
limit of the symmetric truncations (the pairing when the force is not integrable, as in the torus
`HRS.PDE.periodic_same_function`), and
`|⟨κ*(aw), w⟩| ≤ C K₀ (‖a‖_{C^{0,1}} + ‖⟨·⟩^{d+3}a‖_∞) ‖w‖²_{L²}`, `C = C(d,s)`.
Technical hypotheses: `s < d` (standing, `∫_{|z|≤1}|z|^{-s} dz < ∞` is used in the proof);
measurability of `κ` (implied by smoothness off `0`) and of `a`. -/
theorem same_function_rd (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 1 < s) (hsd : s < d) :
    ∃ C : ℝ, ∀ (κ : Euc d → ℝ) (K₀ : ℝ), (∀ z, κ (-z) = -κ z) →
      ContDiffOn ℝ ∞ κ {z | z ≠ 0} → (∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1)) →
      ∀ (La Λ : ℝ) (a w : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La a →
        (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) → MemLp w 2 volume →
      Integrable (fun p : Euc d × Euc d => κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1)) ∧
      (∀ ε : ℝ, 0 < ε → Integrable (fun p : Euc d × Euc d =>
        if ε < ‖p.1 - p.2‖ then κ (p.1 - p.2) * a p.2 * w p.2 * w p.1 else 0)) ∧
      Tendsto (fun ε => truncPairing ε κ a w (fun _ => 1)) (𝓝[>] 0)
        (𝓝 (symPairing κ a w (fun _ => 1))) ∧
      |symPairing κ a w (fun _ => 1)| ≤ C * K₀ * (La + Λ) * ∫ x, w x ^ 2 := by
  sorry

/-- Lemma S.B.8(ii) (`B:lem:same-function`, `B:item:sf-rd-weighted`, TeX S L11509-11511): uniformly local
`w`.  With `κ, a` as in (i) and the cutoff `χ = χ_z^τ` of the class `B:eq:advected-cutoffs` (an advecting
drift with bounds `(m, Cb, T)`, its flow `Ψ`, `0 ≤ τ ≤ T`, `z ∈ ℝ^d`),
`|⟨χ² κ*(aw), w⟩| ≤ C K₀ (‖a‖_{C^{0,1}} + ‖⟨·⟩^{d+3}a‖_∞) ‖χ‖²_{C^{0,1}} sup_{z'} ‖χ_{z'}^τ w‖²_{L²} C e^{Cdτ}`
(`‖χ‖_{C^{0,1}} ≤ 1 + Lχ` for a Lipschitz constant `Lχ` of `χ_z^τ`; the supremum over the lattice
`z' ∈ ℤ^d`, represented by an upper bound `S ≥ ‖1_{Q_{z'}^τ} w‖_{L²}` over the cells
`Q_{z'}^τ = Ψ_τ(z'+[0,1]^d)`; the constant `C` in `C e^{Cdτ}` is the same, as in the TeX).  The cutoff pair
`χ, χ̂` is fixed first (S L10081).
SUSPECTED ISSUE (S L11509-11511, S L11013-11020): the TeX uses `sup_{z'} ‖χ_{z'}^τ w‖` over the lattice
`z' ∈ ℤ^d`, but for `d ≥ 16` the supports `Ψ_τ(z'+B(0,2))` leave gaps (`√d/2 ≥ 2`) and `w` supported in a
gap gives a nonzero left side with a zero right side; the cell version (which is what the bounded-overlap
cover of `B:lem:uloc-bilip`(iv) gives) is stated instead.  The symmetrized integral converges absolutely and is the limit of the symmetric
truncations.  `C` depends on `d, s, m, Cb, T` (quantified first).  Technical hypotheses: `w` measurable;
`S ≥ 0` finite (a bound; if the supremum is infinite the claim is vacuous). -/
theorem same_function_rd_weighted (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 1 < s) (hsd : s < d)
    (m : ℕ) (Cb T : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : Euc d, ∀ Lχ : ℝ,
        HRS.PDE.ToolboxRd.IsLipschitz Lχ (advCutoff χ Ψ τ z) →
      ∀ (κ : Euc d → ℝ) (K₀ : ℝ), (∀ z, κ (-z) = -κ z) →
      ContDiffOn ℝ ∞ κ {z | z ≠ 0} → (∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1)) →
      ∀ (La Λ : ℝ) (a w : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La a →
        (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) → Measurable w →
      ∀ S : ℝ, 0 ≤ S → (∀ z' : Fin d → ℤ,
        eLpNorm ((flowCell Ψ τ z').indicator w) 2 volume ≤ ENNReal.ofReal S) →
      Integrable (fun p : Euc d × Euc d => κ (p.1 - p.2) * w p.1 * w p.2 *
        (a p.2 * advCutoff χ Ψ τ z p.1 ^ 2 - a p.1 * advCutoff χ Ψ τ z p.2 ^ 2)) ∧
      Tendsto (fun ε => truncPairing ε κ a w (fun x => advCutoff χ Ψ τ z x ^ 2)) (𝓝[>] 0)
        (𝓝 (symPairing κ a w (fun x => advCutoff χ Ψ τ z x ^ 2))) ∧
      |symPairing κ a w (fun x => advCutoff χ Ψ τ z x ^ 2)| ≤
        C * K₀ * (La + Λ) * (1 + Lχ) ^ 2 * S ^ 2 * (C * Real.exp (C * d * τ)) := by
  sorry

end HRS.Whole
