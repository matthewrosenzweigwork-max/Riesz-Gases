import HRS.Dynamics.Setup
import HRS.Duality.PairingExpansion
import HRS.Prob.HilbertMartingale
import HRS.PDE.Hadamard
import HRS.Uniform.Q13Aux2

/-!
# Section 3 (adjoint operator, uniform path estimates): specification statements, part I
(packet SPEC-U; all theorems here are statements with `sorry` proofs)

Rows (main manuscript `M`, source lines of `HRS_periodic_main_20261008T010000Z.tex`):

* Definition 3.2 `M:B:def:adjoint-operator` (L1587-1593) and Definition 3.5
  `M:B:def:adjoint-solution` (L1633-1635): **already represented**, by `HRS.backwardGenerator`
  (`HRS/Dynamics/Setup.lean`, with the cancellation convention `convGradConv` for both
  convolutions, as Definition 3.2 prescribes through Lemma 3.1) and by `HRS.IsClassicalAdjointSolution`
  / `HRS.propagator` respectively.  Nothing is redefined here.
* Lemma 3.3 `M:B:lem:adjoint-audit` (L1595-1600): `adjoint_audit`.
* Remark 3.4 `M:B:rem:sign-audit` (L1623-1629): `sign_audit` (the checkable content).
* Lemma 3.17 `M:U:lem:maximal` (L2026-2045): `maximal_estimate`.
* Lemma 3.18 `M:U:lem:gradient-energy` (L2070-2076): `gradient_energy`.
* Lemma 3.19 `M:U:lem:polar` (L2121-2137): `polar_coupling_cost`.
* Lemma 3.20 `M:U:lem:covmeasure` (L2183-2194): `covariance_measure`.
* Proposition 3.21 `M:U:prop:smoothpath` (L2219-2232): `smooth_path_comparison`.

## Representation decisions (the orchestrator must check these against the TeX)

* **Torus only.**  The statements of this packet are on `𝕋^d` (the paper is the periodic one);
  `𝔻 = ℝ^d` is the whole-space supplement.
* **Abstract evolutions (Lemma 3.17, 3.20, 3.21).**  The data "`H ↪ H_-`, an evolution `V(t,r)`
  bounded on both spaces, with generator `A_r : H → H_-` and `∂_r V(t,r) = -V(t,r)A_r`" is the
  record `EvolData` with the predicate `IsEvolution`; the one-level dissipative alternative of
  Lemma 3.17 (`H_- = H`) is the case in which the embedding `j` is an isometric isomorphism and
  `2⟨z, A_r z⟩ ≤ K‖z‖²` on a dense core `D`.  The two alternatives are the two disjuncts of
  `EvolData.MaxHyp`; the single number `K` bounds the operator norms (first alternative) or is the
  quasi-dissipativity constant `C` of `U:eq:quasidissipative` (second alternative).  "Constants
  `C_{T,p}`" of the TeX are quantified **before** the spaces and the evolution (`∃ C, ∀ H E S …`):
  they depend only on `(T, p, K)`, which is the uniformity in the viscosity that the title of
  Lemma 3.17 asserts.
* **Stochastic convolution `∫_a^t V(t,r) dM_r`** (not available in the library for a general Hilbert
  martingale `M` with covariance density): `IsStochConv` characterises it as the `L²(P;E)`-limit of
  the left-endpoint Riemann sums `∑ V(t,r_i) j(M_{r_{i+1}} - M_{r_i})` as the mesh tends to `0`.
  For an `L²` Hilbert martingale and a strongly continuous evolution this is the stochastic integral
  (the integrand is deterministic); in Lemma 3.17 the *existence* of the limit and of a continuous
  version is part of the conclusion (the proof says "approximation passes the identity and supplies
  continuous paths", L2041-2042).
* **Hilbert martingales** are `HRS.IsHilbertMartingaleWithCovariation` (continuous, `M_0 = 0`,
  square integrable, covariation `∫_0^· Σ_r dr` with `E ∫ ‖Σ_r‖_{𝔖₁} dr < ∞`; ISSUES §G.1).
  For `p ≥ 2` the right side of `U:eq:maximal-two` finite forces this integrability, so it is
  technical.
* **Path spaces** `𝒴 = C([0,T]; E)` are `PathSp T E` (continuous maps with the sup norm, Borel σ-algebra),
  and `d_{C_b²}` is `HRS.smoothDist 2` (SUM of the derivative sup norms, project convention
  `H:eq:metrics`).
* **Projective tensor product** `𝒴 ⊗̂_π 𝒴` of Lemma 3.20 is `ProjTensor2 𝒴`, the completion
  (`UniformSpace.Completion`) of Mathlib's `PiTensorProduct` (projective seminorm); elements are
  paired with bounded bilinear forms by `tensorPairing` (the extension of the algebraic pairing).
  "Symmetric" means invariant under exchanging the two factors, expressed by `tensorPairing Ψ = tensorPairing Ψ.flip`
  for all bounded bilinear forms `Ψ` (these separate points of `𝒴 ⊗̂_π 𝒴`, its dual being the bounded bilinear forms).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators TensorProduct

namespace HRS

namespace Uniform

variable {d : ℕ}

/-! ### Lemma 3.3 and Remark 3.4: the adjoint operator -/

/-- The pairing `⟨φ, A_ν ϱ⟩` of a test function `φ` with the linearisation
`A_ν ϱ = Div(ϱ(∇V - M∇g*ν)) - Div(ν M∇g*ϱ) + β⁻¹Δϱ` of the right-hand side of `H:eq:meanfield` at `ν`
(Lemma 3.3, L1596-1597), in the weak (distributional) sense: for a vector field `G`,
`⟨φ, Div G⟩ = -∫ ∇φ·G`, and `⟨φ, Δϱ⟩ = ∫ Δφ ϱ`.  Hence
`⟨φ, A_νϱ⟩ = -∫ ∇φ·ϱ(∇V - M∇g*ν) + ∫ ∇φ·ν M∇g*ϱ + β⁻¹ ∫ Δφ ϱ`, with `ν = ν dx`, `ϱ = ϱ dx` and both
convolutions `∇g*·` by the cancellation convention (`convGradConv`). -/
def linearizedPairing (D : DynData d) (ν ϱ φ : Torus d → ℝ) : ℝ :=
  D.invβ * (∫ x, Torus.laplacian φ x * ϱ x)
    + (∫ x, inner ℝ (Torus.grad φ x)
        (ν x • Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ϱ x)))
    - (∫ x, inner ℝ (Torus.grad φ x)
        (ϱ x • (Torus.grad D.V x
          - Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ν x))))

/-! ### Helpers for Lemma 3.3: the cancellation convolution against Hölder functions

The pairing `∫ f ⟪v, ∇g ⋆ h⟫` is computed by Fubini on the cancellation integrand
(`KernelGrad.kern`) and then antisymmetry of `∇g` gives `∫ f ⟪v, ∇g⋆h⟫ = -∫ h ⟪v, ∇g⋆f⟫`
for two Hölder functions (exponent `β > s + 1 - d`).  This is the Hölder analogue of
`HRS.PDE.MFPairing.antisym` (which needs Lipschitz functions). -/

theorem adj_inner_kern (v : Euc d) (G : Torus d → Euc d) (h : Torus d → ℝ) (x z : Torus d) :
    inner ℝ v (KernelGrad.kern G h x z) =
      (h (x - z) - (if ‖z‖ ≤ 1 / 4 then h x else 0)) * inner ℝ v (G z) := by
  unfold KernelGrad.kern
  split_ifs <;> simp [inner_smul_right]

/-- The cancellation integrand is bounded by an integrable majorant at every `z`. -/
theorem adj_kern_norm_all {s C : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    {h : Torus d → ℝ} {B Λ β : ℝ} (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hH : ∀ x z, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x z : Torus d) :
    ‖KernelGrad.kern G h x z‖ ≤
      Λ * C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β) + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
  by_cases hz : z = 0
  · subst hz
    have hC0 : 0 ≤ C := hG.hC0
    have h0 : 0 ≤ Λ * C * (‖(0 : Torus d)‖ ^ (β - s - 1) + ‖(0 : Torus d)‖ ^ β)
        + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by
      have e1 := Real.rpow_nonneg (norm_nonneg (0 : Torus d)) (β - s - 1)
      have e2 := Real.rpow_nonneg (norm_nonneg (0 : Torus d)) β
      have e3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (-s - 1)
      positivity
    have e0 : KernelGrad.kern G h x 0 = 0 := by
      unfold KernelGrad.kern; simp
    rw [e0, norm_zero]
    exact h0
  · exact Duality.kern_norm_holder hG hB hB0 hΛ hH x hz

/-- Fubini form of `∫ f ⟪v, ∇g ⋆ h⟫` for continuous `f`, `h` with a Hölder bound on `h`. -/
theorem adj_holder_pair {s C : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    (v : Euc d) {f h : Torus d → ℝ} (hf : Continuous f) (hh : Continuous h)
    {Λ β : ℝ} (hΛ : 0 ≤ Λ) (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hH : ∀ x z, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) :
    ∫ x, f x * inner ℝ v (convGradConv G h x) =
      ∫ z, inner ℝ v (G z) * ((∫ x, f x * h (x - z)) -
        (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * ∫ x, f x * h x) := by
  obtain ⟨B, hB0, hB⟩ := Duality.bounded_of_continuous hh
  obtain ⟨F, hF0, hF⟩ := Duality.bounded_of_continuous hf
  have hC0 : 0 ≤ C := hG.hC0
  have hhm : Measurable h := hh.measurable
  have step1 : ∀ x, f x * inner ℝ v (convGradConv G h x) =
      ∫ z, f x * inner ℝ v (KernelGrad.kern G h x z) := by
    intro x
    rw [KernelGrad.convGradConv_eq_integral_kern,
      ← integral_inner (Duality.integrable_kern_holder hG hhm hB hB0 hΛ hβ0 hβ hH x) v,
      integral_const_mul]
  simp_rw [step1]
  have hint : Integrable (Function.uncurry fun x z => f x * inner ℝ v (KernelGrad.kern G h x z))
      ((volume : Measure (Torus d)).prod volume) := by
    have hdom : Integrable (fun p : Torus d × Torus d => (1 : ℝ) *
        (Λ * C * (‖p.2‖ ^ (β - s - 1) + ‖p.2‖ ^ β) + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)))
        ((volume : Measure (Torus d)).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod
        (Duality.integrable_dom_holder hG (Λ := Λ) (B := B) hβ0 hβ)
    refine (hdom.const_mul (F * ‖v‖)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hf.measurable.comp measurable_fst).mul
        ((continuous_const.inner continuous_id).measurable.comp
          (Duality.measurable_kern_joint hG hhm))).aestronglyMeasurable
    · have key : ‖f p.1 * inner ℝ v (KernelGrad.kern G h p.1 p.2)‖ ≤
          F * (‖v‖ * (Λ * C * (‖p.2‖ ^ (β - s - 1) + ‖p.2‖ ^ β)
            + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1))) := by
        simp only [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (hF p.1)
          ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
            (adj_kern_norm_all hG hB hB0 hΛ hH p.1 p.2) (norm_nonneg v)))
          (abs_nonneg _) hF0
      show ‖f p.1 * inner ℝ v (KernelGrad.kern G h p.1 p.2)‖ ≤
        F * ‖v‖ * (1 * (Λ * C * (‖p.2‖ ^ (β - s - 1) + ‖p.2‖ ^ β)
            + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)))
      calc _ ≤ _ := key
        _ = _ := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  have hp : ∀ x, f x * inner ℝ v (KernelGrad.kern G h x z) =
      inner ℝ v (G z) * (f x * h (x - z)) -
        (inner ℝ v (G z) * (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0)) * (f x * h x) := by
    intro x
    rw [adj_inner_kern]
    split_ifs <;> ring
  simp_rw [hp]
  have i1 : Integrable (fun x => f x * h (x - z)) :=
    (hf.mul (hh.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun x => f x * h x) :=
    (hf.mul hh).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  ring

/-- Antisymmetry of the cancellation convolution against two Hölder functions:
`∫ f ⟪v, ∇g ⋆ h⟫ = -∫ h ⟪v, ∇g ⋆ f⟫`. -/
theorem adj_holder_antisym {s C : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    (v : Euc d) {f h : Torus d → ℝ} (hf : Continuous f) (hh : Continuous h)
    {Λf Λh β : ℝ} (hΛf : 0 ≤ Λf) (hΛh : 0 ≤ Λh) (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hHf : ∀ x z, ‖z‖ ≤ 1 / 4 → |f (x - z) - f x| ≤ Λf * ‖z‖ ^ β)
    (hHh : ∀ x z, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λh * ‖z‖ ^ β) :
    ∫ x, f x * inner ℝ v (convGradConv G h x) =
      -∫ x, h x * inner ℝ v (convGradConv G f x) := by
  rw [adj_holder_pair hG v hf hh hΛh hβ0 hβ hHh, adj_holder_pair hG v hh hf hΛf hβ0 hβ hHf]
  set R : Torus d → ℝ := fun z => inner ℝ v (G z) * ((∫ x, f x * h (x - z)) -
    (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * ∫ x, f x * h x) with hR
  rw [← integral_neg, ← integral_neg_eq_self R volume]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hR]
  have e1 : (∫ x, h x * f (x - z)) = ∫ x, f x * h (x - (-z)) := by
    rw [← integral_add_right_eq_self (fun x => h x * f (x - z)) z]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_neg_eq_add, add_sub_cancel_right]
    ring
  have e2 : (∫ x, h x * f x) = ∫ x, f x * h x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  have e3 : G (-z) = -G z := hG.odd z
  have e4 : ‖-z‖ = ‖z‖ := norm_neg z
  rw [e1, e2, e3, e4, inner_neg_right]
  ring

/-- The `j`-th coordinate of a Euclidean vector as an inner product with a unit vector. -/
theorem adj_inner_single (j : Fin d) (w : Euc d) :
    inner ℝ (EuclideanSpace.single j (1 : ℝ)) w = w j := by
  simp [EuclideanSpace.inner_single_left]

/-- The coordinates of the torus gradient are the partial derivatives (as in `MFAux.grad_apply`). -/
theorem adj_grad_apply (φ : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    Torus.grad φ x j = Torus.partialDeriv j φ x := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)
    (x := EuclideanSpace.single j (1 : ℝ)) (y := fderiv ℝ (Torus.lift φ) (Torus.rep x))
  unfold Torus.grad Torus.partialDeriv
  unfold gradient
  rw [← h]
  rw [EuclideanSpace.inner_single_right]
  simp

/-- A coordinate of a Euclidean vector is bounded by its norm. -/
theorem adj_abs_coord (v : Euc d) (a : Fin d) : |v a| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le v a

/-- `|⟪g, t • v⟫| ≤ ‖g‖ (|t| ‖v‖)`. -/
theorem adj_abs_inner_smul (g v : Euc d) (t : ℝ) :
    |inner ℝ g (t • v)| ≤ ‖g‖ * (|t| * ‖v‖) := by
  rw [inner_smul_right, abs_mul]
  calc |t| * |inner ℝ g v| ≤ |t| * (‖g‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ = ‖g‖ * (|t| * ‖v‖) := by ring


theorem adj_abs_three {X Y Z a b c : ℝ} (hX : |X| ≤ a) (hY : |Y| ≤ b) (hZ : |Z| ≤ c) :
    |X + Y - Z| ≤ a + b + c := by
  have h1 := abs_le.mp hX
  have h2 := abs_le.mp hY
  have h3 := abs_le.mp hZ
  exact abs_le.mpr ⟨by linarith [h1.1, h2.1, h3.2], by linarith [h1.2, h2.2, h3.1]⟩

/-- Lemma 3.3 (`M:B:lem:adjoint-audit`, TeX M L1595-1600), torus case: `𝓛_{β,ν}` is the adjoint of the
linearisation: `⟨φ, A_ν ρ⟩ = ⟨𝓛_{β,ν} φ, ρ⟩` for all `φ ∈ C^∞(𝕋^d)` and all finite signed measures `ρ`
with density in `C^{0,α}_b ∩ L¹`, for `ν ∈ 𝒫 ∩ C^{0,α}_b`, `α > max(0, s+1-d)`.
`𝓛_{β,ν} = backwardGenerator D ν` (Definition 3.2, represented by `HRS.backwardGenerator`), `A_ν`
is `linearizedPairing`.  The two sides are absolutely convergent integrals (asserted in the conclusion,
so that no Bochner integral is a junk `0`).

Standing assumptions: `d ≥ 1`, `0 ≤ s < d` (carried by `DynData`), `M` an arbitrary constant matrix,
`β ∈ (0,∞]` encoded by `D.invβ ∈ [0,∞)` (`1/β := 0` for `β = ∞`, L1592).

Technical hypotheses: `V ∈ C¹` (so that `∇V·∇φ` is a continuous integrand; Lemma 3.3 uses `∇V` only
through `⟨(M∇g*ν - ∇V)·∇φ, ρ⟩`). -/
theorem adjoint_audit (hd : 1 ≤ d) (D : DynData d) (hV : Torus.IsCk 1 D.V)
    (ν : Torus d → ℝ) (hν : IsProbDensity ν) (Cν α : NNReal) (hα0 : 0 < (α : ℝ))
    (hα : D.s + 1 - d < α) (hνH : HolderWith Cν α ν)
    (ϱ : Torus d → ℝ) (Cϱ : NNReal) (hϱH : HolderWith Cϱ α ϱ)
    (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    Integrable (fun x => Torus.laplacian φ x * ϱ x) ∧
    Integrable (fun x => inner ℝ (Torus.grad φ x)
        (ν x • Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ϱ x))) ∧
    Integrable (fun x => inner ℝ (Torus.grad φ x)
        (ϱ x • (Torus.grad D.V x
          - Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ν x)))) ∧
    Integrable (fun x => backwardGenerator D ν φ x * ϱ x) ∧
    linearizedPairing D ν ϱ φ = ∫ x, backwardGenerator D ν φ x * ϱ x := by
  -- the good kernel `∇g` and a name for it
  obtain ⟨CG, hG0⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le hd D.hs0 D.hsd
  obtain ⟨G, hGdef⟩ : ∃ G : Torus d → Euc d, G = periodicRieszGrad d D.s := ⟨_, rfl⟩
  rw [← hGdef] at hG0 ⊢
  have hG : KernelGrad.GoodKernel d D.s CG G := hG0
  have hC0 : (0 : ℝ) ≤ CG := hG.hC0
  -- the Hölder exponent `β = min(α, 1)`
  have hαpos : 0 < α := NNReal.coe_pos.mp hα0
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = min (α : ℝ) 1 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβdef]; exact lt_min hα0 one_pos
  have hβ1 : β ≤ 1 := by rw [hβdef]; exact min_le_right _ _
  have hβα : β ≤ (α : ℝ) := by rw [hβdef]; exact min_le_left _ _
  have hβ : D.s + 1 - d < β := by
    rw [hβdef]; exact lt_min hα (by linarith [D.hsd])
  have hνc : Continuous ν := hνH.continuous hαpos
  have hϱc : Continuous ϱ := hϱH.continuous hαpos
  have hCν0 : (0 : ℝ) ≤ Cν := NNReal.coe_nonneg Cν
  have hCϱ0 : (0 : ℝ) ≤ Cϱ := NNReal.coe_nonneg Cϱ
  have hloc : ∀ (C : NNReal) (f : Torus d → ℝ), HolderWith C α f →
      ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 → |f (x - z) - f x| ≤ (C : ℝ) * ‖z‖ ^ β := by
    intro C f hf x z hz
    have h1 := Duality.holder_abs_le hf (x - z) x
    rw [sub_sub_cancel_left, norm_neg] at h1
    have hz1 : ‖z‖ ≤ 1 := by linarith [norm_nonneg z]
    have h2 : ‖z‖ ^ (α : ℝ) ≤ ‖z‖ ^ β :=
      Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hz1 hβ0.le hβα
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg C))
  have hνL := hloc Cν ν hνH
  have hϱL := hloc Cϱ ϱ hϱH
  obtain ⟨Bν, hBν0, hBν⟩ := Duality.bounded_of_continuous hνc
  obtain ⟨Bϱ, hBϱ0, hBϱ⟩ := Duality.bounded_of_continuous hϱc
  -- the test function
  have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  have hφ2 : Torus.IsCk 2 φ := ContDiff.of_le hφ' (by norm_num)
  have hgφ : Continuous (Torus.grad φ) := Duality.grad_continuous hφ2
  have hΔ : Continuous (Torus.laplacian φ) := by
    rw [funext (PDE.laplacian_eq_sum φ hφ2)]
    exact continuous_finsetSum _ fun j _ =>
      PDE.continuous_partialDeriv j _ (PDE.isCk_one_partialDeriv j φ hφ2)
  have hgV : Continuous (Torus.grad D.V) := by
    have e : Torus.grad D.V = fun x => (WithLp.toLp 2 (fun i => Torus.partialDeriv i D.V x) : Euc d) := by
      funext x
      ext i
      simp only [adj_grad_apply, PiLp.toLp_apply]
    rw [e]
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => PDE.continuous_partialDeriv i D.V hV)
  have hmatC : ∀ M : Matrix (Fin d) (Fin d) ℝ, Continuous (fun v : Euc d => Torus.matVec M v) := by
    intro M
    have e : (fun v : Euc d => Torus.matVec M v)
        = ⇑(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) := rfl
    rw [e]
    exact ContinuousLinearMap.continuous _
  -- the components `a ↦ (Mᵀ∇φ)_a` are Lipschitz, hence continuous and bounded
  have hwL : ∀ a : Fin d, ∃ Lw : ℝ, 0 ≤ Lw ∧ ∀ x y : Torus d,
      |Torus.matVec D.M.transpose (Torus.grad φ x) a - Torus.matVec D.M.transpose (Torus.grad φ y) a|
        ≤ Lw * ‖x - y‖ := fun a => Duality.vcomp_lip D.M hφ2 a
  choose Lw hLw0 hLw using hwL
  have hwc : ∀ a : Fin d, Continuous (fun y => Torus.matVec D.M.transpose (Torus.grad φ y) a) :=
    fun a => Duality.continuous_of_lip _ (hLw0 a)
      (fun x y => by rw [Real.norm_eq_abs]; exact hLw a x y)
  have hwB : ∀ a : Fin d, ∃ Bw : ℝ, 0 ≤ Bw ∧ ∀ y : Torus d,
      |Torus.matVec D.M.transpose (Torus.grad φ y) a| ≤ Bw :=
    fun a => Duality.bounded_of_continuous (hwc a)
  choose Bw hBw0 hBw using hwB
  -- the Hölder functions `F_a = ν · (Mᵀ∇φ)_a`
  have hFc : ∀ a : Fin d, Continuous (fun y => ν y * Torus.matVec D.M.transpose (Torus.grad φ y) a) :=
    fun a => hνc.mul (hwc a)
  have hFH : ∀ a : Fin d, ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 →
      |ν (x - z) * Torus.matVec D.M.transpose (Torus.grad φ (x - z)) a
        - ν x * Torus.matVec D.M.transpose (Torus.grad φ x) a|
        ≤ ((Cν : ℝ) * Bw a + Bν * Lw a) * ‖z‖ ^ β := fun a x z hz =>
    Duality.holder_mul_kern hβ0.le hβ1 hCν0 (hLw0 a) hBν (hBw a) hνL (hLw a) x hz
  have hFB : ∀ a : Fin d, ∀ x, |ν x * Torus.matVec D.M.transpose (Torus.grad φ x) a| ≤ Bν * Bw a := by
    intro a x
    rw [abs_mul]
    exact mul_le_mul (hBν x) (hBw a x) (abs_nonneg _) hBν0
  have hFΛ : ∀ a : Fin d, 0 ≤ (Cν : ℝ) * Bw a + Bν * Lw a := fun a =>
    add_nonneg (mul_nonneg hCν0 (hBw0 a)) (mul_nonneg hBν0 (hLw0 a))
  -- uniform bounds for the convention convolutions
  have hKFa : ∀ a : Fin d, ∃ K : ℝ, ∀ x,
      ‖convGradConv G (fun y => ν y * Torus.matVec D.M.transpose (Torus.grad φ y) a) x‖ ≤ K :=
    fun a => ⟨_, fun x => Duality.conv_norm_le hG (hFB a) (mul_nonneg hBν0 (hBw0 a)) (hFΛ a)
      hβ0 hβ (hFH a) x⟩
  choose KF hKF using hKFa
  obtain ⟨Kϱ, hKϱ⟩ : ∃ K : ℝ, ∀ x, ‖convGradConv G ϱ x‖ ≤ K :=
    ⟨_, fun x => Duality.conv_norm_le hG hBϱ hBϱ0 hCϱ0 hβ0 hβ hϱL x⟩
  obtain ⟨Kν, hKν⟩ : ∃ K : ℝ, ∀ x, ‖convGradConv G ν x‖ ≤ K :=
    ⟨_, fun x => Duality.conv_norm_le hG hBν hBν0 hCν0 hβ0 hβ hνL x⟩
  have hKϱ0 : 0 ≤ Kϱ := (norm_nonneg _).trans (hKϱ 0)
  have hKν0 : 0 ≤ Kν := (norm_nonneg _).trans (hKν 0)
  have hKF0 : ∀ a, 0 ≤ KF a := fun a => (norm_nonneg _).trans (hKF a 0)
  -- measurability
  have hmν : Measurable (fun x => convGradConv G ν x) := Duality.measurable_conv hG hνc.measurable
  have hmϱ : Measurable (fun x => convGradConv G ϱ x) := Duality.measurable_conv hG hϱc.measurable
  have hmF : ∀ a : Fin d, Measurable (fun x =>
      convGradConv G (fun y => ν y * Torus.matVec D.M.transpose (Torus.grad φ y) a) x) :=
    fun a => Duality.measurable_conv hG (hFc a).measurable
  have hmcoord : ∀ a : Fin d, Measurable (fun v : Euc d => v a) := fun a =>
    (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.measurable
  have hmgφ : Measurable (Torus.grad φ) := hgφ.measurable
  have hmgV : Measurable (Torus.grad D.V) := hgV.measurable
  have hmΔ : Measurable (Torus.laplacian φ) := hΔ.measurable
  have hmMν : Measurable (fun x => Torus.matVec D.M (convGradConv G ν x)) :=
    (hmatC D.M).measurable.comp hmν
  have hmfd : Measurable (fun x => Torus.matVec D.M (convGradConv G ν x) - Torus.grad D.V x) :=
    hmMν.sub hmgV
  -- bounds on the test function and the drift
  obtain ⟨Gφ, hGφ0, hGφ⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖Torus.grad φ x‖ ≤ K := by
    obtain ⟨K, hK0, hK⟩ := Duality.bounded_of_continuous hgφ.norm
    exact ⟨K, hK0, fun x => (le_abs_self _).trans (hK x)⟩
  obtain ⟨GV, hGV0, hGV⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖Torus.grad D.V x‖ ≤ K := by
    obtain ⟨K, hK0, hK⟩ := Duality.bounded_of_continuous hgV.norm
    exact ⟨K, hK0, fun x => (le_abs_self _).trans (hK x)⟩
  obtain ⟨CM, hCM0, hCM⟩ := Duality.exists_matVec_bound D.M
  obtain ⟨Lap, hLap0, hLap⟩ := Duality.bounded_of_continuous hΔ
  -- (1) the Laplacian term
  have I1 : Integrable (fun x => Torus.laplacian φ x * ϱ x) :=
    (hΔ.mul hϱc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- (2) the interaction term
  have hbdd2 : ∀ x, |inner ℝ (Torus.grad φ x)
      (ν x • Torus.matVec D.M (convGradConv G ϱ x))| ≤ Gφ * (Bν * (CM * Kϱ)) := by
    intro x
    refine (adj_abs_inner_smul _ _ _).trans ?_
    refine mul_le_mul (hGφ x) ?_ (by positivity) hGφ0
    refine mul_le_mul (hBν x) ?_ (by positivity) hBν0
    exact (hCM _).trans (mul_le_mul_of_nonneg_left (hKϱ x) hCM0)
  have I2 : Integrable (fun x => inner ℝ (Torus.grad φ x)
      (ν x • Torus.matVec D.M (convGradConv G ϱ x))) := by
    refine Duality.integrable_of_bdd_meas ?_ hbdd2
    exact hmgφ.inner (hνc.measurable.smul ((hmatC D.M).measurable.comp hmϱ))
  -- (3) the drift term
  have hbdd3 : ∀ x, |inner ℝ (Torus.grad φ x)
      (ϱ x • (Torus.grad D.V x - Torus.matVec D.M (convGradConv G ν x)))|
        ≤ Gφ * (Bϱ * (GV + CM * Kν)) := by
    intro x
    refine (adj_abs_inner_smul _ _ _).trans ?_
    refine mul_le_mul (hGφ x) ?_ (by positivity) hGφ0
    refine mul_le_mul (hBϱ x) ?_ (by positivity) hBϱ0
    exact (norm_sub_le _ _).trans (add_le_add (hGV x)
      ((hCM _).trans (mul_le_mul_of_nonneg_left (hKν x) hCM0)))
  have I3 : Integrable (fun x => inner ℝ (Torus.grad φ x)
      (ϱ x • (Torus.grad D.V x - Torus.matVec D.M (convGradConv G ν x)))) := by
    refine Duality.integrable_of_bdd_meas ?_ hbdd3
    exact hmgφ.inner (hϱc.measurable.smul (hmgV.sub hmMν))
  -- (4) the backward generator
  have hbdD : ∀ x, |inner ℝ (Torus.matVec D.M (convGradConv G ν x) - Torus.grad D.V x) (Torus.grad φ x)|
      ≤ (CM * Kν + GV) * Gφ := by
    intro x
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul ?_ (hGφ x) (norm_nonneg _) (by positivity)
    exact (norm_sub_le _ _).trans (add_le_add ((hCM _).trans (mul_le_mul_of_nonneg_left (hKν x) hCM0))
      (hGV x))
  have hbdT : ∀ a : Fin d, ∀ x, |ϱ x * (convGradConv G (fun y => ν y * Torus.matVec D.M.transpose
      (Torus.grad φ y) a) x) a| ≤ Bϱ * KF a := by
    intro a x
    rw [abs_mul]
    exact mul_le_mul (hBϱ x) ((adj_abs_coord _ a).trans (hKF a x)) (abs_nonneg _) hBϱ0
  have hbG : ∀ x, |backwardGenerator D ν φ x| ≤
      D.invβ * Lap + (CM * Kν + GV) * Gφ + ∑ a, KF a := by
    intro x
    unfold backwardGenerator meanFieldDrift
    rw [← hGdef]
    have hA : |D.invβ * Torus.laplacian φ x| ≤ D.invβ * Lap := by
      rw [abs_mul, abs_of_nonneg D.hβ]
      exact mul_le_mul_of_nonneg_left (hLap x) D.hβ
    have hC : |∑ j : Fin d, (convGradConv G (fun y => ν y * Torus.matVec D.M.transpose
        (Torus.grad φ y) j) x) j| ≤ ∑ a, KF a :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
        (adj_abs_coord _ a).trans (hKF a x))
    exact adj_abs_three hA (hbdD x) hC
  have hBg0 : 0 ≤ D.invβ * Lap + (CM * Kν + GV) * Gφ + ∑ a, KF a :=
    (abs_nonneg _).trans (hbG 0)
  have hmbG : Measurable (fun x => backwardGenerator D ν φ x) := by
    unfold backwardGenerator meanFieldDrift
    rw [← hGdef]
    refine ((hmΔ.const_mul _).add (hmfd.inner hmgφ)).sub (Finset.measurable_sum _ fun j _ => ?_)
    exact (hmcoord j).comp (hmF j)
  have I4 : Integrable (fun x => backwardGenerator D ν φ x * ϱ x) := by
    refine Duality.integrable_of_bdd_meas (hmbG.mul hϱc.measurable)
      (K := (D.invβ * Lap + (CM * Kν + GV) * Gφ + ∑ a, KF a) * Bϱ) (fun x => ?_)
    rw [abs_mul]
    exact mul_le_mul (hbG x) (hBϱ x) (abs_nonneg _) hBg0
  -- the identity
  -- (P1) the interaction term splits along the coordinates of `Mᵀ∇φ`
  have P1 : ∀ x, inner ℝ (Torus.grad φ x) (ν x • Torus.matVec D.M (convGradConv G ϱ x))
      = ∑ a, (ν x * Torus.matVec D.M.transpose (Torus.grad φ x) a) * (convGradConv G ϱ x) a := by
    intro x
    rw [inner_smul_right, Duality.inner_matVec_transpose, Duality.inner_euc_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have IF : ∀ a : Fin d, Integrable (fun x => (ν x * Torus.matVec D.M.transpose (Torus.grad φ x) a)
      * (convGradConv G ϱ x) a) := by
    intro a
    refine Duality.integrable_of_bdd_meas ((hFc a).measurable.mul ((hmcoord a).comp hmϱ))
      (K := Bν * Bw a * Kϱ) (fun x => ?_)
    rw [abs_mul]
    exact mul_le_mul (hFB a x) ((adj_abs_coord _ a).trans (hKϱ x)) (abs_nonneg _)
      (mul_nonneg hBν0 (hBw0 a))
  -- (P3) the antisymmetry of the cancellation convolution, coordinatewise
  have P3 : ∀ a : Fin d, ∫ x, (ν x * Torus.matVec D.M.transpose (Torus.grad φ x) a)
      * (convGradConv G ϱ x) a
      = -∫ x, ϱ x * (convGradConv G (fun y => ν y * Torus.matVec D.M.transpose
          (Torus.grad φ y) a) x) a := by
    intro a
    have h := adj_holder_antisym hG (EuclideanSpace.single a 1) (hFc a) hϱc (hFΛ a) hCϱ0 hβ0 hβ
      (hFH a) hϱL
    simp only [adj_inner_single] at h
    exact h
  have hB_eq : ∫ x, inner ℝ (Torus.grad φ x) (ν x • Torus.matVec D.M (convGradConv G ϱ x))
      = -∑ a, ∫ x, ϱ x * (convGradConv G (fun y => ν y * Torus.matVec D.M.transpose
          (Torus.grad φ y) a) x) a := by
    rw [funext P1, integral_finsetSum _ (fun a _ => IF a), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => P3 a
  -- (P5) the drift term
  have P5 : ∀ x, inner ℝ (Torus.grad φ x) (ϱ x • (Torus.grad D.V x
        - Torus.matVec D.M (convGradConv G ν x)))
      = -(ϱ x * inner ℝ (Torus.matVec D.M (convGradConv G ν x) - Torus.grad D.V x) (Torus.grad φ x)) := by
    intro x
    rw [inner_smul_right, inner_sub_right, inner_sub_left,
      real_inner_comm (Torus.matVec D.M (convGradConv G ν x)) (Torus.grad φ x),
      real_inner_comm (Torus.grad D.V x) (Torus.grad φ x)]
    ring
  have hC_eq : ∫ x, inner ℝ (Torus.grad φ x)
        (ϱ x • (Torus.grad D.V x - Torus.matVec D.M (convGradConv G ν x)))
      = -∫ x, ϱ x * inner ℝ (Torus.matVec D.M (convGradConv G ν x) - Torus.grad D.V x)
          (Torus.grad φ x) := by
    simp_rw [P5, integral_neg]
  -- the backward generator, pointwise and integrated
  have hpt : ∀ x, backwardGenerator D ν φ x * ϱ x = D.invβ * (Torus.laplacian φ x * ϱ x)
      + ϱ x * inner ℝ (Torus.matVec D.M (convGradConv G ν x) - Torus.grad D.V x) (Torus.grad φ x)
      - ϱ x * ∑ a, (convGradConv G (fun y => ν y * Torus.matVec D.M.transpose
          (Torus.grad φ y) a) x) a := by
    intro x
    unfold backwardGenerator meanFieldDrift
    rw [← hGdef]
    ring
  have IS : Integrable (fun x => ϱ x * inner ℝ (Torus.matVec D.M (convGradConv G ν x)
      - Torus.grad D.V x) (Torus.grad φ x)) := by
    refine Duality.integrable_of_bdd_meas (hϱc.measurable.mul (hmfd.inner hmgφ))
      (K := Bϱ * ((CM * Kν + GV) * Gφ)) (fun x => ?_)
    rw [abs_mul]
    exact mul_le_mul (hBϱ x) (hbdD x) (abs_nonneg _) hBϱ0
  have IT : ∀ a : Fin d, Integrable (fun x => ϱ x * (convGradConv G (fun y => ν y *
      Torus.matVec D.M.transpose (Torus.grad φ y) a) x) a) := by
    intro a
    refine Duality.integrable_of_bdd_meas (hϱc.measurable.mul ((hmcoord a).comp (hmF a)))
      (K := Bϱ * KF a) (hbdT a)
  have IZ : Integrable (fun x => ϱ x * ∑ a, (convGradConv G (fun y => ν y *
      Torus.matVec D.M.transpose (Torus.grad φ y) a) x) a) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun a _ => IT a
  have hZ : ∫ x, ϱ x * ∑ a, (convGradConv G (fun y => ν y * Torus.matVec D.M.transpose
      (Torus.grad φ y) a) x) a
      = ∑ a, ∫ x, ϱ x * (convGradConv G (fun y => ν y * Torus.matVec D.M.transpose
          (Torus.grad φ y) a) x) a := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ fun a _ => IT a
  have IA : Integrable (fun x => D.invβ * (Torus.laplacian φ x * ϱ x)) := I1.const_mul _
  have hRHS : ∫ x, backwardGenerator D ν φ x * ϱ x = D.invβ * (∫ x, Torus.laplacian φ x * ϱ x)
      + (∫ x, ϱ x * inner ℝ (Torus.matVec D.M (convGradConv G ν x) - Torus.grad D.V x)
          (Torus.grad φ x))
      - ∑ a, ∫ x, ϱ x * (convGradConv G (fun y => ν y * Torus.matVec D.M.transpose
          (Torus.grad φ y) a) x) a := by
    have IAS : Integrable (fun x => D.invβ * (Torus.laplacian φ x * ϱ x)
        + ϱ x * inner ℝ (Torus.matVec D.M (convGradConv G ν x) - Torus.grad D.V x)
            (Torus.grad φ x)) := IA.add IS
    rw [funext hpt, integral_sub IAS IZ, integral_add IA IS, integral_const_mul, hZ]
  -- assemble
  refine ⟨I1, I2, I3, I4, ?_⟩
  unfold linearizedPairing
  rw [← hGdef, hRHS, hB_eq, hC_eq]
  ring

/-- Remark 3.4 (`M:B:rem:sign-audit`, TeX M L1623-1629), checkable content: the one-body drift of the
particle system is `-∇V`, so the backward operator contains exactly `-∇V·∇φ`; i.e. `𝓛` differs from
the operator with `V` replaced by `0` precisely by `-⟨∇V, ∇φ⟩` (the same sign convention as the
empirical and mean-field equations, whose linear terms then cancel exactly in Proposition 3.7, which is
`HRS.duality_identity`).  The prose claim "their linear terms cancel exactly in Proposition 3.7" is
the proved `HRS.duality_identity` and is not restated. -/
theorem sign_audit (D : DynData d) (ρ φ : Torus d → ℝ) (x : Torus d) :
    backwardGenerator D ρ φ x =
      backwardGenerator { D with V := fun _ => 0 } ρ φ x
        - inner ℝ (Torus.grad D.V x) (Torus.grad φ x) := by
  have hz : Torus.grad (fun _ : Torus d => (0 : ℝ)) x = 0 := by
    simp [Torus.grad, Torus.lift, gradient, Function.comp_def]
  unfold backwardGenerator meanFieldDrift
  simp only [hz, sub_zero]
  rw [inner_sub_left]
  ring

/-! ### Lemma 3.17: a maximal estimate uniform in the viscosity -/

section Evolution

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The data of Lemma 3.17 (L2026-2033): `H ↪ H_-` (`j`), an evolution `V(t,r)` acting on both spaces
(`VH`, `VE`, intertwined by `j`), and its generator `A_r` defined on a dense core `D ⊆ H` with values in
`H_- = E` (so `A_r : H → H_-` is bounded in the first alternative, where `D = ⊤`). -/
structure EvolData (H E : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  j : H →L[ℝ] E
  VH : ℝ → ℝ → H →L[ℝ] H
  VE : ℝ → ℝ → E →L[ℝ] E
  D : Submodule ℝ H
  A : ℝ → D →ₗ[ℝ] E

/-- `S` is a (strongly continuous) deterministic evolution on `[0,T]` on both spaces, `j` is an embedding
with dense range on the core, the two actions are intertwined by `j`, and `∂_r V(t,r) = -V(t,r) A_r`
(L2029-2030) on the core `D`, in the topology of `H_-`.

Technical (implicit in "deterministic evolution"): the cocycle property, `V(t,t) = 1`, strong continuity
of the `E`-action `VE` on the simplex `0 ≤ r ≤ t ≤ T` (`cont_E`; strong continuity of `VH` is not
assumed: in the dissipative branch it is derived, `EvolData.Dissipative.cont_VH`; repaired 2026-10-17, ISSUES GFEV-MAT). -/
structure EvolData.IsEvolution (S : EvolData H E) (T : ℝ) : Prop where
  inj : Function.Injective S.j
  dense : Dense (S.D : Set H)
  self_H : ∀ t ∈ Set.Icc 0 T, S.VH t t = 1
  self_E : ∀ t ∈ Set.Icc 0 T, S.VE t t = 1
  comp_H : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ T → (S.VH t r).comp (S.VH r s) = S.VH t s
  comp_E : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ T → (S.VE t r).comp (S.VE r s) = S.VE t s
  intertwine : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → (S.VE t r).comp S.j = S.j.comp (S.VH t r)
  cont_E : ∀ y : E, ContinuousOn (fun p : ℝ × ℝ => S.VE p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}
  deriv : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : S.D, ∀ r ∈ Set.Icc (0 : ℝ) t,
    HasDerivWithinAt (fun r' => S.VE t r' (S.j (x : H))) (-(S.VE t r (S.A r x))) (Set.Icc 0 t) r

/-- First alternative of Lemma 3.17 ("two levels"): the evolution is bounded on both spaces, uniformly
for `0 ≤ r ≤ t ≤ T`, and `A_r` maps `H` boundedly into `H_-` (`D = ⊤`); all these norms (and the norm of
the embedding) are `≤ K`. -/
def EvolData.TwoLevel (S : EvolData H E) (T K : ℝ) : Prop :=
  S.D = ⊤ ∧ ‖S.j‖ ≤ K ∧
    (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖S.VH t r‖ ≤ K ∧ ‖S.VE t r‖ ≤ K) ∧
    ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : S.D, ‖S.A r x‖ ≤ K * ‖(x : H)‖

/-- Second alternative of Lemma 3.17 ("one dissipative level", `H_- = H`, L2034-2037): `j` is an isometric
isomorphism, `2⟨z, A_r z⟩_H ≤ K‖z‖²_H` for `z` in the common dense core `D` (`U:eq:quasidissipative`; `K` is the
constant `C` there), and `A_r` *generates the evolution* on `H`: the core is invariant, `V(t,r)D ⊆ D`, and
`∂_t V(t,r)x = A_t V(t,r)x` for `x ∈ D` (forward equation, in `H_- = H`; together with the relation
`∂_r V(t,r) = -V(t,r)A_r` of `IsEvolution`), "with the corresponding Galerkin approximation" (L2042), the last conjunct:
finite-rank projections `P_n` into the core, strongly convergent to `1`, with Galerkin evolutions converging strongly to `V`. -/
def EvolData.Dissipative (S : EvolData H E) (T K : ℝ) : Prop :=
  (∀ x, ‖S.j x‖ = ‖x‖) ∧ Function.Surjective S.j ∧
    (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ z : S.D, 2 * inner ℝ (S.j (z : H)) (S.A r z) ≤ K * ‖(z : H)‖ ^ 2) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc r T, ∀ x : S.D,
      ∃ h : S.VH t r (x : H) ∈ S.D,
        HasDerivWithinAt (fun t' => S.VE t' r (S.j (x : H))) (S.A t ⟨S.VH t r (x : H), h⟩)
          (Set.Icc r T) t) ∧
    -- the corresponding Galerkin approximation (L2042): finite-rank orthogonal projections `P n` with range in the core,
    -- converging strongly to the identity, and Galerkin evolutions `Vn n t r` (the solutions in `range (P n)` of
    -- `∂_t u = P_n A_t u`, `u(r) = P_n x`, in weak form against the test vectors `y ∈ range (P n)`), which satisfy the
    -- same dissipativity bound `2⟨z, P_n A z⟩ = 2⟨z, A z⟩ ≤ K‖z‖²` (automatic on `range (P n) ⊆ D`) and converge strongly to `V`
    ∃ (P : ℕ → H →L[ℝ] H) (Vn : ℕ → ℝ → ℝ → H →L[ℝ] H),
      (∀ n, (P n).comp (P n) = P n) ∧ (∀ n x y, inner ℝ (P n x) y = inner ℝ x (P n y)) ∧
      (∀ n, FiniteDimensional ℝ (LinearMap.range (P n : H →ₗ[ℝ] H))) ∧ (∀ n x, P n x ∈ S.D) ∧
      (∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) ∧
      (∀ n r x, r ∈ Set.Icc (0 : ℝ) T → Vn n r r x = P n x) ∧
      (∀ n t r x, ∃ y, P n y = Vn n t r x) ∧
      (∀ n r t x y (h : Vn n t r x ∈ S.D), r ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc r T →
        (∃ z, P n z = y) →
        HasDerivWithinAt (fun t' => inner ℝ y (Vn n t' r x))
          (inner ℝ (S.j y) (S.A t ⟨Vn n t r x, h⟩)) (Set.Icc r T) t) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc r T, ∀ x, Tendsto (fun n => Vn n t r x) atTop (𝓝 (S.VH t r x))

/-- In the dissipative branch `j` is an isometry, so strong continuity of `VH` follows from that of `VE`. -/
theorem EvolData.Dissipative.cont_VH {T K : ℝ} {S : EvolData H E} (hev : S.IsEvolution T)
    (h : S.Dissipative T K) (x : H) :
    ContinuousOn (fun p : ℝ × ℝ => S.VH p.1 p.2 x) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := by
  have hiso : ∀ y, ‖S.j y‖ = ‖y‖ := h.1
  have hc := hev.cont_E (S.j x)
  rw [Metric.continuousOn_iff] at hc ⊢
  intro p hp ε hε
  obtain ⟨δ, hδ, hδ'⟩ := hc p hp ε hε
  refine ⟨δ, hδ, fun q hq hqp => ?_⟩
  have h1 := hδ' q hq hqp
  have hint : ∀ (t r : ℝ), 0 ≤ r → r ≤ t → t ≤ T → S.j (S.VH t r x) = S.VE t r (S.j x) := by
    intro t r hr hrt htT
    have := congrArg (fun f => f x) (hev.intertwine r t hr hrt htT)
    simpa using this.symm
  obtain ⟨hq1, hq2, hq3⟩ := hq
  obtain ⟨hp1, hp2, hp3⟩ := hp
  rw [dist_eq_norm] at h1 ⊢
  rw [← hiso, map_sub, hint _ _ hq1 hq2 hq3, hint _ _ hp1 hp2 hp3]
  exact h1

/-- The hypotheses of Lemma 3.17: an evolution on `[0,T]` satisfying either alternative (with constant `K`). -/
def EvolData.MaxHyp (S : EvolData H E) (T K : ℝ) : Prop :=
  S.IsEvolution T ∧ (S.TwoLevel T K ∨ S.Dissipative T K)

section Convolution

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The left-endpoint Riemann sum `∑_i V(t, r_i) j(M_{r_{i+1}} - M_{r_i})` along the partition
`r_0 ≤ … ≤ r_n` approximating `∫ V(t,r) dM_r`. -/
def riemannSum (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E) (M : ℝ → Ω → H) (t : ℝ) {n : ℕ}
    (r : Fin (n + 1) → ℝ) (ω : Ω) : E :=
  ∑ i : Fin n, VE t (r i.castSucc) (j (M (r i.succ) ω - M (r i.castSucc) ω))

/-- `Z` is the stochastic convolution `∫_a^t V(t,r) dM_r` of the `H`-valued martingale `M` against the
deterministic evolution `V`, viewed in `E` through `j`: the `L²(P;E)`-limit of the Riemann sums over
partitions `a = r_0 ≤ … ≤ r_n = t` as the mesh tends to `0` (for `t < a` there is no partition and the
predicate is vacuous; it is only used for `t ≥ a`). -/
def IsStochConv (P : Measure Ω) (VE : ℝ → ℝ → E →L[ℝ] E) (j : H →L[ℝ] E) (M : ℝ → Ω → H)
    (a t : ℝ) (Z : Ω → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (r : Fin (n + 1) → ℝ), r 0 = a →
    r (Fin.last n) = t → Monotone r → (∀ i : Fin n, r i.succ - r i.castSucc < δ) →
      ∫⁻ ω, ‖Z ω - riemannSum VE j M t r ω‖ₑ ^ 2 ∂P < ENNReal.ofReal ε

end Convolution

end Evolution

/-- Lemma 3.17 (`M:U:lem:maximal`, "Two levels, or one dissipative level", TeX M L2026-2045).

(1) For `p ≥ 2`, every continuous `H`-valued martingale `M` with `M_0 = 0` and covariance density `C_r`
(`Sg`), has a stochastic convolution `Z_t = ∫_0^t V(t,r) dM_r` in `E = H_-` with continuous paths on `[0,T]`
and `‖Z‖_{L^p(C_T H_-)} ≤ C_{T,p} ‖(∫_0^T Tr C_r dr)^{1/2}‖_{L^p}` (`U:eq:maximal-two`), the same conclusion
with `H_- = H` in the dissipative alternative (`U:eq:quasidissipative`).  Both sides are `lintegral`s in `ℝ≥0∞`
(so finiteness of the right side is not assumed and no integral is a junk value); `Tr C_r = traceNormForm (Sg r ω)`
for the nonnegative trace-class form `C_r`.
(2) The deterministic convolution `∫_0^t V(t,r) b(r) dr` obeys `sup_t ‖·‖_{H_-} ≤ C_T ∫_0^T ‖b(r)‖_H dr`.

The constant `C` is chosen after `(T, p, K)` and before the spaces, the evolution, the probability space
and the martingale: it depends only on `(T, p, K)`.

Technical hypotheses: `H`, `E` separable (second countable) Hilbert spaces with Borel σ-algebras; `M` is a
square-integrable martingale with `E∫‖C_r‖₁ dr < ∞` (inside `IsHilbertMartingaleWithCovariation`; for `p ≥ 2`
the finiteness of the right side of the estimate forces it); strong continuity and the cocycle property of the
evolution (inside `IsEvolution`); `0 ≤ T`. -/
theorem maximal_estimate (T p K : ℝ) (hT : 0 ≤ T) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (hS : S.MaxHyp T K)
        (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
        (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg),
        ∃ Z : ℝ → Ω → E,
          (∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t)) ∧
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) ∧
          (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) ^ p ∂P) ^ (1 / p) ≤
            ENNReal.ofReal C *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P) ^ (1 / p)) ∧
      (∀ (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        (S : EvolData H E) (hS : S.MaxHyp T K) (b : ℝ → H),
        ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖∫ r in Set.Icc (0 : ℝ) t, S.VE t r (S.j (b r))‖ₑ ≤
          ENNReal.ofReal C * ∫⁻ r in Set.Icc (0 : ℝ) T, ‖b r‖ₑ) := by
  sorry

/-! ### Lemma 3.18: no path loss in the gradient regimes -/

/-- The forward linearisation `A_ν` of `H:eq:meanfield` at a frozen density `μ`
(`B:eq:forward-linearized-comparison`, L1998-2002),
`A ϱ = Div(ϱ(∇V - M∇g*μ)) - Div(μ M∇g*ϱ) + β⁻¹Δϱ`, in Fourier coefficients (Lemma 3.3 shows it is the
`L²`-adjoint of `backwardGenerator`).  The three terms are `β⁻¹ Δ`, `-Div(b ϱ)` with `b = M∇g*μ - ∇V`
(`HRS.PDE.driftCoeff`) and the nonlocal term `-Div(μ M∇g*ϱ)` (`HRS.PDE.forwardNonlocalCoeff`). -/
def forwardLinCoeff (D : DynData d) (μ : Torus d → ℝ) (F : PDE.Coeff d) : PDE.Coeff d :=
  fun k => ((D.invβ : ℝ) : ℂ) * PDE.laplaceCoeff F k
    - ∑ j : Fin d, PDE.derivCoeff j (PDE.mulCoeff (PDE.driftCoeff D μ j) F) k
    + PDE.forwardNonlocalCoeff D μ F k

/-- Lemma 3.18 (`M:U:lem:gradient-energy`, TeX M L2070-2076): for periodic gradient dynamics (`M = -I`),
uniform smooth coefficient bounds imply the quasi-dissipativity `2⟨z, A_r z⟩_{H^{-γ}} ≤ C‖z‖²_{H^{-γ}}`
(`U:eq:quasidissipative`) on `H^{-γ}_0`, on the common dense core of real trigonometric polynomials with zero
mean, uniformly for `0 ≤ ν_N ≤ ν_max`, provided either `θ = s+2-d ≤ 1`, or `ρ^t ≥ m₀` for a common `m₀ > 0`.

`H^{-γ}_0` is the zero-mean subspace of `HRS.PDE.Coeff`-sequences with `hsInner (-γ)`; `A_r =
forwardLinCoeff D (ρ r)`.  The constant `C` is chosen after `(d, s, γ, T, Λ, ν_max, m₀)` and before `D`, `V`,
`ρ`, `r`, hence is uniform in the viscosity.

AMBIGUITY (L2070-2071): "uniform smooth coefficient bounds" does not say how many derivatives; the reading used
is the one of Theorem 2.1 (L538-546): `‖ρ^t‖_{C^{K}}, ‖V‖_{C^K} ≤ Λ` with `K = γ + 2d + 12`.
AMBIGUITY: the constant may depend on `m₀` also in the case `θ ≤ 1` (where the TeX does not use `m₀`).
Technical hypotheses: `d ≥ 1`; `ρ^t` probability densities (the mean-field densities). -/
theorem gradient_energy (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (γ : ℕ)
    (T Λ νmax m₀ : ℝ) (hm₀ : 0 < m₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : DynData d, D.M = -1 → D.s = s → D.invβ ≤ νmax →
      Torus.IsCk (γ + 2 * d + 12 : ℕ) D.V → Torus.cbNorm (γ + 2 * d + 12) D.V ≤ Λ →
      ∀ ρ : ℝ → Torus d → ℝ, (∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r)) →
        IsRegularMF (γ + 2 * d + 12) Λ T ρ →
        (PDE.thetaOrder d s ≤ 1 ∨ ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, m₀ ≤ ρ r x) →
        ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ (n : ℕ) (c : PDE.Coeff d),
          PDE.IsTrigPoly n c → PDE.IsRealCoeff c → c 0 = 0 →
          2 * (PDE.hsInner (-(γ : ℝ)) c (forwardLinCoeff D (ρ r) c)).re ≤
            C * PDE.hsNormSq (-(γ : ℝ)) c := by
  obtain ⟨C₀, hC₀, h⟩ := Q13.q13_energy_const hd s hs0 hsd γ Λ m₀ hm₀
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro D hM hs hβ hV hVb ρ hρ hreg hcase r hr n c hc hcr hc0
  have hle : γ + 3 ≤ γ + 2 * d + 12 := by omega
  obtain ⟨hk, hb⟩ := hreg r hr
  have hk' : Torus.IsCk ((γ + 3 : ℕ)) (ρ r) := PDE.ET.isCk_mono' hle hk
  have hb' : Torus.cbNorm (γ + 3) (ρ r) ≤ Λ := (PDE.ET.cbNorm_mono' hle _).trans hb
  have hV' : Torus.IsCk ((γ + 3 : ℕ)) D.V := PDE.ET.isCk_mono' hle hV
  have hVb' : Torus.cbNorm (γ + 3) D.V ≤ Λ := (PDE.ET.cbNorm_mono' hle _).trans hVb
  have hcase' : PDE.thetaOrder d s ≤ 1 ∨ ∀ x, m₀ ≤ ρ r x :=
    hcase.imp_right fun h => h r hr
  have hE := h D hM hs hV' hVb' (ρ r) (hρ r hr) hk' hb' hcase' n
  have := Q13.q13_form (n := n) γ D (Q13.q13_real_of_isCk hk) (Q13.q13_real_of_isCk hV) hc hcr C₀
    (fun F hFr hFt => hE F hFr hFt)
  have h2 := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
  calc 2 * (PDE.hsInner (-(γ : ℝ)) c (forwardLinCoeff D (ρ r) c)).re
      ≤ 2 * (C₀ * PDE.hsNormSq (-(γ : ℝ)) c) := h2
    _ = _ := by ring

/-! ### Lemma 3.19: the polar martingale coupling with its square-root cost -/

universe u

/-- Lemma 3.19 (`M:U:lem:polar`, "Polar martingale coupling", TeX M L2121-2137).  Let `B_r` (here the
progressive Hilbert-Schmidt family `Φ`) drive `M = ∫Φ dW`, with covariance density `C_r = Σ_r = Φ_rΦ_r^*`, and let
`C̄_r` (`sb`) be a deterministic nonnegative trace-class density with integrable traces.  On an extension
of the space there is an `H`-cylindrical Brownian motion `𝒲` (`B`), independent of the initial σ-field `𝒢`, with
`dM = C^{1/2} d𝒲` and `dM̄ = C̄^{1/2} d𝒲` (`U:eq:polar-coupling`; `M̄ = G`), and
`E ∫_0^T ‖C_r^{1/2} - C̄_r^{1/2}‖²_{𝔖₂} dr ≤ E ∫_0^T ‖C_r - C̄_r‖_{𝔖₁} dr` (`U:eq:coupling-cost`, the last conjunct,
stated for the square roots `S_r`, `S̄_r` produced by the coupling; Hilbert-Schmidt norm `‖A‖²_{𝔖₂} = ∑_i ‖A e_i‖²`
along the Hilbert basis `e` of `H`).  "The same construction works when the initial σ-field contains a prescribed
coupling of two initial states" is the generality `𝒢 ⊆ ℱ_0` arbitrary.

All conjuncts but the last are those of `HRS.hilbert_polar_coupling` (Corollary A.23, same statement of the
coupling; its own last conjunct is the consequence `E‖M_T - G_T‖² ≤ …`, retained); the conclusion adds the
integrated Powers-Størmer cost.  The conventions (progressive for predictable; `hΦ`: `L²` on every finite horizon)
are those of `HRS.hilbert_polar_coupling`, see its docstring.  Both sides of the cost inequality are in `ℝ≥0∞`
(so finiteness of the right side is not assumed). -/
theorem polar_coupling_cost {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t) (𝒢 : InitialSigma ℱ)
    {κ : Type*} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (hW : IsCylindricalBrownian P ℱ W)
    (Φ : ℝ → Ω → κ → H) (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ)
    (M : ℝ → Ω → H) (hM : IsHilbertItoIntegral P ℱ W Φ M)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (ι : Type u) (_ : Countable ι) (e : HilbertBasis ι ℝ H) (B : ℝ≥0 → Ω' → ι → ℝ)
      (S : ℝ → Ω → (H →L[ℝ] H)) (Sb : ℝ → (H →L[ℝ] H)) (G : ℝ → Ω' → H),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsCylindricalBrownian P' ℱ' B ∧
      Indep (𝒢.1.comap π) (cylindricalPathSigma B) P' ∧
      (∀ r ω, IsSqrtOfForm (S r ω) (hsCovForm (Φ r ω))) ∧
      IsHilbertItoIntegral P' ℱ' B (fun r ω' j => if r ≤ t then S r (π ω') (e j) else 0)
        (fun τ ω' => M (min τ t) (π ω')) ∧
      (∀ r ∈ Set.Icc 0 t, IsSqrtOfForm (Sb r) (sb r)) ∧
      IsHilbertItoIntegral P' ℱ' B (fun r _ j => if r ≤ t then Sb r (e j) else 0) G ∧
      AEMeasurable (G t) P' ∧
      Indep (𝒢.1.comap π) (MeasurableSpace.comap (G t) inferInstance) P' ∧
      IsCenteredGaussian (law P' (G t)) ∧
      (∀ x y, covarianceBilin (law P' (G t)) x y = ∫ σ in Set.Icc 0 t, sb σ x y) ∧
      ∫⁻ ω', ‖M t (π ω') - G t ω'‖ₑ ^ 2 ∂P' ≤
        ENNReal.ofReal (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb) ∧
      ∫⁻ ω', (∫⁻ r in Set.Icc 0 t, ∑' i, ‖((S r (π ω')) - Sb r) (e i)‖ₑ ^ 2) ∂P' ≤
        ENNReal.ofReal (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb) := by
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', ι, hι, e, B, S, Sb, G, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, hbound⟩ := hilbert_polar_coupling P ℱ t ht 𝒢 W hW Φ hΦ M hM sb hsb
  refine ⟨Ω', mΩ', P', hP', π, hπ, ℱ', ι, hι, e, B, S, Sb, G, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, hbound, ?_⟩
  -- pointwise Powers–Størmer bound on the Hilbert basis `e` of the coupling
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ ω : Ω,
      ∑' i, ‖(S r ω - Sb r) (e i)‖ₑ ^ 2 ≤
        ENNReal.ofReal (traceNormForm (hsCovForm (Φ r ω) - sb r)) := by
    intro r hr ω
    have hC := isTraceClassCov_hsCovForm ((hΦ 0).summable r ω)
    have hC' := hsb.traceClass r hr
    obtain ⟨T1, hT1, -⟩ := hC.hasSum_basis e
    obtain ⟨T2, hT2, -⟩ := hC'.hasSum_basis e
    obtain ⟨hsum, hle⟩ :=
      powers_stormer e (h4 r ω) (h6 r hr) hC hC' hT1.summable hT2.summable
    calc ∑' i, ‖(S r ω - Sb r) (e i)‖ₑ ^ 2
        = ∑' i, ENNReal.ofReal (‖(S r ω - Sb r) (e i)‖ ^ 2) :=
          tsum_congr fun i => by
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ = ENNReal.ofReal (∑' i, ‖(S r ω - Sb r) (e i)‖ ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum).symm
      _ ≤ ENNReal.ofReal (traceNormForm (hsCovForm (Φ r ω) - sb r)) :=
          ENNReal.ofReal_le_ofReal hle
  -- integrate over `Ω'` and transport to `Ω` by measure preservation
  have hcost : ∫⁻ ω', (∫⁻ r in Set.Icc 0 t, ∑' i, ‖(S r (π ω') - Sb r) (e i)‖ₑ ^ 2) ∂P' ≤
      ∫⁻ ω', (∫⁻ r in Set.Icc 0 t,
        ENNReal.ofReal (traceNormForm (hsCovForm (Φ r (π ω')) - sb r))) ∂P' :=
    lintegral_mono fun ω' => setLIntegral_mono' measurableSet_Icc fun r hr => hpt r hr (π ω')
  have hcomp := hπ.lintegral_comp (pc_meas_Lr hΦ t sb hsb)
  exact hcost.trans (le_of_eq (hcomp.trans (pc_lintegral_covDisc hΦ ht sb hsb)))

/-! ### Lemma 3.20: trace densities and path covariance measures -/

section PathCov

/-- The projective tensor square `𝒴 ⊗̂_π 𝒴` of a normed space: the completion of Mathlib's
`PiTensorProduct` (projective seminorm) on two factors. -/
abbrev ProjTensor2 (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] : Type _ :=
  UniformSpace.Completion (⨂[ℝ] _ : Fin 2, Y)

/-- The bilinear form `Ψ` as a multilinear map on two arguments. -/
def bilinMultilinear {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) : MultilinearMap ℝ (fun _ : Fin 2 => Y) ℝ where
  toFun v := Ψ (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update]
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [Function.update]

/-- The pairing of an element of `𝒴 ⊗̂_π 𝒴` with a bounded bilinear form `Ψ`: the (unique continuous)
extension of `y ⊗ y' ↦ Ψ(y, y')`.  (`Completion.extension` of a linear map bounded by the projective norm; the
junk branch of `extension` is never used since the map is uniformly continuous.) -/
def tensorPairing {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) : ProjTensor2 Y → ℝ :=
  UniformSpace.Completion.extension (PiTensorProduct.lift (bilinMultilinear Ψ))

/-- `𝒴 = C([0,T]; E)` with the sup norm and the Borel σ-algebra (cf. `HRS.PathSpace`, which is the case
`E = E_m`). -/
def PathSp (T : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Type _ :=
  C(Set.Icc (0 : ℝ) T, E)

namespace PathSp

variable {T : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : NormedAddCommGroup (PathSp T E) :=
  inferInstanceAs (NormedAddCommGroup C(Set.Icc (0 : ℝ) T, E))

instance : NormedSpace ℝ (PathSp T E) :=
  inferInstanceAs (NormedSpace ℝ C(Set.Icc (0 : ℝ) T, E))

instance : MeasurableSpace (PathSp T E) := borel _

instance : BorelSpace (PathSp T E) := ⟨rfl⟩

/-- Evaluation `w ↦ w(t)` of a path at a time `t ∈ [0,T]`, a bounded linear map. -/
def eval (t : Set.Icc (0 : ℝ) T) : PathSp T E →L[ℝ] E :=
  ContinuousMap.evalCLM ℝ t

end PathSp

open Classical in
/-- The window `t ↦ X(a+t)`, `t ∈ [0,T]`, of a process `X : [0,∞) → E` as an element of `C([0,T];E)`
(`0` if the path is not continuous, a null event in all uses). -/
def windowPath {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a T : ℝ)
    (X : ℝ → Ω → E) (ω : Ω) : PathSp T E :=
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => X (a + t) ω then
    (⟨fun t => X (a + t) ω, h⟩ : C(Set.Icc (0 : ℝ) T, E))
  else 0

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bounded bilinear form `(y, y') ↦ ℓ₁(y(t₁)) ℓ₂(y'(t₂))` on `𝒴 = C([0,T];E)`: two terminal observations
(`ℓ_i ∈ E^*`, `t_i ∈ [0,T]`). -/
def obsForm {T : ℝ} (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ) :
    PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ :=
  (ℓ₁.comp (PathSp.eval t₁)).smulRight (ℓ₂.comp (PathSp.eval t₂))

/-- The vector `V(t,r)^*ℓ ∈ H` representing the functional `x ↦ ℓ(V(t,r) j x)` on `H` (Riesz). -/
def pullbackVec (S : EvolData H E) (t r : ℝ) (ℓ : E →L[ℝ] ℝ) : H :=
  (InnerProductSpace.toDual ℝ H).symm (ℓ.comp ((S.VE t r).comp S.j))

/-- `D ∈ L¹([0,T]; 𝔖₁(H))`, self-adjoint: pointwise symmetric forms of finite trace norm (the variational
sums are bounded), entrywise measurable, with `∫_0^T ‖D_r‖_{𝔖₁} dr < ∞`. -/
def IsTraceDensityL1 (T : ℝ) (D : ℝ → H →L[ℝ] H →L[ℝ] ℝ) : Prop :=
  (∀ r x y, D r x y = D r y x) ∧
  (∀ r ∈ Set.Icc (0 : ℝ) T, BddAbove (Set.range fun p : OrthonormalPairs H =>
    ∑ i, |D r (p.1.2.1 i) (p.1.2.2 i)|)) ∧
  (∀ x y, Measurable fun r => D r x y) ∧
  IntegrableOn (fun r => traceNormForm (D r)) (Set.Icc 0 T)

/-- Lemma 3.20 (`M:U:lem:covmeasure`, "Trace densities and path covariance measures", TeX M L2183-2194).
For `𝒴 = C([0,T];H_-)` (in the setting of Lemma 3.17: either alternative; the one-level variant is `E ≅ H`):
for every self-adjoint `D ∈ L¹([0,T];𝔖₁(H))` there is an additive (here: countably additive) symmetric
`𝒴 ⊗̂_π 𝒴`-valued measure `𝒥_D` with total variation
`‖𝒥_D‖_{var} ≤ C_T ∫_0^T ‖D_r‖_{𝔖₁} dr` (`U:eq:abstract-Jbound`; the variation measure of
`MeasureTheory.VectorMeasure.variation` evaluated at `[0,T]`), supported on `[0,T]`, equal on two terminal
observations `(t₁,ℓ₁)`, `(t₂,ℓ₂)` to the integral of the propagated bilinear form
`∫_{I ∩ [0, t₁∧t₂]} D_r(V(t₁,r)^*ℓ₁, V(t₂,r)^*ℓ₂) dr`, linear in `D` (`D ↦ 𝒥_D` bounded and linear, the bound
being the variation bound), with continuous cumulative measure `t ↦ 𝒥_D([0,t])`.
`C` depends only on `(T,K)` (chosen before the evolution), as in Lemma 3.17.
The measure `𝒥_D` is not claimed unique here (the TeX construction fixes it; it is determined by the
two-observation formula since observations separate points of `𝒴 ⊗̂_π 𝒴`). -/
theorem covariance_measure (T K : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        (S : EvolData H E) (_ : S.MaxHyp T K),
      ∃ J : (ℝ → H →L[ℝ] H →L[ℝ] ℝ) → VectorMeasure ℝ (ProjTensor2 (PathSp T E)),
        (∀ D, IsTraceDensityL1 T D →
          (∀ I, MeasurableSet I → J D I = J D (I ∩ Set.Icc 0 T)) ∧
          (∀ I, MeasurableSet I → ∀ Ψ : PathSp T E →L[ℝ] PathSp T E →L[ℝ] ℝ,
            tensorPairing Ψ (J D I) = tensorPairing Ψ.flip (J D I)) ∧
          (J D).variation (Set.Icc 0 T) ≤
            ENNReal.ofReal C * ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (D r)) ∧
          (∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ) (I : Set ℝ), MeasurableSet I →
            tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) (J D I) =
              ∫ r in I ∩ Set.Icc 0 (min (t₁ : ℝ) t₂),
                D r (pullbackVec S t₁ r ℓ₁) (pullbackVec S t₂ r ℓ₂)) ∧
          ContinuousOn (fun t => J D (Set.Icc 0 t)) (Set.Icc 0 T)) ∧
        (∀ D D', IsTraceDensityL1 T D → IsTraceDensityL1 T D' → ∀ a b : ℝ, ∀ I, MeasurableSet I →
          J (fun r => a • D r + b • D' r) I = a • J D I + b • J D' I) := by
  sorry

end PathCov

/-! ### Proposition 3.21: smooth comparison on continuous paths -/

/-- Proposition 3.21 (`M:U:prop:smoothpath`, "Smooth comparison on continuous paths", TeX M L2219-2232), in the
setting of Lemma 3.17 (`S.MaxHyp T K`), path space `𝒴 = C([0,T];H_-)`.

A process `X(t) = V(t,0)X₀ + Z(t) + R(t)` is the sum of its transported initial state, the martingale convolution
`Z = ∫V dM` (`M` a continuous Hilbert martingale of covariance density `C_r = Sg`, `IsStochConv`) and a remainder
`R` with continuous paths (the "drift convolution"; only its path norm enters, as in the proof L2243-2244, so
`R` is not required to be a convolution).  The surrogate `X̄(t) = V(t,0)X̄₀ + Z̄(t)` has initial state `X̄₀` coupled
with `X₀` in the initial σ-field `ℱ_0` (so that `M` remains a martingale given the coupling), and Gaussian driving
noise `Z̄ = ∫V dG` where `G` is a continuous Hilbert martingale with *deterministic* covariance density `C̄_r`
(`Cb`): such a martingale is Gaussian with independent increments, hence independent of `ℱ_0` (Lévy).
Then
`d_{C_b²(𝒴)}(X, X̄) ≤ C_T E‖X₀ - X̄₀‖_H + E‖R‖_𝒴 + C_T E ∫_0^T ‖C_r - C̄_r‖_{𝔖₁} dr`  (`U:eq:abstract-smooth`).
No Gaussian assumption on the initial state is made.  The inequality is in `ℝ≥0∞` (all expectations are
`lintegral`s), so no integrability is assumed and no integral is a junk value; `smoothDist 2` is the project's
`d_{C_b²}`, applied to the laws of the path-valued random variables (`windowPath 0 T`).

`C` depends only on `(T, K)` (chosen before the evolution and the probability space).

Technical hypotheses: separable Hilbert spaces; measurability of `Z t`, `Z̄ t`, `R t` (so that the path laws are
the honest push-forwards, not the junk measure `0`); `ℱ_0`-measurability of the initial states. -/
theorem smooth_path_comparison (T K : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (_ : S.MaxHyp T K)
        (X₀ X₀' : Ω → H) (_ : Measurable[ℱ 0] X₀) (_ : Measurable[ℱ 0] X₀')
        (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
        (_ : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
        (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (_ : IsDetCovDensity T Cb)
        (_ : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r))
        (Z Zb R : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t))
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Zb t))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T))
        (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
        (X Xb : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, X t ω = S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Xb t ω = S.VE t 0 (S.j (X₀' ω)) + Zb t ω),
        ENNReal.ofReal (smoothDist 2 (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb))) ≤
          ENNReal.ofReal C * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P +
            ENNReal.ofReal C *
              ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P := by
  sorry

end Uniform

end HRS

