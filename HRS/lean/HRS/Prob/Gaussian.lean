import HRS.Prob.Metrics

/-!
# Gaussian measures on Hilbert/Banach spaces: Edgeworth expansion, Stein equation, chaos

Sources (HRS periodic main paper):
* Lemma 7.1 `M:O:lem:iid-edge` (source lines 7729-7736): stated in `HRS.Prob.Edgeworth`, which
  imports this file so that its proof can use the Stein lemmas below.
* Lemma 7.2 `M:F:lem:Stein` (7774-7789): Stein equation without a dimension factor.
* Lemma 7.3 `M:F:lem:contractions` (7805-7819): Banach-valued Gaussian contractions.
* Proposition 7.18 `M:E:prop:chaos` (9782-9820), first display `E:eq:chaos-isometry`:
  Gaussian quadratic chaos of a Hilbert–Schmidt operator.
* Proposition 2.4 `M:H:prop:field-singularity` (701-710): mutual singularity of a
  Gaussian field law and empirical-measure laws.

## Representation
* A centered Gaussian random variable `G : Ω → H` is one whose law satisfies
  `IsCenteredGaussian` (Mathlib `IsGaussian`, all one-dimensional projections centered).
* Covariance of an `H`-valued random variable: Mathlib's `covarianceBilin (law P X)`.
* The pairing `⟨D³F(G), M₃⟩` with the third-moment tensor `M₃ = E[X^{⊗3}]` in the projective
  tensor product is represented by its evaluation `E'[D³F(G)[X', X', X']]` with `X'` an
  independent copy of `X` (see `docs/ISSUES.md` §G1: for `X` with finite third moment this
  evaluation equals the pairing with the Bochner integral `E[X^{⊗3}]` in `H^{⊗̂π 3}`, so no
  content is lost; the projective-tensor formulation is deferred to EDGE-02).
* Completed projective tensor powers `B^{⊗̂π k}` (Lemma 7.3, `F:eq:firstcontract`): `projTensor B k`,
  the closed span of the elementary tensors in the dual `TensorDual B k = (B [×k]→L[ℝ] ℝ) →L[ℝ] ℝ`
  of the bounded `k`-linear forms (see the comment before `TensorDual`).
* Gaussian chaos (Prop. 7.18): `G : ℕ → Ω → ℝ` i.i.d. standard Gaussians and a symmetric
  Hilbert–Schmidt matrix `A : ℕ → ℕ → ℝ`; `Q(A)` is the `L²` limit of the finite sections
  `½ ∑_{i,j<n} A_ij (G_i G_j - δ_ij)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- `G` is a centered Gaussian random variable in `H` with covariance bilinear form `C`. -/
def IsCenteredGaussianRV (G : Ω → H) (C : H → H → ℝ) : Prop :=
  AEMeasurable G P ∧ IsCenteredGaussian (law P G) ∧
    ∀ x y, ProbabilityTheory.covarianceBilin (law P G) x y = C x y

/-- Independent copies: `X i` are i.i.d. with the law of `X 0`. -/
def IsIIDCopies {ι : Type*} (X : ι → Ω → H) : Prop :=
  ProbabilityTheory.iIndepFun X P ∧ ∀ i j, law P (X i) = law P (X j)

/-- Finite `p`-th moment. -/
def HasMoment (p : ℝ) (X : Ω → H) : Prop := Integrable (fun ω => ‖X ω‖ ^ p) P

/-- The trilinear-form pairing `⟨D³F(G), E[X^{⊗3}]⟩` represented by evaluation on an
independent copy `X'` of `X` (living on a product space). -/
def thirdMomentPairing (F : H → ℝ) (G : Ω → H) (X : Ω → H) : ℝ :=
  ∫ p : Ω × Ω, iteratedFDeriv ℝ 3 F (G p.1) ![X p.2, X p.2, X p.2] ∂(P.prod P)


end Hilbert

section Stein

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The Stein solution `f(x) = -∫_0^∞ (E[Φ(e^{-u}x + √(1-e^{-2u}) G)] - E[Φ(G)]) du`
(`F:eq:stein-solution`, lines 7777-7780). -/
def steinSolution (G : Ω → B) (Φ : B → ℝ) (x : B) : ℝ :=
  -∫ u in Set.Ioi (0 : ℝ),
    (∫ ω, Φ (Real.exp (-u) • x + Real.sqrt (1 - Real.exp (-2 * u)) • G ω) ∂P - ∫ ω, Φ (G ω) ∂P)

/-- The contraction `⟨D²f(x), C_G⟩ = E[D²f(x)[G, G]]` of a second derivative with the Gaussian
covariance (representation by expectation over `G`). -/
def covarianceContraction (G : Ω → B) (f : B → ℝ) (x : B) : ℝ :=
  ∫ ω, iteratedFDeriv ℝ 2 f x ![G ω, G ω] ∂P

/-- `Φ ∈ C_b^k(B)`: `C^k` with all derivatives of order `≤ k` bounded. -/
def MemCb (k : ℕ) (Φ : B → ℝ) : Prop :=
  ContDiff ℝ k Φ ∧ ∀ j ≤ k, BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ j Φ x‖)

end Stein

-- BEGIN STEIN AUX
section SteinAuxAll
open ProbabilityTheory

section ParamInt

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma contDiff_of_chain (f : B → ℝ) (N : ℕ) (D : ∀ j : ℕ, B → (B [×j]→L[ℝ] ℝ))
    (h0 : ∀ x, D 0 x = (continuousMultilinearCurryFin0 ℝ B ℝ).symm (f x))
    (h1 : ∀ j < N, ∀ x, HasFDerivAt (D j)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ (D (j+1) x)) x)
    (h2 : Continuous (D N)) :
    ContDiff ℝ N f ∧ ∀ j ≤ N, iteratedFDeriv ℝ j f = D j := by
  have heq : ∀ j ≤ N, iteratedFDeriv ℝ j f = D j := by
    intro j
    induction j with
    | zero =>
      intro _
      ext x : 1
      rw [h0]; rfl
    | succ j ih =>
      intro hj
      have ih' := ih (Nat.le_of_succ_le hj)
      ext x : 1
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih',
        (h1 j (Nat.lt_of_succ_le hj) x).fderiv]
      simp
  refine ⟨?_, heq⟩
  rw [contDiff_nat_iff_continuous_differentiable]
  constructor
  · intro m hm
    rw [heq m hm]
    rcases Nat.lt_or_ge m N with h | h
    · exact continuous_iff_continuousAt.2 fun x => (h1 m h x).continuousAt
    · have : m = N := le_antisymm (by exact_mod_cast hm) h
      subst this; exact h2
  · intro m hm
    rw [heq m (by exact_mod_cast hm.le)]
    exact fun x => (h1 m (by exact_mod_cast hm) x).differentiableAt


lemma integral_curryLeft_comm {S : Type*} [MeasurableSpace S] (ν : Measure S) (j : ℕ)
    (φ : S → (B [×(j+1)]→L[ℝ] ℝ)) (hφ : Integrable φ ν) :
    ∫ p, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ (φ p) ∂ν =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ (∫ p, φ p ∂ν) := by
  let L : (B [×(j+1)]→L[ℝ] ℝ) →L[ℝ] (B →L[ℝ] B [×j]→L[ℝ] ℝ) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  exact ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (E := B [×(j+1)]→L[ℝ] ℝ)
    (Fₗ := B →L[ℝ] B [×j]→L[ℝ] ℝ) L hφ

lemma contDiff_integral_dominated {S : Type*} [MeasurableSpace S] (ν : Measure S)
    (g : S → B → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hcd : ∀ p, ContDiff ℝ N (g p))
    (hint : ∀ x, Integrable (fun p => g p x) ν)
    (hmeas : ∀ j ≤ N, ∀ x, AEStronglyMeasurable (fun p => iteratedFDeriv ℝ j (g p) x) ν)
    (b : ℕ → S → ℝ) (hb : ∀ j, 1 ≤ j → j ≤ N → Integrable (b j) ν)
    (hbd : ∀ j, 1 ≤ j → j ≤ N → ∀ p x, ‖iteratedFDeriv ℝ j (g p) x‖ ≤ b j p) :
    ContDiff ℝ N (fun x => ∫ p, g p x ∂ν) ∧
      ∀ j ≤ N, ∀ x, iteratedFDeriv ℝ j (fun x => ∫ p, g p x ∂ν) x =
        ∫ p, iteratedFDeriv ℝ j (g p) x ∂ν := by
  set D : ∀ j : ℕ, B → (B [×j]→L[ℝ] ℝ) := fun j x => ∫ p, iteratedFDeriv ℝ j (g p) x ∂ν with hD
  have hF_int : ∀ j ≤ N, ∀ x, Integrable (fun p => iteratedFDeriv ℝ j (g p) x) ν := by
    intro j hj x
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      refine (hint x).norm.mono' (hmeas 0 (Nat.zero_le _) x) (Filter.Eventually.of_forall fun p => ?_)
      simp
    · exact (hb j h0 hj).mono' (hmeas j hj x) (Filter.Eventually.of_forall fun p => hbd j h0 hj p x)
  have h0 : ∀ x, D 0 x = (continuousMultilinearCurryFin0 ℝ B ℝ).symm (∫ p, g p x ∂ν) := by
    intro x
    simp only [hD]
    have := ContinuousLinearEquiv.integral_comp_comm (μ := ν)
      (continuousMultilinearCurryFin0 ℝ B ℝ).symm.toContinuousLinearEquiv (fun p => g p x)
    exact this
  have h1 : ∀ j < N, ∀ x, HasFDerivAt (D j)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ (D (j+1) x)) x := by
    intro j hj x₀
    have hjN : j + 1 ≤ N := hj
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (s := Set.univ)
      (F := fun x p => iteratedFDeriv ℝ j (g p) x)
      (F' := fun x p => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ
        (iteratedFDeriv ℝ (j+1) (g p) x))
      (x₀ := x₀) (bound := b (j+1)) Filter.univ_mem
      (Filter.Eventually.of_forall fun x => hmeas j (by omega) x)
      (hF_int j (by omega) x₀)
      (((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ).continuous.comp_aestronglyMeasurable
        (hmeas (j+1) hjN x₀)))
      (Filter.Eventually.of_forall fun p x _ => by
        rw [LinearIsometryEquiv.norm_map]; exact hbd (j+1) (by omega) hjN p x)
      (hb (j+1) (by omega) hjN)
      (Filter.Eventually.of_forall fun p x _ => by
        have hd : Differentiable ℝ (iteratedFDeriv ℝ j (g p)) :=
          (hcd p).differentiable_iteratedFDeriv (by exact_mod_cast hj)
        exact (hd x).hasFDerivAt)
    have e : ∫ p, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ
        (iteratedFDeriv ℝ (j+1) (g p) x₀) ∂ν =
        continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) ℝ (D (j+1) x₀) := by
      simp only [hD]
      exact integral_curryLeft_comm ν j _ (hF_int (j+1) hjN x₀)
    rw [← e]
    exact key
  have h2 : Continuous (D N) := by
    refine continuous_of_dominated (bound := b N) (fun x => (hmeas N le_rfl x))
      (fun x => Filter.Eventually.of_forall fun p => hbd N hN le_rfl p x) (hb N hN le_rfl)
      (Filter.Eventually.of_forall fun p => ?_)
    exact (hcd p).continuous_iteratedFDeriv (by exact_mod_cast le_rfl)
  obtain ⟨hC, hE⟩ := contDiff_of_chain (fun x => ∫ p, g p x ∂ν) N D h0 h1 h2
  refine ⟨hC, fun j hj x => ?_⟩
  rw [hE j hj]

end ParamInt


section SteinAux

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- OU scalings `e^{-u}` and `√(1-e^{-2u})`. -/
def ouA (u : ℝ) : ℝ := Real.exp (-u)
def ouS (u : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-2 * u))

lemma ouA_pos (u : ℝ) : 0 < ouA u := Real.exp_pos _
@[fun_prop] lemma continuous_ouA : Continuous ouA := by unfold ouA; fun_prop
@[fun_prop] lemma continuous_ouS : Continuous ouS := by unfold ouS; fun_prop
lemma ouA_sq (u : ℝ) : ouA u ^ 2 = Real.exp (-2 * u) := by
  unfold ouA; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
lemma ouA_le_one {u : ℝ} (hu : 0 ≤ u) : ouA u ≤ 1 := by
  unfold ouA; rw [Real.exp_le_one_iff]; linarith
lemma ouS_nonneg (u : ℝ) : 0 ≤ ouS u := Real.sqrt_nonneg _
lemma ouS_sq {u : ℝ} (hu : 0 ≤ u) : ouS u ^ 2 = 1 - ouA u ^ 2 := by
  unfold ouS; rw [Real.sq_sqrt, ouA_sq]
  rw [sub_nonneg, Real.exp_le_one_iff]; linarith
lemma ouA_sq_add_ouS_sq {u : ℝ} (hu : 0 ≤ u) : ouA u ^ 2 + ouS u ^ 2 = 1 := by
  rw [ouS_sq hu]; ring
lemma ouS_le_one {u : ℝ} (hu : 0 ≤ u) : ouS u ≤ 1 := by
  have := ouA_sq_add_ouS_sq hu
  nlinarith [sq_nonneg (ouA u), ouS_nonneg u]
lemma one_sub_ouS_le {u : ℝ} (hu : 0 ≤ u) : 1 - ouS u ≤ ouA u ^ 2 := by
  have h1 := ouS_le_one hu
  have h2 := ouA_sq_add_ouS_sq hu
  nlinarith [ouS_nonneg u]


/-- the integrand of the single-integral representation of the Stein solution -/
def steinG (Φ : B → ℝ) (p : ℝ × B) (x : B) : ℝ := Φ (ouA p.1 • x + ouS p.1 • p.2) - Φ p.2

lemma iteratedFDeriv_affine (Φ : B → ℝ) (hΦ : ContDiff ℝ 5 Φ) (c : ℝ) (w : B) (j : ℕ) (hj : j ≤ 5) (x : B) :
    iteratedFDeriv ℝ j (fun x => Φ (c • x + w)) x = c ^ j • iteratedFDeriv ℝ j Φ (c • x + w) := by
  have h1 : (fun x => Φ (c • x + w)) = (fun z => Φ (z + w)) ∘ (c • ContinuousLinearMap.id ℝ B) := by
    ext x; simp
  have hcd : ContDiff ℝ 5 (fun z => Φ (z + w)) := hΦ.comp (contDiff_id.add contDiff_const)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd x (by exact_mod_cast hj),
    iteratedFDeriv_comp_add_right]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousMultilinearMap.smul_apply]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

lemma iteratedFDeriv_steinG (Φ : B → ℝ) (hΦ : ContDiff ℝ 5 Φ) (p : ℝ × B) (j : ℕ) (hj1 : 1 ≤ j)
    (hj5 : j ≤ 5) (x : B) :
    iteratedFDeriv ℝ j (steinG Φ p) x =
      (ouA p.1) ^ j • iteratedFDeriv ℝ j Φ (ouA p.1 • x + ouS p.1 • p.2) := by
  have h1 : steinG Φ p = (fun x => Φ (ouA p.1 • x + ouS p.1 • p.2)) - fun _ => Φ p.2 := by
    ext x; rfl
  have hcd : ContDiff ℝ 5 (fun x => Φ (ouA p.1 • x + ouS p.1 • p.2)) :=
    hΦ.comp ((contDiff_const.smul contDiff_id).add contDiff_const)
  rw [h1, iteratedFDeriv_sub_apply (hcd.contDiffAt.of_le (by exact_mod_cast hj5))
    (contDiff_const.contDiffAt), iteratedFDeriv_const_of_ne (by omega), iteratedFDeriv_affine Φ hΦ _ _ j hj5]
  simp

lemma contDiff_steinG (Φ : B → ℝ) (hΦ : ContDiff ℝ 5 Φ) (p : ℝ × B) : ContDiff ℝ 5 (steinG Φ p) := by
  unfold steinG
  exact (hΦ.comp ((contDiff_const.smul contDiff_id).add contDiff_const)).sub contDiff_const


/-- sup norm of `j`-th derivative -/
def cbSup (Φ : B → ℝ) (j : ℕ) : ℝ := ⨆ y, ‖iteratedFDeriv ℝ j Φ y‖

lemma norm_iter_le_cbSup {Φ : B → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 5) (y : B) :
    ‖iteratedFDeriv ℝ j Φ y‖ ≤ cbSup Φ j :=
  le_ciSup (f := fun y => ‖iteratedFDeriv ℝ j Φ y‖) (hΦ.2 j hj) y

lemma cbSup_nonneg {Φ : B → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 5) : 0 ≤ cbSup Φ j :=
  (norm_nonneg _).trans (norm_iter_le_cbSup hΦ hj 0)

lemma abs_le_cbSup {Φ : B → ℝ} (hΦ : MemCb 5 Φ) (y : B) : |Φ y| ≤ cbSup Φ 0 := by
  have := norm_iter_le_cbSup hΦ (j := 0) (by norm_num) y
  simpa using this

lemma lip_cb {Φ : B → ℝ} (hΦ : MemCb 5 Φ) (y z : B) : |Φ z - Φ y| ≤ cbSup Φ 1 * ‖z - y‖ := by
  have hd : Differentiable ℝ Φ := hΦ.1.differentiable (by norm_num)
  have hL : LipschitzWith (Real.toNNReal (cbSup Φ 1)) Φ := by
    refine lipschitzWith_of_nnnorm_fderiv_le hd fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (cbSup_nonneg hΦ (by norm_num))]
    have := norm_iter_le_cbSup hΦ (j := 1) (by norm_num) x
    simpa using this
  have := hL.dist_le_mul z y
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (cbSup_nonneg hΦ (by norm_num))] at this
  exact this

section Gaussian
variable {γ : Measure B} [IsProbabilityMeasure γ]

/-- the product measure on `(0,∞) × B` -/
abbrev steinNu (γ : Measure B) : Measure (ℝ × B) := (volume.restrict (Set.Ioi (0:ℝ))).prod γ

lemma ae_steinNu_pos : ∀ᵐ p ∂(steinNu γ), 0 < p.1 := by
  have h : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0:ℝ))), 0 < u := ae_restrict_mem measurableSet_Ioi
  exact Measure.quasiMeasurePreserving_fst.ae h

lemma integrable_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    Integrable (fun u : ℝ => Real.exp (-c * u)) (volume.restrict (Set.Ioi (0:ℝ))) :=
  exp_neg_integrableOn_Ioi 0 hc

lemma ouA_pow (j : ℕ) (u : ℝ) : ouA u ^ j = Real.exp (-(j : ℝ) * u) := by
  unfold ouA; rw [← Real.exp_nat_mul]; congr 1; ring

variable {Φ : B → ℝ}

lemma steinG_integrable (hΦ : MemCb 5 Φ) (hγ1 : Integrable (fun y : B => ‖y‖) γ) (x : B) :
    Integrable (fun p => steinG Φ p x) (steinNu γ) := by
  set μ0 : Measure ℝ := volume.restrict (Set.Ioi (0:ℝ)) with hμ0
  have hA1 : Integrable (fun u : ℝ => ouA u) μ0 := by
    have := integrable_exp_neg_mul 1 one_pos
    simpa [ouA] using this
  have hA2 : Integrable (fun u : ℝ => ouA u ^ 2) μ0 := by
    have := integrable_exp_neg_mul 2 two_pos
    simpa [ouA_pow] using this
  have hbd : Integrable (fun p : ℝ × B => cbSup Φ 1 * (ouA p.1 * ‖x‖ + ouA p.1 ^ 2 * ‖p.2‖)) (steinNu γ) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact ((hA1.mul_const ‖x‖).comp_fst γ)
    · exact hA2.mul_prod hγ1
  refine hbd.mono' ?_ ?_
  · have hc : Continuous (fun p : ℝ × B => steinG Φ p x) := by
      unfold steinG
      have hΦc := hΦ.1.continuous
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [ae_steinNu_pos (γ := γ)] with p hp
    unfold steinG
    rw [Real.norm_eq_abs]
    refine (lip_cb hΦ p.2 _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (cbSup_nonneg hΦ (by norm_num))
    have h1 : ouA p.1 • x + ouS p.1 • p.2 - p.2 = ouA p.1 • x - (1 - ouS p.1) • p.2 := by
      module
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (ouA_pos _),
      abs_of_nonneg (sub_nonneg.2 (ouS_le_one hp.le))]
    gcongr
    exact one_sub_ouS_le hp.le


lemma steinG_meas (hΦ : MemCb 5 Φ) (j : ℕ) (hj : j ≤ 5) (x : B) :
    AEStronglyMeasurable (fun p => iteratedFDeriv ℝ j (steinG Φ p) x) (steinNu γ) := by
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    have hc : Continuous (fun p : ℝ × B => steinG Φ p x) := by
      unfold steinG
      have hΦc := hΦ.1.continuous
      fun_prop
    have : (fun p => iteratedFDeriv ℝ 0 (steinG Φ p) x) =
        fun p => (continuousMultilinearCurryFin0 ℝ B ℝ).symm (steinG Φ p x) := rfl
    rw [this]
    exact ((continuousMultilinearCurryFin0 ℝ B ℝ).symm.continuous.comp hc).aestronglyMeasurable
  · have hc : Continuous (fun p : ℝ × B =>
        (ouA p.1) ^ j • iteratedFDeriv ℝ j Φ (ouA p.1 • x + ouS p.1 • p.2)) := by
      have hΦc := hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)
      fun_prop
    have : (fun p => iteratedFDeriv ℝ j (steinG Φ p) x) =
        fun p : ℝ × B => (ouA p.1) ^ j • iteratedFDeriv ℝ j Φ (ouA p.1 • x + ouS p.1 • p.2) := by
      ext1 p; exact iteratedFDeriv_steinG Φ hΦ.1 p j h0 hj x
    rw [this]
    exact hc.aestronglyMeasurable

lemma steinG_bound (hΦ : MemCb 5 Φ) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 5) (p : ℝ × B) (x : B) :
    ‖iteratedFDeriv ℝ j (steinG Φ p) x‖ ≤ cbSup Φ j * Real.exp (-(j : ℝ) * p.1) := by
  rw [iteratedFDeriv_steinG Φ hΦ.1 p j hj1 hj, norm_smul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (ouA_pos _), ouA_pow, mul_comm]
  gcongr
  exact norm_iter_le_cbSup hΦ hj _

lemma steinG_bound_int (hΦ : MemCb 5 Φ) (j : ℕ) (hj1 : 1 ≤ j) :
    Integrable (fun p : ℝ × B => cbSup Φ j * Real.exp (-(j : ℝ) * p.1)) (steinNu γ) := by
  have h := (integrable_exp_neg_mul (j : ℝ) (by exact_mod_cast hj1)).const_mul (cbSup Φ j)
  exact h.comp_fst γ

lemma stein_contDiff_core (hΦ : MemCb 5 Φ) (hγ1 : Integrable (fun y : B => ‖y‖) γ) :
    ContDiff ℝ 5 (fun x => ∫ p, steinG Φ p x ∂(steinNu γ)) ∧
      ∀ j ≤ 5, ∀ x, iteratedFDeriv ℝ j (fun x => ∫ p, steinG Φ p x ∂(steinNu γ)) x =
        ∫ p, iteratedFDeriv ℝ j (steinG Φ p) x ∂(steinNu γ) := by
  refine contDiff_integral_dominated (steinNu γ) (steinG Φ) 5 (by norm_num)
    (contDiff_steinG Φ hΦ.1) (steinG_integrable hΦ hγ1) (fun j hj x => steinG_meas hΦ j hj x)
    (fun j p => cbSup Φ j * Real.exp (-(j : ℝ) * p.1))
    (fun j hj1 _ => steinG_bound_int hΦ j hj1) (fun j hj1 hj5 p x => steinG_bound hΦ j hj1 hj5 p x)


lemma integrable_cont_bdd' (hΦ : MemCb 5 Φ) (a s : ℝ) (x : B) :
    Integrable (fun y : B => Φ (a • x + s • y)) γ := by
  refine Integrable.of_bound (C := cbSup Φ 0) ?_ ?_
  · exact (hΦ.1.continuous.comp (by fun_prop : Continuous fun y : B => a • x + s • y)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_le_cbSup hΦ _

lemma integrable_Phi (hΦ : MemCb 5 Φ) : Integrable Φ γ := by
  refine Integrable.of_bound (C := cbSup Φ 0) hΦ.1.continuous.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_le_cbSup hΦ _

/-- the Stein solution as a single integral against `ν` (γ-form) -/
lemma stein_inner (hΦ : MemCb 5 Φ) (x : B) (u : ℝ) :
    ∫ y, steinG Φ (u, y) x ∂γ =
      ∫ y, Φ (ouA u • x + ouS u • y) ∂γ - ∫ y, Φ y ∂γ := by
  unfold steinG
  simp only
  exact integral_sub (integrable_cont_bdd' hΦ _ _ _) (integrable_Phi hΦ)


/-- Stein solution in terms of the Gaussian law `γ` -/
def steinSolG (γ : Measure B) (Φ : B → ℝ) (x : B) : ℝ :=
  -∫ u in Set.Ioi (0 : ℝ), (∫ y, Φ (ouA u • x + ouS u • y) ∂γ - ∫ y, Φ y ∂γ)

lemma steinSolG_eq_nu (hΦ : MemCb 5 Φ) (hγ1 : Integrable (fun y : B => ‖y‖) γ) (x : B) :
    steinSolG γ Φ x = -∫ p, steinG Φ p x ∂(steinNu γ) := by
  unfold steinSolG
  congr 1
  rw [integral_prod _ (steinG_integrable hΦ hγ1 x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact (stein_inner hΦ x u).symm

lemma contDiff_steinSolG (hΦ : MemCb 5 Φ) (hγ1 : Integrable (fun y : B => ‖y‖) γ) :
    ContDiff ℝ 5 (steinSolG γ Φ) := by
  have h := (stein_contDiff_core (γ := γ) hΦ hγ1).1.neg
  have e : steinSolG γ Φ = fun x => -∫ p, steinG Φ p x ∂(steinNu γ) := by
    ext x; exact steinSolG_eq_nu hΦ hγ1 x
  rw [e]; exact h

lemma iteratedFDeriv_steinSolG (hΦ : MemCb 5 Φ) (hγ1 : Integrable (fun y : B => ‖y‖) γ)
    (j : ℕ) (hj : j ≤ 5) (x : B) :
    iteratedFDeriv ℝ j (steinSolG γ Φ) x = -∫ p, iteratedFDeriv ℝ j (steinG Φ p) x ∂(steinNu γ) := by
  have e : steinSolG γ Φ = -(fun x => ∫ p, steinG Φ p x ∂(steinNu γ)) := by
    ext x; exact steinSolG_eq_nu hΦ hγ1 x
  have hcd := (stein_contDiff_core (γ := γ) hΦ hγ1).1
  rw [e, iteratedFDeriv_neg_apply, (stein_contDiff_core (γ := γ) hΦ hγ1).2 j hj x]

lemma norm_iteratedFDeriv_steinSolG_le (hΦ : MemCb 5 Φ) (hγ1 : Integrable (fun y : B => ‖y‖) γ)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 5) (x : B) :
    ‖iteratedFDeriv ℝ j (steinSolG γ Φ) x‖ ≤ (j : ℝ)⁻¹ * cbSup Φ j := by
  rw [iteratedFDeriv_steinSolG hΦ hγ1 j hj x, norm_neg]
  refine (norm_integral_le_of_norm_le (steinG_bound_int hΦ j hj1)
    (Filter.Eventually.of_forall fun p => steinG_bound hΦ j hj1 hj p x)).trans (le_of_eq ?_)
  rw [integral_prod _ (steinG_bound_int hΦ j hj1)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [integral_const_mul]
  have hj0 : (0:ℝ) < j := by exact_mod_cast hj1
  have := integral_exp_mul_Ioi (a := -(j:ℝ)) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at this
  rw [this]
  field_simp

end Gaussian


section PLevel
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable {Φ : B → ℝ}

lemma steinSolution_eq_steinSolG (G : Ω → B) (hG : AEMeasurable G P) (hΦ : MemCb 5 Φ) :
    steinSolution P G Φ = steinSolG (P.map G) Φ := by
  funext x
  unfold steinSolution steinSolG
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have h1 : ∫ ω, Φ (Real.exp (-u) • x + Real.sqrt (1 - Real.exp (-2 * u)) • G ω) ∂P =
      ∫ y, Φ (ouA u • x + ouS u • y) ∂(P.map G) := by
    rw [integral_map hG]
    · rfl
    · exact (hΦ.1.continuous.comp (by fun_prop : Continuous fun y : B => ouA u • x + ouS u • y)).aestronglyMeasurable
  have h2 : ∫ ω, Φ (G ω) ∂P = ∫ y, Φ y ∂(P.map G) := by
    rw [integral_map hG hΦ.1.continuous.aestronglyMeasurable]
  rw [h1, h2]

lemma gaussian_norm_integrable (G : Ω → B) (hGauss : IsCenteredGaussian (law P G)) :
    Integrable (fun y : B => ‖y‖) (P.map G) := by
  haveI := hGauss.1
  exact (IsGaussian.integrable_id (μ := P.map G)).norm

theorem stein_bounds' (G : Ω → B) (hG : AEMeasurable G P) (hGauss : IsCenteredGaussian (law P G))
    (Φ : B → ℝ) (hΦ : MemCb 5 Φ) :
    (∀ x, IntegrableOn (fun u : ℝ =>
        ∫ ω, Φ (Real.exp (-u) • x + Real.sqrt (1 - Real.exp (-2 * u)) • G ω) ∂P -
          ∫ ω, Φ (G ω) ∂P) (Set.Ioi 0)) ∧
    ContDiff ℝ 5 (steinSolution P G Φ) ∧
    ∀ j, 1 ≤ j → j ≤ 5 → ∀ x,
      ‖iteratedFDeriv ℝ j (steinSolution P G Φ) x‖ ≤
        (j : ℝ)⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ j Φ y‖ := by
  haveI := hGauss.1
  have hγ1 := gaussian_norm_integrable P G hGauss
  refine ⟨fun x => ?_, ?_, fun j hj1 hj5 x => ?_⟩
  · have h : IntegrableOn (fun u : ℝ => ∫ y, steinG Φ (u, y) x ∂(P.map G)) (Set.Ioi 0) :=
      (steinG_integrable (γ := P.map G) hΦ hγ1 x).integral_prod_left
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    show ∫ y, steinG Φ (u, y) x ∂(P.map G) = _
    rw [stein_inner hΦ x u]
    have h1 : ∫ ω, Φ (Real.exp (-u) • x + Real.sqrt (1 - Real.exp (-2 * u)) • G ω) ∂P =
        ∫ y, Φ (ouA u • x + ouS u • y) ∂(P.map G) := by
      rw [integral_map hG]
      · rfl
      · exact (hΦ.1.continuous.comp (by fun_prop : Continuous fun y : B => ouA u • x + ouS u • y)).aestronglyMeasurable
    have h2 : ∫ ω, Φ (G ω) ∂P = ∫ y, Φ y ∂(P.map G) := by
      rw [integral_map hG hΦ.1.continuous.aestronglyMeasurable]
    rw [h1, h2]
  · rw [steinSolution_eq_steinSolG P G hG hΦ]
    exact contDiff_steinSolG hΦ hγ1
  · rw [steinSolution_eq_steinSolG P G hG hΦ]
    exact norm_iteratedFDeriv_steinSolG_le hΦ hγ1 j hj1 hj5 x

end PLevel

end SteinAux

section GaussRot
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {γ : Measure B} [IsProbabilityMeasure γ]

/-- centered Gaussian: the mean vanishes -/
lemma gaussian_integral_id_eq_zero (hγ : IsCenteredGaussian γ) : γ[id] = 0 := by
  have := hγ.1
  have h : ∫ x, x ∂γ = 0 := by
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun L => ?_
    have h1 := IsGaussian.integral_dual (μ := γ) L
    rw [← h1]; exact hγ.2 L
  simpa using h

/-- rotation invariance in the form needed for the Ornstein–Uhlenbeck semigroup -/
lemma gaussian_comb_map (hγ : IsCenteredGaussian γ) {a s : ℝ} (hs : 0 ≤ s)
    (has : a ^ 2 + s ^ 2 = 1) :
    (γ.prod γ).map (fun q : B × B => a • q.1 + s • q.2) = γ := by
  have := hγ.1
  obtain ⟨θ, hc, hsn⟩ : ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = s := by
    refine ⟨Real.arccos a, Real.cos_arccos (by nlinarith) (by nlinarith), ?_⟩
    rw [Real.sin_arccos]
    have : 1 - a ^ 2 = s ^ 2 := by linarith
    rw [this, Real.sqrt_sq hs]
  have hrot := IsGaussian.map_rotation_eq_self (μ := γ) (gaussian_integral_id_eq_zero hγ) θ
  have e : (fun q : B × B => a • q.1 + s • q.2) = Prod.fst ∘ (ContinuousLinearMap.rotation θ) := by
    ext q <;> simp [ContinuousLinearMap.rotation_apply, hc, hsn]
  rw [e, ← Measure.map_map measurable_fst (ContinuousLinearMap.rotation θ).continuous.measurable, hrot]
  simp



/-- Gaussian rotation: the OU kernel preserves the Gaussian law, in integrated form. -/
lemma gaussian_comb_integral (hγ : IsCenteredGaussian γ) {a s : ℝ} (hs : 0 ≤ s)
    (has : a ^ 2 + s ^ 2 = 1) {h : B → ℝ} (hc : Continuous h) {M : ℝ} (hM : ∀ z, |h z| ≤ M) :
    ∫ y, ∫ x, h (a • x + s • y) ∂γ ∂γ = ∫ z, h z ∂γ := by
  have hint : Integrable (fun q : B × B => h (a • q.1 + s • q.2)) (γ.prod γ) := by
    refine Integrable.of_bound (C := M) ?_ (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]; exact hM _)
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  rw [← integral_prod_symm (fun q : B × B => h (a • q.1 + s • q.2)) hint]
  have hm : Measurable fun q : B × B => a • q.1 + s • q.2 := by fun_prop
  have := integral_map (μ := γ.prod γ) hm.aemeasurable (f := h) hc.aestronglyMeasurable
  rw [gaussian_comb_map hγ hs has] at this
  exact this.symm


variable {Φ : B → ℝ}

lemma iter3_steinSolG_apply (hΦ : MemCb 5 Φ) (hγ1 : Integrable (fun y : B => ‖y‖) γ) (x : B)
    (v : Fin 3 → B) :
    iteratedFDeriv ℝ 3 (steinSolG γ Φ) x v =
      -∫ p, ouA p.1 ^ 3 * iteratedFDeriv ℝ 3 Φ (ouA p.1 • x + ouS p.1 • p.2) v ∂(steinNu γ) := by
  rw [iteratedFDeriv_steinSolG hΦ hγ1 3 (by norm_num) x, neg_apply]
  congr 1
  have hint : Integrable (fun p => iteratedFDeriv ℝ 3 (steinG Φ p) x) (steinNu γ) :=
    (steinG_bound_int hΦ 3 (by norm_num)).mono' (steinG_meas hΦ 3 (by norm_num) x)
      (Filter.Eventually.of_forall fun p => steinG_bound hΦ 3 (by norm_num) (by norm_num) p x)
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => B) ℝ v).integral_comp_comm hint
  simp only [ContinuousMultilinearMap.apply_apply] at this
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show (iteratedFDeriv ℝ 3 (steinG Φ p) x) v = _
  rw [iteratedFDeriv_steinG Φ hΦ.1 p 3 (by norm_num) (by norm_num) x]
  simp

lemma third_core (hγ : IsCenteredGaussian γ) (hΦ : MemCb 5 Φ)
    (hγ1 : Integrable (fun y : B => ‖y‖) γ) (v : Fin 3 → B) :
    ∫ x, iteratedFDeriv ℝ 3 (steinSolG γ Φ) x v ∂γ =
      -(1 / 3) * ∫ z, iteratedFDeriv ℝ 3 Φ z v ∂γ := by
  set h : B → ℝ := fun z => iteratedFDeriv ℝ 3 Φ z v with hh
  have hc : Continuous h :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => B) ℝ v).continuous.comp
      (hΦ.1.continuous_iteratedFDeriv (m := 3) (by norm_num))
  set M : ℝ := cbSup Φ 3 * ∏ i, ‖v i‖ with hM
  have hbd : ∀ z, |h z| ≤ M := fun z => by
    have := (iteratedFDeriv ℝ 3 Φ z).le_opNorm v
    rw [← Real.norm_eq_abs]
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (norm_iter_le_cbSup hΦ (by norm_num) z)
      (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hbd 0)
  let Fn : B → ℝ × B → ℝ := fun x p => ouA p.1 ^ 3 * h (ouA p.1 • x + ouS p.1 • p.2)
  have hbdint : Integrable (fun z : B × (ℝ × B) => M * Real.exp (-(3:ℝ) * z.2.1)) (γ.prod (steinNu γ)) := by
    have h1 := ((integrable_exp_neg_mul 3 (by norm_num)).const_mul M).comp_fst γ
    exact Integrable.comp_snd (f := fun p : ℝ × B => M * Real.exp (-(3:ℝ) * p.1)) h1 γ
  have hint2 : Integrable (Function.uncurry Fn) (γ.prod (steinNu γ)) := by
    refine hbdint.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have : Continuous (Function.uncurry Fn) := by
        have := hc
        simp only [Function.uncurry, Fn]
        fun_prop
      exact this.aestronglyMeasurable
    · simp only [Function.uncurry, Fn]
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (ouA_pos _), ouA_pow, Real.norm_eq_abs,
        mul_comm]
      exact mul_le_mul_of_nonneg_right (hbd _) (Real.exp_pos _).le
  calc ∫ x, iteratedFDeriv ℝ 3 (steinSolG γ Φ) x v ∂γ
      = ∫ x, -∫ p, Fn x p ∂(steinNu γ) ∂γ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => iter3_steinSolG_apply hΦ hγ1 x v)
    _ = -∫ x, ∫ p, Fn x p ∂(steinNu γ) ∂γ := integral_neg _
    _ = -∫ p, ∫ x, Fn x p ∂γ ∂(steinNu γ) := by rw [integral_integral_swap hint2]
    _ = -∫ u in Set.Ioi (0:ℝ), ∫ y, ∫ x, Fn x (u, y) ∂γ ∂γ := by
        congr 1
        exact integral_prod (fun p : ℝ × B => ∫ x, Fn x p ∂γ) hint2.integral_prod_right
    _ = -∫ u in Set.Ioi (0:ℝ), ouA u ^ 3 * ∫ z, h z ∂γ := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 ≤ u := le_of_lt hu
        simp only [Fn]
        simp_rw [integral_const_mul]
        congr 1
        exact gaussian_comb_integral hγ (ouS_nonneg u) (ouA_sq_add_ouS_sq hu0) hc hbd
    _ = -(1 / 3) * ∫ z, h z ∂γ := by
        congr 1
        rw [integral_mul_const]
        have h3 : ∫ u in Set.Ioi (0:ℝ), ouA u ^ 3 = 1 / 3 := by
          simp_rw [ouA_pow]
          have := integral_exp_mul_Ioi (a := -(3:ℕ)) (by norm_num) 0
          simp only [mul_zero, Real.exp_zero] at this
          rw [this]; norm_num
        rw [h3]; ring


section PLevel3
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma stein_third' (G : Ω → B) (hG : AEMeasurable G P) (hGauss : IsCenteredGaussian (law P G))
    (hΦ : MemCb 5 Φ) (v : Fin 3 → B) :
    ∫ ω, iteratedFDeriv ℝ 3 (steinSolution P G Φ) (G ω) v ∂P =
      -(1 / 3) * ∫ ω, iteratedFDeriv ℝ 3 Φ (G ω) v ∂P := by
  have := hGauss.1
  have hγ1 := gaussian_norm_integrable P G hGauss
  have hf := contDiff_steinSolG (γ := P.map G) hΦ hγ1
  rw [steinSolution_eq_steinSolG P G hG hΦ]
  have c1 : Continuous fun x => iteratedFDeriv ℝ 3 (steinSolG (P.map G) Φ) x v :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => B) ℝ v).continuous.comp
      (hf.continuous_iteratedFDeriv (m := 3) (by norm_num))
  have c2 : Continuous fun x => iteratedFDeriv ℝ 3 Φ x v :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => B) ℝ v).continuous.comp
      (hΦ.1.continuous_iteratedFDeriv (m := 3) (by norm_num))
  have e1 := integral_map hG c1.aestronglyMeasurable
  have e2 := integral_map hG c2.aestronglyMeasurable
  exact e1.symm.trans ((third_core hGauss hΦ hγ1 v).trans (by rw [e2]))

end PLevel3

end GaussRot

end SteinAuxAll
-- END STEIN AUX

/-! ### Gaussian integration by parts and the Stein equation (Lemma 7.2, `F:eq:Stein-eq`) -/

section GaussIBP
open ProbabilityTheory
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {γ : Measure B} [IsProbabilityMeasure γ]

lemma gaussian_sqnorm_integrable (hγ : IsCenteredGaussian γ) :
    Integrable (fun y : B => ‖y‖ ^ 2) γ := by
  haveI := hγ.1
  have := (IsGaussian.memLp_id γ 2 (by norm_num)).integrable_norm_pow (by norm_num)
  simpa using this

lemma integral_fst_prod {g : B → ℝ} (hg : Integrable g γ) :
    ∫ q : B × B, g q.1 ∂(γ.prod γ) = ∫ w, g w ∂γ := by
  rw [integral_prod _ (hg.comp_fst γ)]
  simp


lemma gaussian_ibp (hγ : IsCenteredGaussian γ) {Φ : B → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {M1 M2 : ℝ} (h1 : ∀ w, ‖fderiv ℝ Φ w‖ ≤ M1) (h2 : ∀ w, ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ M2)
    (c : B) (s : ℝ) :
    ∫ w, fderiv ℝ Φ (c + s • w) w ∂γ =
      s * ∫ w, ∫ z, fderiv ℝ (fderiv ℝ Φ) (c + s • w) z z ∂γ ∂γ := by
  have := hγ.1
  have hM1 : 0 ≤ M1 := (norm_nonneg (fderiv ℝ Φ 0)).trans (h1 0)
  have hM2 : 0 ≤ M2 := (norm_nonneg (fderiv ℝ (fderiv ℝ Φ) 0)).trans (h2 0)
  have hd1 : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv (by norm_num)
  have hd2 : Continuous (fderiv ℝ (fderiv ℝ Φ)) := by
    have : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
    exact this.continuous_fderiv (by norm_num)
  have hdiff1 : Differentiable ℝ (fderiv ℝ Φ) := by
    have : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
    exact this.differentiable (by norm_num)
  set μ := γ.prod γ with hμ
  have hint1 : Integrable (fun w : B => ‖w‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hint2 := gaussian_sqnorm_integrable hγ
  -- the rotated integrand
  let pt : ℝ → B × B → B := fun θ q => c + s • (Real.cos θ • q.1 + Real.sin θ • q.2)
  let vec : ℝ → B × B → B := fun θ q => -(Real.sin θ) • q.1 + Real.cos θ • q.2
  let F : ℝ → B × B → ℝ := fun θ q => fderiv ℝ Φ (pt θ q) (vec θ q)
  let F' : ℝ → B × B → ℝ := fun θ q =>
    fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q) (vec θ q) +
      fderiv ℝ Φ (pt θ q) (-(Real.cos θ • q.1 + Real.sin θ • q.2))
  have hFcont : ∀ θ, Continuous (F θ) := fun θ => by
    simp only [F, pt, vec]
    exact hd1.comp (by fun_prop) |>.clm_apply (by fun_prop)
  -- invariance
  have hrotmeas : ∀ θ : ℝ, Measurable (ContinuousLinearMap.rotation θ : B × B → B × B) :=
    fun θ => (ContinuousLinearMap.rotation θ).continuous.measurable
  have hJ : ∀ θ, ∫ q, F θ q ∂μ = ∫ q, F 0 q ∂μ := by
    intro θ
    have hrot := IsGaussian.map_rotation_eq_self (μ := γ) (gaussian_integral_id_eq_zero hγ) θ
    have e : ∀ q : B × B, F θ q = F 0 (ContinuousLinearMap.rotation θ q) := by
      intro q
      simp [F, pt, vec, ContinuousLinearMap.rotation_apply]
    have h := integral_map (μ := μ) (hrotmeas θ).aemeasurable (f := F 0)
      (hFcont 0).aestronglyMeasurable
    rw [hrot] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall e)
  -- pointwise derivative
  have hpt : ∀ (θ : ℝ) (q : B × B), HasDerivAt (fun θ => pt θ q) (s • vec θ q) θ := by
    intro θ q
    have h1 := ((Real.hasDerivAt_cos θ).smul_const q.1).add ((Real.hasDerivAt_sin θ).smul_const q.2)
    have h2 := (h1.const_smul s).const_add c
    convert h2 using 1
  have hvec : ∀ (θ : ℝ) (q : B × B), HasDerivAt (fun θ => vec θ q)
      (-(Real.cos θ • q.1 + Real.sin θ • q.2)) θ := by
    intro θ q
    have h1 := ((Real.hasDerivAt_sin θ).neg.smul_const q.1).add ((Real.hasDerivAt_cos θ).smul_const q.2)
    convert h1 using 1
    module
  have hderivF : ∀ (θ : ℝ) (q : B × B), HasDerivAt (fun θ => F θ q) (F' θ q) θ := by
    intro θ q
    have h1 : HasDerivAt (fun θ => fderiv ℝ Φ (pt θ q))
        (fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q)) θ :=
      (hdiff1 (pt θ q)).hasFDerivAt.comp_hasDerivAt θ (hpt θ q)
    exact h1.clm_apply (hvec θ q)
  have hn1 : ∀ (θ : ℝ) (q : B × B), ‖vec θ q‖ ≤ ‖q.1‖ + ‖q.2‖ := by
    intro θ q
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, norm_neg, Real.norm_eq_abs]
    have a1 := Real.abs_sin_le_one θ
    have a2 := Real.abs_cos_le_one θ
    nlinarith [norm_nonneg q.1, norm_nonneg q.2]
  have hn2 : ∀ (θ : ℝ) (q : B × B), ‖Real.cos θ • q.1 + Real.sin θ • q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := by
    intro θ q
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs]
    have a1 := Real.abs_sin_le_one θ
    have a2 := Real.abs_cos_le_one θ
    nlinarith [norm_nonneg q.1, norm_nonneg q.2]
  set b : B × B → ℝ := fun q => M2 * |s| * (‖q.1‖ + ‖q.2‖) ^ 2 + M1 * (‖q.1‖ + ‖q.2‖) with hb
  have hn1int : Integrable (fun q : B × B => ‖q.1‖ + ‖q.2‖) μ :=
    (hint1.comp_fst γ).add (hint1.comp_snd γ)
  have hn2int : Integrable (fun q : B × B => (‖q.1‖ + ‖q.2‖) ^ 2) μ := by
    have := ((hint2.comp_fst γ).add ((hint1.mul_prod hint1).const_mul 2)).add (hint2.comp_snd γ)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]
    ring
  have hbint : Integrable b μ := (hn2int.const_mul (M2 * |s|)).add (hn1int.const_mul M1)
  have hFbound : ∀ (θ : ℝ) (q : B × B), ‖F θ q‖ ≤ M1 * (‖q.1‖ + ‖q.2‖) := by
    intro θ q
    refine ((fderiv ℝ Φ (pt θ q)).le_opNorm _).trans ?_
    exact mul_le_mul (h1 _) (hn1 θ q) (norm_nonneg _) hM1
  have hF'bound : ∀ (θ : ℝ) (q : B × B), ‖F' θ q‖ ≤ b q := by
    intro θ q
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q) (vec θ q)‖ ≤
        M2 * |s| * (‖q.1‖ + ‖q.2‖) ^ 2 := by
      refine ((fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q)).le_opNorm _).trans ?_
      have : ‖fderiv ℝ (fderiv ℝ Φ) (pt θ q) (s • vec θ q)‖ ≤ M2 * (|s| * (‖q.1‖ + ‖q.2‖)) := by
        refine ((fderiv ℝ (fderiv ℝ Φ) (pt θ q)).le_opNorm _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (h2 _) (mul_le_mul_of_nonneg_left (hn1 θ q) (abs_nonneg _)) (by positivity) hM2
      calc _ ≤ M2 * (|s| * (‖q.1‖ + ‖q.2‖)) * (‖q.1‖ + ‖q.2‖) :=
            mul_le_mul this (hn1 θ q) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have e2 : ‖fderiv ℝ Φ (pt θ q) (-(Real.cos θ • q.1 + Real.sin θ • q.2))‖ ≤
        M1 * (‖q.1‖ + ‖q.2‖) := by
      refine ((fderiv ℝ Φ (pt θ q)).le_opNorm _).trans ?_
      rw [norm_neg]
      exact mul_le_mul (h1 _) (hn2 θ q) (norm_nonneg _) hM1
    exact add_le_add e1 e2
  have hF'cont : ∀ θ, Continuous (F' θ) := fun θ => by
    simp only [F', pt, vec]
    refine Continuous.add ?_ ?_
    · exact (hd2.comp (by fun_prop)).clm_apply (by fun_prop) |>.clm_apply (by fun_prop)
    · exact (hd1.comp (by fun_prop)).clm_apply (by fun_prop)
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (x₀ := 0) (bound := b) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun θ => (hFcont θ).aestronglyMeasurable)
    (((hn1int.const_mul M1)).mono' (hFcont 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => hFbound 0 q))
    (hF'cont 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q θ _ => hF'bound θ q) hbint
    (Filter.Eventually.of_forall fun q θ _ => hderivF θ q)
  have hconst : HasDerivAt (fun θ => ∫ q, F θ q ∂μ) 0 0 := by
    have : (fun θ => ∫ q, F θ q ∂μ) = fun _ => ∫ q, F 0 q ∂μ := funext hJ
    rw [this]; exact hasDerivAt_const _ _
  have hzero : ∫ q, F' 0 q ∂μ = 0 := hD.2.unique hconst
  -- evaluate at θ = 0
  have hF'0 : ∀ q : B × B, F' 0 q = s * fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2 q.2 -
      fderiv ℝ Φ (c + s • q.1) q.1 := by
    intro q
    simp [F', pt, vec]
    ring
  have hAcont : Continuous fun q : B × B => fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2 q.2 :=
    ((hd2.comp (by fun_prop)).clm_apply (by fun_prop)).clm_apply (by fun_prop)
  have hBcont : Continuous fun q : B × B => fderiv ℝ Φ (c + s • q.1) q.1 :=
    (hd1.comp (by fun_prop)).clm_apply (by fun_prop)
  have hAint : Integrable (fun q : B × B => fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2 q.2) μ := by
    refine (hint2.comp_snd γ |>.const_mul M2).mono' hAcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    refine ((fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2).le_opNorm _).trans ?_
    have : ‖fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2‖ ≤ M2 * ‖q.2‖ :=
      ((fderiv ℝ (fderiv ℝ Φ) (c + s • q.1)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (h2 _) (norm_nonneg _))
    calc _ ≤ M2 * ‖q.2‖ * ‖q.2‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by ring
  have hBint : Integrable (fun q : B × B => fderiv ℝ Φ (c + s • q.1) q.1) μ := by
    refine (hint1.comp_fst γ |>.const_mul M1).mono' hBcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    exact ((fderiv ℝ Φ (c + s • q.1)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _))
  have hBint' : Integrable (fun w : B => fderiv ℝ Φ (c + s • w) w) γ := by
    refine (hint1.const_mul M1).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
    · exact ((hd1.comp (by fun_prop : Continuous fun w : B => c + s • w)).clm_apply
        continuous_id).aestronglyMeasurable
    · exact ((fderiv ℝ Φ (c + s • w)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _))
  have hz : s * ∫ q, fderiv ℝ (fderiv ℝ Φ) (c + s • q.1) q.2 q.2 ∂μ -
      ∫ q, fderiv ℝ Φ (c + s • q.1) q.1 ∂μ = 0 := by
    rw [← integral_const_mul, ← integral_sub (hAint.const_mul s) hBint]
    rw [← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hF'0 q).symm)
  rw [integral_prod _ hAint] at hz
  have hB := integral_fst_prod (γ := γ) (g := fun w => fderiv ℝ Φ (c + s • w) w) hBint'
  linarith


lemma ouS_pos {u : ℝ} (hu : 0 < u) : 0 < ouS u := by
  unfold ouS
  refine Real.sqrt_pos.2 ?_
  have : Real.exp (-2 * u) < 1 := by
    have := Real.exp_lt_exp.2 (show -2 * u < 0 by linarith)
    simpa using this
  linarith

lemma ouS_mono {u v : ℝ} (h : u ≤ v) : ouS u ≤ ouS v := by
  unfold ouS
  refine Real.sqrt_le_sqrt ?_
  have : Real.exp (-2 * v) ≤ Real.exp (-2 * u) := Real.exp_le_exp.2 (by linarith)
  linarith

lemma hasDerivAt_ouA (u : ℝ) : HasDerivAt ouA (-ouA u) u := by
  have := (hasDerivAt_id u).neg.exp
  convert this using 1
  · funext x; simp [ouA]
  · simp [ouA]

lemma hasDerivAt_ouS {u : ℝ} (hu : 0 < u) : HasDerivAt ouS (ouA u ^ 2 / ouS u) u := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - Real.exp (-2 * u)) (2 * Real.exp (-2 * u)) u := by
    have := (((hasDerivAt_id u).const_mul (-2)).exp).const_sub 1
    convert this using 1
    · rfl
    · simp only [id]
      ring_nf
  have hne : 1 - Real.exp (-2 * u) ≠ 0 := by
    have : Real.exp (-2 * u) < 1 := by
      have := Real.exp_lt_exp.2 (show -2 * u < 0 by linarith)
      simpa using this
    linarith
  have h2 := h1.sqrt hne
  have hs : ouS u ≠ 0 := (ouS_pos hu).ne'
  have e : ouS = fun y => √(1 - Real.exp (-2 * y)) := rfl
  rw [e]
  convert h2 using 1
  rw [ouA_sq]
  simp only
  field_simp
  
lemma norm_fderiv_le_cbSup {Φ : B → ℝ} (hΦ : MemCb 5 Φ) (w : B) : ‖fderiv ℝ Φ w‖ ≤ cbSup Φ 1 := by
  have := norm_iter_le_cbSup hΦ (j := 1) (by norm_num) w
  simpa using this

lemma norm_fderiv2_le_cbSup {Φ : B → ℝ} (hΦ : MemCb 5 Φ) (w : B) :
    ‖fderiv ℝ (fderiv ℝ Φ) w‖ ≤ cbSup Φ 2 := by
  have := norm_iter_le_cbSup hΦ (j := 2) (by norm_num) w
  rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Φ) (n := 1)] at this
  simpa using this


variable {Φ : B → ℝ}

lemma hasDerivAt_stein_T (hγ : IsCenteredGaussian γ) (hΦ : MemCb 5 Φ) (x : B) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    HasDerivAt (fun u => ∫ y, Φ (ouA u • x + ouS u • y) ∂γ)
      (ouA u₀ ^ 2 * ∫ y', ∫ y, fderiv ℝ (fderiv ℝ Φ) (ouA u₀ • x + ouS u₀ • y') y y ∂γ ∂γ -
        ouA u₀ * ∫ y', fderiv ℝ Φ (ouA u₀ • x + ouS u₀ • y') x ∂γ) u₀ := by
  haveI := hγ.1
  have hint1 : Integrable (fun w : B => ‖w‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hcd : ContDiff ℝ 5 Φ := hΦ.1
  have hd1 : Continuous (fderiv ℝ Φ) := hcd.continuous_fderiv (by norm_num)
  have hdiffΦ : Differentiable ℝ Φ := hcd.differentiable (by norm_num)
  set σ : ℝ := ouS (u₀ / 2) with hσ
  have hσpos : 0 < σ := ouS_pos (by linarith)
  let F : ℝ → B → ℝ := fun u y => Φ (ouA u • x + ouS u • y)
  let F' : ℝ → B → ℝ := fun u y =>
    fderiv ℝ Φ (ouA u • x + ouS u • y) ((-ouA u) • x + (ouA u ^ 2 / ouS u) • y)
  have hFcont : ∀ u, Continuous (F u) := fun u => by
    simp only [F]; exact hΦ.1.continuous.comp (by fun_prop)
  have hF'cont : ∀ u, Continuous (F' u) := fun u => by
    simp only [F']
    exact (hd1.comp (by fun_prop)).clm_apply (by fun_prop)
  set b : B → ℝ := fun y => cbSup Φ 1 * (‖x‖ + σ⁻¹ * ‖y‖) with hb
  have hbint : Integrable b γ := ((integrable_const ‖x‖).add (hint1.const_mul σ⁻¹)).const_mul _
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ) (F := F) (F' := F')
    (x₀ := u₀) (bound := b) (Metric.ball_mem_nhds u₀ (half_pos hu₀))
    (Filter.Eventually.of_forall fun u => (hFcont u).aestronglyMeasurable)
    (integrable_cont_bdd' hΦ _ _ x)
    (hF'cont u₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y u hu => by
      have hu' : u₀ / 2 < u := by
        have := (Metric.mem_ball.1 hu)
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.1]
      have hu0 : 0 < u := by linarith
      have hsu : σ ≤ ouS u := ouS_mono hu'.le
      have hspos : 0 < ouS u := lt_of_lt_of_le hσpos hsu
      have ha1 := ouA_le_one hu0.le
      have ha0 := ouA_pos u
      refine ((fderiv ℝ Φ _).le_opNorm _).trans ?_
      refine mul_le_mul (norm_fderiv_le_cbSup hΦ _) ?_ (norm_nonneg _) (cbSup_nonneg hΦ (by norm_num))
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha0,
        abs_of_pos (div_pos (pow_pos ha0 2) hspos)]
      refine add_le_add (by nlinarith [norm_nonneg x]) ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [div_le_iff₀ hspos]
      calc ouA u ^ 2 ≤ 1 := pow_le_one₀ ha0.le ha1
        _ = σ⁻¹ * σ := by field_simp
        _ ≤ σ⁻¹ * ouS u := mul_le_mul_of_nonneg_left hsu (inv_nonneg.2 hσpos.le))
    hbint
    (Filter.Eventually.of_forall fun y u hu => by
      have hu' : u₀ / 2 < u := by
        have := (Metric.mem_ball.1 hu)
        rw [Real.dist_eq, abs_lt] at this
        linarith [this.1]
      have hu0 : 0 < u := by linarith
      have h1 : HasDerivAt (fun u => ouA u • x + ouS u • y)
          ((-ouA u) • x + (ouA u ^ 2 / ouS u) • y) u :=
        ((hasDerivAt_ouA u).smul_const x).add ((hasDerivAt_ouS hu0).smul_const y)
      exact (hdiffΦ (ouA u • x + ouS u • y)).hasFDerivAt.comp_hasDerivAt u h1)
  have hmain := hD.2
  convert hmain using 1
  set a := ouA u₀ with ha
  set s := ouS u₀ with hs
  have hspos : 0 < s := ouS_pos hu₀
  have hibp := gaussian_ibp hγ (hcd.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 5))
    (fun w => norm_fderiv_le_cbSup hΦ w) (fun w => norm_fderiv2_le_cbSup hΦ w) (a • x) s
  have hcpt : Continuous fun y : B => a • x + s • y := by fun_prop
  have hI1 : Integrable (fun y : B => fderiv ℝ Φ (a • x + s • y) x) γ := by
    refine Integrable.of_bound (C := cbSup Φ 1 * ‖x‖) (hd1.comp hcpt |>.clm_apply continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    exact ((fderiv ℝ Φ _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_cbSup hΦ _) (norm_nonneg _))
  have hI3 : Integrable (fun y : B => fderiv ℝ Φ (a • x + s • y) y) γ := by
    refine ((hint1.const_mul (cbSup Φ 1))).mono' (hd1.comp hcpt |>.clm_apply continuous_id).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    exact ((fderiv ℝ Φ _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_cbSup hΦ _) (norm_nonneg _))
  have e : ∀ y : B, F' u₀ y = (-a) * fderiv ℝ Φ (a • x + s • y) x +
      (a ^ 2 / s) * fderiv ℝ Φ (a • x + s • y) y := by
    intro y
    simp only [F']
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp_rw [e]
  rw [integral_add (hI1.const_mul _) (hI3.const_mul _), integral_const_mul, integral_const_mul, hibp]
  field_simp
  ring


lemma iter_steinSolG_apply (hΦ : MemCb 5 Φ) (hγ1 : Integrable (fun y : B => ‖y‖) γ) (x : B)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ 5) (v : Fin j → B) :
    iteratedFDeriv ℝ j (steinSolG γ Φ) x v =
      -∫ p, ouA p.1 ^ j * iteratedFDeriv ℝ j Φ (ouA p.1 • x + ouS p.1 • p.2) v ∂(steinNu γ) := by
  rw [iteratedFDeriv_steinSolG hΦ hγ1 j hj x, neg_apply]
  congr 1
  have hint : Integrable (fun p => iteratedFDeriv ℝ j (steinG Φ p) x) (steinNu γ) :=
    (steinG_bound_int hΦ j hj1).mono' (steinG_meas hΦ j hj x)
      (Filter.Eventually.of_forall fun p => steinG_bound hΦ j hj1 hj p x)
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => B) ℝ v).integral_comp_comm hint
  simp only [ContinuousMultilinearMap.apply_apply] at this
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show (iteratedFDeriv ℝ j (steinG Φ p) x) v = _
  rw [iteratedFDeriv_steinG Φ hΦ.1 p j hj1 hj x]
  simp

lemma stein_D1_int (hΦ : MemCb 5 Φ) (x : B) :
    Integrable (fun p : ℝ × B => ouA p.1 * fderiv ℝ Φ (ouA p.1 • x + ouS p.1 • p.2) x) (steinNu γ) := by
  have hb : Integrable (fun p : ℝ × B => (cbSup Φ 1 * ‖x‖) * Real.exp (-(1 : ℝ) * p.1)) (steinNu γ) :=
    ((integrable_exp_neg_mul 1 one_pos).const_mul _).comp_fst γ
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hd1 : Continuous (fderiv ℝ Φ) := hΦ.1.continuous_fderiv (by norm_num)
    exact (continuous_ouA.comp continuous_fst).mul
      ((hd1.comp (by fun_prop)).clm_apply continuous_const) |>.aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (ouA_pos _)]
    have h1 : ‖fderiv ℝ Φ (ouA p.1 • x + ouS p.1 • p.2) x‖ ≤ cbSup Φ 1 * ‖x‖ :=
      ((fderiv ℝ Φ _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_cbSup hΦ _) (norm_nonneg _))
    have : ouA p.1 = Real.exp (-(1 : ℝ) * p.1) := by simp [ouA]
    calc ouA p.1 * ‖fderiv ℝ Φ (ouA p.1 • x + ouS p.1 • p.2) x‖
        ≤ ouA p.1 * (cbSup Φ 1 * ‖x‖) := mul_le_mul_of_nonneg_left h1 (ouA_pos _).le
      _ = _ := by rw [this]; ring


lemma stein_D2_int (hγ : IsCenteredGaussian γ) (hΦ : MemCb 5 Φ) (x : B) :
    Integrable (fun z : B × (ℝ × B) => ouA z.2.1 ^ 2 *
      fderiv ℝ (fderiv ℝ Φ) (ouA z.2.1 • x + ouS z.2.1 • z.2.2) z.1 z.1) (γ.prod (steinNu γ)) := by
  have hint2 := gaussian_sqnorm_integrable hγ
  have hg : Integrable (fun p : ℝ × B => cbSup Φ 2 * Real.exp (-(2 : ℝ) * p.1)) (steinNu γ) :=
    ((integrable_exp_neg_mul 2 two_pos).const_mul _).comp_fst γ
  have hb := hint2.mul_prod hg
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have hd1 : Continuous (fderiv ℝ Φ) := hΦ.1.continuous_fderiv (by norm_num)
    have hd2 : Continuous (fderiv ℝ (fderiv ℝ Φ)) := by
      have : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.1.fderiv_right (by norm_num)
      exact this.continuous_fderiv (by norm_num)
    exact ((continuous_ouA.comp (continuous_fst.comp continuous_snd)).pow 2).mul
      (((hd2.comp (by fun_prop)).clm_apply continuous_fst).clm_apply continuous_fst)
      |>.aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos (ouA_pos _) 2)]
    have h1 : ‖fderiv ℝ (fderiv ℝ Φ) (ouA z.2.1 • x + ouS z.2.1 • z.2.2) z.1 z.1‖ ≤
        cbSup Φ 2 * ‖z.1‖ ^ 2 := by
      refine ((fderiv ℝ (fderiv ℝ Φ) _ z.1).le_opNorm _).trans ?_
      have : ‖fderiv ℝ (fderiv ℝ Φ) (ouA z.2.1 • x + ouS z.2.1 • z.2.2) z.1‖ ≤
          cbSup Φ 2 * ‖z.1‖ :=
        ((fderiv ℝ (fderiv ℝ Φ) _).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv2_le_cbSup hΦ _) (norm_nonneg _))
      calc _ ≤ cbSup Φ 2 * ‖z.1‖ * ‖z.1‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := by ring
    have e : ouA z.2.1 ^ 2 = Real.exp (-(2 : ℝ) * z.2.1) := by rw [ouA_sq]
    calc ouA z.2.1 ^ 2 * ‖fderiv ℝ (fderiv ℝ Φ) (ouA z.2.1 • x + ouS z.2.1 • z.2.2) z.1 z.1‖
        ≤ ouA z.2.1 ^ 2 * (cbSup Φ 2 * ‖z.1‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (pow_pos (ouA_pos _) 2).le
      _ = _ := by rw [e]; ring


lemma stein_T_cont (hΦ : MemCb 5 Φ) (x : B) :
    Continuous fun u : ℝ => ∫ y, Φ (ouA u • x + ouS u • y) ∂γ := by
  refine continuous_of_dominated (bound := fun _ => cbSup Φ 0) (fun u => ?_) (fun u => ?_)
    (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
  · exact (integrable_cont_bdd' hΦ _ _ x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_le_cbSup hΦ _
  · exact hΦ.1.continuous.comp (by fun_prop)

lemma stein_T_zero (x : B) : ∫ y, Φ (ouA 0 • x + ouS 0 • y) ∂γ = Φ x := by
  have h1 : ouA 0 = 1 := by simp [ouA]
  have h2 : ouS 0 = 0 := by simp [ouS]
  simp [h1, h2]

lemma stein_T_tendsto (hΦ : MemCb 5 Φ) (x : B) :
    Tendsto (fun u : ℝ => ∫ y, Φ (ouA u • x + ouS u • y) ∂γ) atTop (𝓝 (∫ y, Φ y ∂γ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => cbSup Φ 0) ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun u => (integrable_cont_bdd' hΦ _ _ x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u => Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact abs_le_cbSup hΦ _
  · refine Filter.Eventually.of_forall fun y => ?_
    have hA : Tendsto ouA atTop (𝓝 0) := by
      unfold ouA
      exact Real.tendsto_exp_neg_atTop_nhds_zero
    have hS : Tendsto ouS atTop (𝓝 1) := by
      unfold ouS
      have : Tendsto (fun u : ℝ => Real.exp (-2 * u)) atTop (𝓝 0) := by
        exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2:ℝ) < 0))
      have h := (this.const_sub 1).sqrt
      simpa using h
    have h := (hΦ.1.continuous.tendsto ((0 : ℝ) • x + (1 : ℝ) • y)).comp
      ((hA.smul_const x).add (hS.smul_const y))
    simpa [Function.comp_def] using h


lemma stein_core (hγ : IsCenteredGaussian γ) (hΦ : MemCb 5 Φ) (x : B) :
    ∫ y, iteratedFDeriv ℝ 2 (steinSolG γ Φ) x ![y, y] ∂γ - fderiv ℝ (steinSolG γ Φ) x x =
      Φ x - ∫ y, Φ y ∂γ := by
  haveI := hγ.1
  have hγ1 : Integrable (fun y : B => ‖y‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  set f := steinSolG γ Φ with hf
  set μ0 : Measure ℝ := volume.restrict (Set.Ioi (0:ℝ)) with hμ0
  -- first derivative
  have hDx : fderiv ℝ f x x =
      -∫ p, ouA p.1 * fderiv ℝ Φ (ouA p.1 • x + ouS p.1 • p.2) x ∂(steinNu γ) := by
    have := iter_steinSolG_apply hΦ hγ1 x 1 le_rfl (by norm_num) ![x]
    simpa using this
  have hD2 : ∀ y : B, iteratedFDeriv ℝ 2 f x ![y, y] =
      -∫ p, ouA p.1 ^ 2 * fderiv ℝ (fderiv ℝ Φ) (ouA p.1 • x + ouS p.1 • p.2) y y ∂(steinNu γ) := by
    intro y
    have := iter_steinSolG_apply hΦ hγ1 x 2 (by norm_num) (by norm_num) ![y, y]
    simpa [iteratedFDeriv_two_apply] using this
  have hint2 := stein_D2_int hγ hΦ x
  have hint1 := stein_D1_int (γ := γ) hΦ x
  -- the second-derivative term
  have hP2 : ∫ y, iteratedFDeriv ℝ 2 f x ![y, y] ∂γ =
      -∫ u in Set.Ioi (0:ℝ), ouA u ^ 2 * ∫ y', ∫ y,
        fderiv ℝ (fderiv ℝ Φ) (ouA u • x + ouS u • y') y y ∂γ ∂γ := by
    simp_rw [hD2]
    rw [integral_neg, integral_integral_swap hint2]
    congr 1
    have hI : Integrable (fun p : ℝ × B => ∫ y, ouA p.1 ^ 2 *
        fderiv ℝ (fderiv ℝ Φ) (ouA p.1 • x + ouS p.1 • p.2) y y ∂γ) (steinNu γ) :=
      hint2.integral_prod_right
    rw [integral_prod _ hI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
    simp only
    rw [integral_const_mul]
  have hP1 : fderiv ℝ f x x =
      -∫ u in Set.Ioi (0:ℝ), ouA u * ∫ y', fderiv ℝ Φ (ouA u • x + ouS u • y') x ∂γ := by
    rw [hDx]
    congr 1
    rw [integral_prod _ hint1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [integral_const_mul]
  -- integrability in u
  have hIU2 : Integrable (fun u : ℝ => ouA u ^ 2 * ∫ y', ∫ y,
      fderiv ℝ (fderiv ℝ Φ) (ouA u • x + ouS u • y') y y ∂γ ∂γ) μ0 := by
    have h1 : Integrable (fun p : ℝ × B => ∫ y, ouA p.1 ^ 2 *
        fderiv ℝ (fderiv ℝ Φ) (ouA p.1 • x + ouS p.1 • p.2) y y ∂γ) (steinNu γ) :=
      hint2.integral_prod_right
    have h2 := h1.integral_prod_left
    refine h2.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
    simp only
    rw [integral_const_mul]
  have hIU1 : Integrable (fun u : ℝ => ouA u * ∫ y', fderiv ℝ Φ (ouA u • x + ouS u • y') x ∂γ) μ0 := by
    have h2 := hint1.integral_prod_left
    refine h2.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [integral_const_mul]
  -- FTC
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0:ℝ))
    (f := fun u : ℝ => ∫ y, Φ (ouA u • x + ouS u • y) ∂γ)
    (f' := fun u => ouA u ^ 2 * ∫ y', ∫ y,
        fderiv ℝ (fderiv ℝ Φ) (ouA u • x + ouS u • y') y y ∂γ ∂γ -
      ouA u * ∫ y', fderiv ℝ Φ (ouA u • x + ouS u • y') x ∂γ)
    (stein_T_cont hΦ x).continuousWithinAt
    (fun u hu => hasDerivAt_stein_T hγ hΦ x hu)
    (hIU2.sub hIU1) (stein_T_tendsto hΦ x)
  rw [stein_T_zero, integral_sub hIU2 hIU1] at hFTC
  rw [hP2, hP1]
  linarith

end GaussIBP

section Stein

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Lemma 7.2 `M:F:lem:Stein` (lines 7774-7789), finiteness and derivative bounds
`F:eq:Stein-bounds`: for a centered (Radon) Gaussian `G` on a separable Banach space and
`Φ ∈ C_b^5(B)`, the Stein integral converges for each `x`, `f` is `C^5` with
`‖D^j f‖_∞ ≤ j⁻¹ ‖D^jΦ‖_∞` for `1 ≤ j ≤ 5`. -/
theorem stein_bounds (G : Ω → B) (hG : AEMeasurable G P) (hGauss : IsCenteredGaussian (law P G))
    (Φ : B → ℝ) (hΦ : MemCb 5 Φ) :
    (∀ x, IntegrableOn (fun u : ℝ =>
        ∫ ω, Φ (Real.exp (-u) • x + Real.sqrt (1 - Real.exp (-2 * u)) • G ω) ∂P -
          ∫ ω, Φ (G ω) ∂P) (Set.Ioi 0)) ∧
    ContDiff ℝ 5 (steinSolution P G Φ) ∧
    ∀ j, 1 ≤ j → j ≤ 5 → ∀ x,
      ‖iteratedFDeriv ℝ j (steinSolution P G Φ) x‖ ≤
        (j : ℝ)⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ j Φ y‖ :=
  stein_bounds' P G hG hGauss Φ hΦ

/-- Lemma 7.2, the Stein equation `F:eq:Stein-eq`:
`⟨D²f(x), C_G⟩ - Df(x)[x] = Φ(x) - E[Φ(G)]`. -/
theorem stein_equation (G : Ω → B) (hG : AEMeasurable G P) (hGauss : IsCenteredGaussian (law P G))
    (Φ : B → ℝ) (hΦ : MemCb 5 Φ) (x : B) :
    covarianceContraction P G (steinSolution P G Φ) x - fderiv ℝ (steinSolution P G Φ) x x =
      Φ x - ∫ ω, Φ (G ω) ∂P := by
  haveI := hGauss.1
  haveI : IsProbabilityMeasure (P.map G) := (Measure.isProbabilityMeasure_map_iff hG).2 inferInstance
  have hf := steinSolution_eq_steinSolG P G hG hΦ
  have hcore := stein_core (γ := P.map G) hGauss hΦ x
  have hfd : ContDiff ℝ 5 (steinSolG (P.map G) Φ) :=
    contDiff_steinSolG hΦ (gaussian_norm_integrable P G hGauss)
  have c : Continuous fun y : B => iteratedFDeriv ℝ 2 (steinSolG (P.map G) Φ) x ![y, y] :=
    (iteratedFDeriv ℝ 2 (steinSolG (P.map G) Φ) x).cont.comp (by fun_prop)
  have h1 := integral_map hG c.aestronglyMeasurable
  have h2 : ∫ ω, Φ (G ω) ∂P = ∫ y, Φ y ∂(P.map G) := by
    rw [integral_map hG hΦ.1.continuous.aestronglyMeasurable]
  rw [hf]
  unfold covarianceContraction
  rw [h1] at hcore
  rw [h2]
  exact hcore

/-- Lemma 7.2, third-derivative identity `F:eq:Stein-third`:
`E[D³f(G)] = -⅓ E[D³Φ(G)]` (as continuous trilinear maps). -/
theorem stein_third_derivative (G : Ω → B) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (Φ : B → ℝ) (hΦ : MemCb 5 Φ) (v : Fin 3 → B) :
    ∫ ω, iteratedFDeriv ℝ 3 (steinSolution P G Φ) (G ω) v ∂P =
      -(1 / 3) * ∫ ω, iteratedFDeriv ℝ 3 Φ (G ω) v ∂P :=
  stein_third' P G hG hGauss hΦ v

end Stein

/-! ### Gaussian quadratic chaos (Proposition 7.18, first display; work package CHAOS-01) -/

section Chaos

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- i.i.d. standard Gaussian coordinates `G_i`. -/
def IsStdGaussianSeq (G : ℕ → Ω → ℝ) : Prop :=
  ProbabilityTheory.iIndepFun G P ∧ ∀ i, law P (G i) = ProbabilityTheory.gaussianReal 0 1

/-- Symmetric Hilbert–Schmidt matrix: `A_ij = A_ji`, `∑ A_ij² < ∞`. -/
def IsSymmetricHS (A : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧ Summable fun p : ℕ × ℕ => A p.1 p.2 ^ 2

/-- Hilbert–Schmidt norm `‖A‖_HS`. -/
def hsNorm (A : ℕ → ℕ → ℝ) : ℝ := Real.sqrt (∑' p : ℕ × ℕ, A p.1 p.2 ^ 2)

/-- The finite sections `Q_n(A) = ½ ∑_{i,j<n} A_ij (G_i G_j - δ_ij)`. -/
def chaosSection (A : ℕ → ℕ → ℝ) (G : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    A i j * (G i ω * G j ω - if i = j then 1 else 0)

/-- `Q_n → Q` in `L²(P)`. -/
def TendstoL2 (Qn : ℕ → Ω → ℝ) (Q : Ω → ℝ) : Prop :=
  AEStronglyMeasurable Q P ∧
    Tendsto (fun n => ∫⁻ ω, ‖Qn n ω - Q ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)

open Classical in
/-- `Q(A)`, the centered second Gaussian chaos of `A`: the `L²` limit of the sections
(junk `0` if no limit exists; `chaos_tendsto` shows it exists for symmetric HS `A`). -/
def chaos (A : ℕ → ℕ → ℝ) (G : ℕ → Ω → ℝ) : Ω → ℝ :=
  if h : ∃ Q : Ω → ℝ, TendstoL2 P (chaosSection A G) Q then h.choose else 0

end Chaos

section ChaosAux
open ProbabilityTheory Matrix

lemma frob_eig (N : ℕ) (a : Matrix (Fin N) (Fin N) ℝ) (ha : a.IsHermitian) :
    ∑ k, ha.eigenvalues k ^ 2 = ∑ i, ∑ j, a i j ^ 2 := by
  have h1 : ∑ i, ∑ j, a i j ^ 2 = (a * a).trace := by
    have : a * a = aᴴ * a := by rw [ha.eq]
    rw [this, Matrix.trace]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, sq]
    rw [Finset.sum_comm]
  rw [h1]
  have hs := ha.spectral_theorem
  set U : Matrix (Fin N) (Fin N) ℝ := (ha.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)
  set D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (RCLike.ofReal ∘ ha.eigenvalues)
  have hU : star U * U = 1 := Unitary.coe_star_mul_self ha.eigenvectorUnitary
  have e : a = U * D * star U := by
    conv_lhs => rw [hs]
    rfl
  have : a * a = U * (D * D) * star U := by
    calc a * a = (U * D * star U) * (U * D * star U) := by rw [← e]
      _ = U * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
      _ = U * (D * D) * star U := by rw [hU]; simp [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.trace]
  simp [D, Matrix.diagonal_mul_diagonal, sq]


lemma quad_eig (N : ℕ) (a : Matrix (Fin N) (Fin N) ℝ) (ha : a.IsHermitian) :
    ∃ (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) (l : Fin N → ℝ),
      (∀ x : Fin N → ℝ, x ⬝ᵥ (a *ᵥ x) =
        ∑ k, l k * (inner ℝ (b k) (WithLp.toLp 2 x)) ^ 2) ∧
      (∑ k, l k = a.trace) ∧ (∑ k, l k ^ 2 = ∑ i, ∑ j, a i j ^ 2) := by
  refine ⟨ha.eigenvectorBasis, ha.eigenvalues, ?_, ?_, ?_⟩
  · intro x
    set b := ha.eigenvectorBasis
    have hx : x = ∑ k, (inner ℝ (b k) (WithLp.toLp 2 x)) • ⇑(b k) := by
      have := b.sum_repr' (WithLp.toLp 2 x)
      have h2 := congrArg WithLp.ofLp this
      simpa using h2.symm
    have key : ∀ k, x ⬝ᵥ ⇑(b k) = inner ℝ (b k) (WithLp.toLp 2 x) := by
      intro k
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct_comm]
    have h1 : a *ᵥ x = ∑ k, (inner ℝ (b k) (WithLp.toLp 2 x) * ha.eigenvalues k) • ⇑(b k) := by
      conv_lhs => rw [hx]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := ha.mulVec_eigenvectorBasis k
      simp only [WithLp.ofLp] at this ⊢
      rw [this, smul_smul]
    rw [h1]
    simp only [dotProduct_sum, dotProduct_smul, key, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  · exact_mod_cast ha.trace_eq_sum_eigenvalues.symm
  · exact frob_eig N a ha




lemma map_pi_coord_eq (N : ℕ) (b : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N))) :
    (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
      (fun x : Fin N → ℝ => fun k => inner ℝ (b k) (WithLp.toLp 2 x)) =
    Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
  set γ := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
  set φ : EuclideanSpace ℝ (Fin N) → (Fin N → ℝ) := fun v k => inner ℝ (b k) v with hφ
  have hφm : Measurable φ := by
    refine Measurable.of_eval fun k => ?_
    exact (continuous_const.inner continuous_id).measurable
  have h1 := map_pi_eq_stdGaussian (ι := Fin N)
  have h2 := stdGaussian_eq_map_pi_orthonormalBasis (E := EuclideanSpace ℝ (Fin N)) b
  have e1 : (fun x : Fin N → ℝ => fun k => inner ℝ (b k) (WithLp.toLp 2 x)) = φ ∘ (WithLp.toLp 2) := rfl
  rw [e1, ← Measure.map_map hφm (by fun_prop), h1, h2, Measure.map_map hφm (by fun_prop)]
  have : φ ∘ (fun x : Fin N → ℝ => ∑ i, x i • b i) = id := by
    ext x k
    simp [hφ, inner_sum, inner_smul_right, b.inner_eq_ite]
  rw [this, Measure.map_id]


lemma pi_integral_eval (N : ℕ) (f : ℝ → ℝ) (hf : Continuous f) (k : Fin N) :
    ∫ y, f (y k) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      ∫ x, f x ∂(gaussianReal 0 1) := by
  have h := (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) k).map_eq
  conv_rhs => rw [← h]
  exact (integral_map (measurable_pi_apply k).aemeasurable hf.aestronglyMeasurable).symm

lemma pi_integral_cross (N : ℕ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (k l : Fin N) (hkl : k ≠ l) :
    ∫ y, f (y k) * g (y l) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      (∫ x, f x ∂(gaussianReal 0 1)) * ∫ x, g x ∂(gaussianReal 0 1) := by
  have hind := iIndepFun_pi (μ := fun _ : Fin N => gaussianReal 0 1) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun hkl)
  have := h2.integral_fun_comp_mul_comp (f := f) (g := g)
    (measurable_pi_apply k).aemeasurable (measurable_pi_apply l).aemeasurable (by simpa using hf.aestronglyMeasurable) (by simpa using hg.aestronglyMeasurable)
  rw [← pi_integral_eval N f hf k, ← pi_integral_eval N g hg l]
  exact this


lemma gauss_integrable_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) n).integrable_norm_pow'
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [norm_pow] using this

lemma gauss_sq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa using h

lemma gauss_one : ∫ x : ℝ, x ∂(gaussianReal 0 1) = 0 := by simp

lemma gauss_sqm1 : ∫ x : ℝ, (x ^ 2 - 1) ∂(gaussianReal 0 1) = 0 := by
  rw [integral_sub (gauss_integrable_pow 2) (integrable_const _)]
  simp [gauss_sq]


/-- `v = E (g² - 1)²`. -/
def vGauss : ℝ := ∫ x : ℝ, (x ^ 2 - 1) ^ 2 ∂(gaussianReal 0 1)

lemma gauss_integrable_sqm1_sq : Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 2) (gaussianReal 0 1) := by
  have h : (fun x : ℝ => (x ^ 2 - 1) ^ 2) = fun x => x ^ 4 - 2 * x ^ 2 + 1 := by ext x; ring
  rw [h]
  exact ((gauss_integrable_pow 4).sub ((gauss_integrable_pow 2).const_mul 2)).add (integrable_const _)

lemma pi_integrable_eval (N : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (hfi : Integrable f (gaussianReal 0 1)) (k : Fin N) :
    Integrable (fun y : Fin N → ℝ => f (y k)) (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := by
  have h := (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) k)
  exact h.integrable_comp_of_integrable hfi

lemma pi_sqm1_orth (N : ℕ) (k m : Fin N) :
    ∫ y, (y k ^ 2 - 1) * (y m ^ 2 - 1) ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      if k = m then vGauss else 0 := by
  by_cases h : k = m
  · subst h
    simp only [ite_true, vGauss]
    rw [← pi_integral_eval N (fun x => (x ^ 2 - 1) ^ 2) (by fun_prop) k]
    congr 1; ext y; ring
  · simp only [h, ite_false]
    rw [pi_integral_cross N (fun x => x ^ 2 - 1) (fun x => x ^ 2 - 1) (by fun_prop) (by fun_prop) k m h,
      gauss_sqm1]
    simp

lemma pi_sqm1_integrable (N : ℕ) (k m : Fin N) :
    Integrable (fun y : Fin N → ℝ => (y k ^ 2 - 1) * (y m ^ 2 - 1))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := by
  have hi : ∀ k : Fin N, Integrable (fun y : Fin N → ℝ => (y k ^ 2 - 1) ^ 2)
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := fun k =>
    pi_integrable_eval N (fun x => (x ^ 2 - 1) ^ 2) (by fun_prop) gauss_integrable_sqm1_sq k
  have hmeas : AEStronglyMeasurable (fun y : Fin N → ℝ => (y k ^ 2 - 1) * (y m ^ 2 - 1))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) := by fun_prop
  refine Integrable.mono' (((hi k).add (hi m)).const_mul (1/2)) hmeas (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_mul]
  nlinarith [sq_nonneg (|y k ^ 2 - 1| - |y m ^ 2 - 1|), sq_abs (y k ^ 2 - 1), sq_abs (y m ^ 2 - 1),
    abs_nonneg (y k ^ 2 - 1), abs_nonneg (y m ^ 2 - 1)]


lemma quad_L2 (N : ℕ) (a : Matrix (Fin N) (Fin N) ℝ) (ha : a.IsHermitian) :
    ∫ z, (z ⬝ᵥ (a *ᵥ z) - a.trace) ^ 2 ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1)) =
      vGauss * ∑ i, ∑ j, a i j ^ 2 := by
  obtain ⟨b, l, h1, h2, h3⟩ := quad_eig N a ha
  set γ := Measure.pi (fun _ : Fin N => gaussianReal 0 1) with hγ
  set φ : (Fin N → ℝ) → (Fin N → ℝ) := fun x k => inner ℝ (b k) (WithLp.toLp 2 x) with hφ
  have hφm : Measurable φ := by
    refine Measurable.of_eval fun k => ?_
    exact (continuous_const.inner (by fun_prop : Continuous fun x : Fin N → ℝ => WithLp.toLp 2 x)).measurable
  set H : (Fin N → ℝ) → ℝ := fun y => (∑ k, l k * (y k ^ 2 - 1)) ^ 2 with hH
  have hint : ∀ z : Fin N → ℝ, (z ⬝ᵥ (a *ᵥ z) - a.trace) ^ 2 = H (φ z) := by
    intro z
    simp only [hH, hφ]
    rw [h1 z, ← h2]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hint]
  have hHm : AEStronglyMeasurable H γ := by
    have : Continuous H := by simp only [hH]; fun_prop
    exact this.aestronglyMeasurable
  have hmap := map_pi_coord_eq N b
  have : ∫ z, H (φ z) ∂γ = ∫ y, H y ∂(γ.map φ) := (integral_map hφm.aemeasurable (by
    rw [show γ.map φ = γ from hmap]; exact hHm)).symm
  rw [this, show γ.map φ = γ from hmap]
  have hexp : ∀ y : Fin N → ℝ, H y = ∑ k, ∑ m, (l k * l m) * ((y k ^ 2 - 1) * (y m ^ 2 - 1)) := by
    intro y
    simp only [hH, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun m _ => (pi_sqm1_integrable N k m).const_mul _)]
  have : ∀ k ∈ (Finset.univ : Finset (Fin N)), ∫ y, ∑ m, (l k * l m) * ((y k ^ 2 - 1) * (y m ^ 2 - 1)) ∂γ
      = l k ^ 2 * vGauss := by
    intro k _
    rw [integral_finsetSum _ (fun m _ => (pi_sqm1_integrable N k m).const_mul _)]
    simp_rw [integral_const_mul, pi_sqm1_orth]
    simp [sq, mul_comm, mul_assoc, mul_left_comm]
  rw [Finset.sum_congr rfl this, ← h3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma IsStdGaussianSeq.aemeasurable {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (i : ℕ) :
    AEMeasurable (G i) P := by
  by_contra h
  have := hG.2 i
  rw [law, Measure.map_of_not_aemeasurable_of_ne_zero h (IsProbabilityMeasure.ne_zero P)] at this
  have h2 : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have h1 : (gaussianReal 0 1) {Classical.ofNonempty} = 1 := by rw [← this]; simp
  rw [measure_singleton] at h1
  simp at h1

lemma law_vec {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (N : ℕ) :
    P.map (fun ω (i : Fin N) => G i ω) = Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
  have hind : iIndepFun (fun i : Fin N => G i) P := hG.1.precomp Fin.val_injective
  have := (iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin N => hG.aemeasurable i)).1 hind
  rw [this]
  congr 1
  ext i : 1
  exact hG.2 i


/-- The finite quadratic form `∑_{i,j<N} c_ij (G_i G_j - δ_ij)`. -/
def quadSum (c : ℕ → ℕ → ℝ) (G : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j * (G i ω * G j ω - if i = j then 1 else 0)

lemma quadSum_eq (c : ℕ → ℕ → ℝ) (G : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    quadSum c G N ω =
      (fun i : Fin N => G i ω) ⬝ᵥ ((Matrix.of fun i j : Fin N => c i j) *ᵥ (fun i : Fin N => G i ω))
        - (Matrix.of fun i j : Fin N => c i j).trace := by
  unfold quadSum
  rw [Finset.sum_range]
  simp only [Finset.sum_range, Matrix.trace, Matrix.diag, Matrix.of_apply, dotProduct, Matrix.mulVec]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  have : ∀ i : Fin N, ∑ j : Fin N, (if (i : ℕ) = (j : ℕ) then c i j else 0) = c i i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [if_neg (fun h => hj (Fin.ext h.symm))]
    · simp
  simp only [this]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma quadSum_L2 {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (c : ℕ → ℕ → ℝ)
    (hc : ∀ i j, c i j = c j i) (N : ℕ) :
    ∫ ω, quadSum c G N ω ^ 2 ∂P =
      vGauss * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j ^ 2 := by
  set a : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j : Fin N => c i j with ha
  have hH : a.IsHermitian := by
    ext i j
    simp [ha, Matrix.conjTranspose_apply, hc]
  have hZ : AEMeasurable (fun ω (i : Fin N) => G i ω) P :=
    AEMeasurable.of_eval fun i => hG.aemeasurable i
  have hF : Continuous (fun z : Fin N → ℝ => (z ⬝ᵥ (a *ᵥ z) - a.trace) ^ 2) := by
    unfold dotProduct Matrix.mulVec; fun_prop
  have h1 : ∫ ω, quadSum c G N ω ^ 2 ∂P =
      ∫ z, (z ⬝ᵥ (a *ᵥ z) - a.trace) ^ 2 ∂(P.map (fun ω (i : Fin N) => G i ω)) := by
    rw [integral_map hZ hF.aestronglyMeasurable]
    simp_rw [quadSum_eq c G N]
    rfl
  rw [h1, law_vec hG N, quad_L2 N a hH, Finset.sum_range]
  congr 1
  simp only [ha, Matrix.of_apply, Finset.sum_range]


lemma Lp2_norm_sq (g : Lp ℝ 2 P) : ‖g‖ ^ 2 = ∫ ω, (g ω) ^ 2 ∂P := by
  have h := real_inner_self_eq_norm_sq g
  rw [← h, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp [sq]

lemma gauss_pow_memLp {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (i : ℕ) (n : ℕ) :
    Integrable (fun ω => G i ω ^ n) P := by
  have h := gauss_integrable_pow n
  rw [← hG.2 i] at h
  exact (integrable_map_measure (continuous_pow n).aestronglyMeasurable (hG.aemeasurable i)).1 h

lemma memLp_term {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (i j : ℕ) :
    MemLp (fun ω => G i ω * G j ω - if i = j then 1 else 0) 2 P := by
  have hm : AEStronglyMeasurable (fun ω => G i ω * G j ω) P :=
    ((hG.aemeasurable i).mul (hG.aemeasurable j)).aestronglyMeasurable
  have h1 : MemLp (fun ω => G i ω * G j ω) 2 P := by
    rw [memLp_two_iff_integrable_sq hm]
    refine Integrable.mono' (((gauss_pow_memLp hG i 4).add (gauss_pow_memLp hG j 4)).const_mul (1/2))
      (hm.pow 2) (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (G i ω ^ 2 - G j ω ^ 2)]
  exact h1.sub (memLp_const _)

lemma memLp_quadSum {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (c : ℕ → ℕ → ℝ) (N : ℕ) :
    MemLp (quadSum c G N) 2 P := by
  unfold quadSum
  have : (fun ω => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      c i j * (G i ω * G j ω - if i = j then 1 else 0)) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        fun ω => c i j * (G i ω * G j ω - if i = j then 1 else 0) := by
    ext ω; simp
  rw [this]
  refine memLp_finsetSum' _ fun i _ => memLp_finsetSum' _ fun j _ => ?_
  exact (memLp_term hG i j).const_mul _


lemma sum_range_sq_ite (f : ℕ → ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (if i < m ∧ j < m then f i j else 0) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, f i j := by
  have h1 : ∀ i, i < m → ∑ j ∈ Finset.range n, (if i < m ∧ j < m then f i j else 0) =
      ∑ j ∈ Finset.range m, f i j := by
    intro i hi
    rw [← Finset.sum_subset (Finset.range_mono hmn) (fun j _ hj => by
      simp only [Finset.mem_range, not_lt] at hj; simp [not_lt.2 hj])]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    simp [hi, hj]
  rw [← Finset.sum_subset (Finset.range_mono hmn) (fun i _ hi => by
    simp only [Finset.mem_range, not_lt] at hi
    refine Finset.sum_eq_zero fun j _ => by simp [not_lt.2 hi])]
  refine Finset.sum_congr rfl fun i hi => h1 i (Finset.mem_range.1 hi)

/-- partial Hilbert–Schmidt sums over squares -/
def hsPartial (A : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j ^ 2

lemma section_sub (A : ℕ → ℕ → ℝ) (G : ℕ → Ω → ℝ) (m n : ℕ) (hmn : m ≤ n) (ω : Ω) :
    chaosSection A G n ω - chaosSection A G m ω =
      (1 / 2) * quadSum (fun i j => if i < m ∧ j < m then 0 else A i j) G n ω := by
  unfold chaosSection quadSum
  have h := sum_range_sq_ite (fun i j => A i j * (G i ω * G j ω - if i = j then 1 else 0)) m n hmn
  have e : ∀ i j : ℕ, (if i < m ∧ j < m then (0:ℝ) else A i j) * (G i ω * G j ω - if i = j then 1 else 0)
      = A i j * (G i ω * G j ω - if i = j then 1 else 0) -
        (if i < m ∧ j < m then A i j * (G i ω * G j ω - if i = j then 1 else 0) else 0) := by
    intro i j; split_ifs <;> simp
  simp_rw [e, Finset.sum_sub_distrib, h]
  ring

lemma section_L2_diff {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (A : ℕ → ℕ → ℝ)
    (hA : ∀ i j, A i j = A j i) (m n : ℕ) (hmn : m ≤ n) :
    ∫ ω, (chaosSection A G n ω - chaosSection A G m ω) ^ 2 ∂P =
      vGauss / 4 * (hsPartial A n - hsPartial A m) := by
  have hc : ∀ i j, (fun i j => if i < m ∧ j < m then (0:ℝ) else A i j) i j =
      (fun i j => if i < m ∧ j < m then (0:ℝ) else A i j) j i := by
    intro i j; simp only [hA i j, and_comm]
  have h := quadSum_L2 hG (fun i j => if i < m ∧ j < m then 0 else A i j) hc n
  simp_rw [section_sub A G m n hmn, mul_pow]
  rw [integral_const_mul, h]
  have e : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      ((fun i j => if i < m ∧ j < m then (0:ℝ) else A i j) i j) ^ 2 = hsPartial A n - hsPartial A m := by
    have h2 := sum_range_sq_ite (fun i j => A i j ^ 2) m n hmn
    have e2 : ∀ i j : ℕ, ((fun i j => if i < m ∧ j < m then (0:ℝ) else A i j) i j) ^ 2 =
        A i j ^ 2 - (if i < m ∧ j < m then A i j ^ 2 else 0) := by
      intro i j; simp only; split_ifs <;> simp
    simp_rw [e2, Finset.sum_sub_distrib, h2]
    rfl
  rw [e]
  ring


lemma hsPartial_tendsto (A : ℕ → ℕ → ℝ) (hs : Summable fun p : ℕ × ℕ => A p.1 p.2 ^ 2) :
    Tendsto (hsPartial A) atTop (𝓝 (∑' p : ℕ × ℕ, A p.1 p.2 ^ 2)) := by
  have h := hs.hasSum
  have hsq : Tendsto (fun n : ℕ => Finset.range n ×ˢ Finset.range n) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro s
    refine ⟨s.sup Prod.fst + s.sup Prod.snd + 1, fun n hn => ?_⟩
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range]
    have h1 : p.1 ≤ s.sup Prod.fst := Finset.le_sup (f := Prod.fst) hp
    have h2 : p.2 ≤ s.sup Prod.snd := Finset.le_sup (f := Prod.snd) hp
    constructor <;> omega
  have := h.comp hsq
  convert this using 1
  ext n
  simp [hsPartial, Function.comp, Finset.sum_product]

lemma section_L2_le {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (A : ℕ → ℕ → ℝ)
    (hA : ∀ i j, A i j = A j i) (m n : ℕ) :
    ∫ ω, (chaosSection A G n ω - chaosSection A G m ω) ^ 2 ∂P ≤
      vGauss / 4 * |hsPartial A n - hsPartial A m| := by
  have hv : 0 ≤ vGauss := integral_nonneg fun x => sq_nonneg _
  rcases le_total m n with h | h
  · rw [section_L2_diff hG A hA m n h]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  · have e : ∫ ω, (chaosSection A G n ω - chaosSection A G m ω) ^ 2 ∂P =
        ∫ ω, (chaosSection A G m ω - chaosSection A G n ω) ^ 2 ∂P := by
      congr 1; ext ω; ring
    rw [e, section_L2_diff hG A hA n m h, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)

lemma exists_chaos_limit {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (A : ℕ → ℕ → ℝ)
    (hA : IsSymmetricHS A) :
    ∃ Q : Ω → ℝ, MemLp Q 2 P ∧
      Tendsto (fun n => ∫ ω, (chaosSection A G n ω - Q ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hmem : ∀ n, MemLp (chaosSection A G n) 2 P := fun n => (memLp_quadSum hG A n).const_mul (1/2)
  set q : ℕ → Lp ℝ 2 P := fun n => (hmem n).toLp (chaosSection A G n) with hq
  have hv : 0 ≤ vGauss := integral_nonneg fun x => sq_nonneg _
  have hdist : ∀ m n, dist (q n) (q m) ^ 2 = ∫ ω, (chaosSection A G n ω - chaosSection A G m ω) ^ 2 ∂P := by
    intro m n
    rw [dist_eq_norm, Lp2_norm_sq]
    refine integral_congr_ae ?_
    have h1 := Lp.coeFn_sub (q n) (q m)
    have h2 := (hmem n).coeFn_toLp
    have h3 := (hmem m).coeFn_toLp
    filter_upwards [h1, h2, h3] with ω h1 h2 h3
    simp only [hq] at h1 h2 h3 ⊢
    rw [h1]; simp only [Pi.sub_apply]; rw [h2, h3]
  have hcau : CauchySeq q := by
    have hconv := (hsPartial_tendsto A hA.2).cauchySeq
    rw [Metric.cauchySeq_iff] at hconv ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hconv (ε ^ 2 / (vGauss / 4 + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : dist (q m) (q n) ^ 2 < ε ^ 2 := by
      rw [hdist n m]
      have := hN m hm n hn
      rw [Real.dist_eq] at this
      calc _ ≤ vGauss / 4 * |hsPartial A m - hsPartial A n| := section_L2_le hG A hA.1 n m
        _ ≤ vGauss / 4 * (ε ^ 2 / (vGauss / 4 + 1)) :=
            mul_le_mul_of_nonneg_left this.le (by positivity)
        _ < ε ^ 2 := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith [sq_nonneg ε, hε]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hb
  obtain ⟨qlim, hqlim⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨qlim, Lp.memLp qlim, ?_⟩
  have hd : Tendsto (fun n => dist (q n) qlim ^ 2) atTop (𝓝 0) := by
    have := (tendsto_iff_dist_tendsto_zero.1 hqlim).pow 2
    simpa using this
  have hE : ∀ n, dist (q n) qlim ^ 2 = ∫ ω, (chaosSection A G n ω - qlim ω) ^ 2 ∂P := by
    intro n
    rw [dist_eq_norm, Lp2_norm_sq]
    refine integral_congr_ae ?_
    have h1 := Lp.coeFn_sub (q n) qlim
    have h2 := (hmem n).coeFn_toLp
    filter_upwards [h1, h2] with ω h1 h2
    simp only [hq] at h1 h2 ⊢
    rw [h1]; simp only [Pi.sub_apply]; rw [h2]
  simpa [hE] using hd

/-- Bochner `L²` convergence of a `MemLp 2` limit gives the lintegral form. -/
lemma tendstoL2_of_memLp {Qn : ℕ → Ω → ℝ} {Q : Ω → ℝ} (hQ : MemLp Q 2 P)
    (hmem : ∀ n, MemLp (Qn n) 2 P)
    (h : Tendsto (fun n => ∫ ω, (Qn n ω - Q ω) ^ 2 ∂P) atTop (𝓝 0)) : TendstoL2 P Qn Q := by
  refine ⟨hQ.aestronglyMeasurable, ?_⟩
  have e : ∀ n, ∫⁻ ω, ‖Qn n ω - Q ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, (Qn n ω - Q ω) ^ 2 ∂P) := by
    intro n
    have hi : Integrable (fun ω => (Qn n ω - Q ω) ^ 2) P := ((hmem n).sub hQ).integrable_sq
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  simpa using ENNReal.tendsto_ofReal h

end ChaosAux

section ChaosAux2
open ProbabilityTheory Matrix
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma lintegral_enorm_sq_eq {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P = eLpNorm f 2 P ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  
lemma TendstoL2.tendsto_eLpNorm {Qn : ℕ → Ω → ℝ} {Q : Ω → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (Qn n) P) (h : TendstoL2 P Qn Q) :
    Tendsto (fun n => eLpNorm (Qn n - Q) 2 P) atTop (𝓝 0) := by
  have h2 := h.2
  have e : ∀ n, ∫⁻ ω, ‖Qn n ω - Q ω‖ₑ ^ 2 ∂P = eLpNorm (Qn n - Q) 2 P ^ 2 :=
    fun n => lintegral_enorm_sq_eq ((hmeas n).sub h.1)
  simp_rw [e] at h2
  have hc : Continuous fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ) := ENNReal.continuous_rpow_const
  have := (hc.tendsto 0).comp h2
  simp only [Function.comp_def] at this
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  refine this.congr fun n => ?_
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma TendstoL2.ae_unique {Qn : ℕ → Ω → ℝ} {Q Q' : Ω → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (Qn n) P)
    (h : TendstoL2 P Qn Q) (h' : TendstoL2 P Qn Q') : Q =ᵐ[P] Q' := by
  have h1 := h.tendsto_eLpNorm hmeas
  have h2 := h'.tendsto_eLpNorm hmeas
  have hle : ∀ n, eLpNorm (Q - Q') 2 P ≤ eLpNorm (Qn n - Q) 2 P + eLpNorm (Qn n - Q') 2 P := by
    intro n
    have e : Q - Q' = -(Qn n - Q) + (Qn n - Q') := by abel
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_neg]
  have hz : eLpNorm (Q - Q') 2 P = 0 := by
    have ht := h1.add h2
    rw [add_zero] at ht
    exact le_antisymm (ge_of_tendsto' ht hle) bot_le
  have := (eLpNorm_eq_zero_iff (by norm_num : (2:ℝ≥0∞) ≠ 0)).1 hz
  filter_upwards [this] with ω hω
  simpa [sub_eq_zero] using hω


lemma sum_fin_dite {n m : ℕ} (hnm : n ≤ m) (f : Fin n → ℝ) :
    ∑ j : Fin m, (if hj : (j : ℕ) < n then f ⟨j, hj⟩ else 0) = ∑ j : Fin n, f j := by
  set F : ℕ → ℝ := fun j => if hj : j < n then f ⟨j, hj⟩ else 0 with hF
  have h1 : ∑ j : Fin m, (if hj : (j : ℕ) < n then f ⟨j, hj⟩ else 0) = ∑ j : Fin m, F j := rfl
  have h2 : ∑ j : Fin n, f j = ∑ j : Fin n, F j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hF, j.2]
  rw [h1, h2, Fin.sum_univ_eq_sum_range F m, Fin.sum_univ_eq_sum_range F n]
  refine (Finset.sum_subset (Finset.range_mono hnm) fun j _ hj => ?_).symm
  simp only [Finset.mem_range, not_lt] at hj
  simp [hF, not_lt.2 hj]

/-- the block-orthogonal matrix `diag(U, I)` on `Fin m` -/
def blockU (n m : ℕ) (U : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if hi : (i : ℕ) < n then (if hj : (j : ℕ) < n then U ⟨i, hi⟩ ⟨j, hj⟩ else 0)
    else (if i = j then 1 else 0)

lemma blockU_row_ge {n m : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) {i : Fin m} (hi : ¬ (i : ℕ) < n)
    (k : Fin m) : blockU n m U i k = if i = k then 1 else 0 := by
  simp [blockU, hi]

lemma blockU_col_ge {n m : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) {i : Fin m} (hi : ¬ (i : ℕ) < n)
    (k : Fin m) : blockU n m U k i = if k = i then 1 else 0 := by
  by_cases hk : (k : ℕ) < n
  · have : k ≠ i := fun h => hi (h ▸ hk)
    simp [blockU, hk, hi, this]
  · simp [blockU, hk]

lemma blockU_row_lt {n m : ℕ} (hnm : n ≤ m) (U : Matrix (Fin n) (Fin n) ℝ) {i : Fin m}
    (hi : (i : ℕ) < n) (v : Fin m → ℝ) :
    ∑ k, blockU n m U i k * v k = ∑ k : Fin n, U ⟨i, hi⟩ k * v (Fin.castLE hnm k) := by
  rw [← sum_fin_dite hnm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < n
  · simp [blockU, hi, hk]
  · simp [blockU, hi, hk]

lemma blockU_row_lt' {n m : ℕ} (hnm : n ≤ m) (U : Matrix (Fin n) (Fin n) ℝ) {i : Fin m}
    (hi : (i : ℕ) < n) (v : Fin m → ℝ) :
    ∑ k, v k * blockU n m U i k = ∑ k : Fin n, v (Fin.castLE hnm k) * U ⟨i, hi⟩ k := by
  simp_rw [mul_comm (v _)]
  exact blockU_row_lt hnm U hi v

lemma blockU_col_lt {n m : ℕ} (hnm : n ≤ m) (U : Matrix (Fin n) (Fin n) ℝ) {i : Fin m}
    (hi : (i : ℕ) < n) (v : Fin m → ℝ) :
    ∑ k, blockU n m U k i * v k = ∑ k : Fin n, U k ⟨i, hi⟩ * v (Fin.castLE hnm k) := by
  rw [← sum_fin_dite hnm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < n
  · simp [blockU, hi, hk]
  · have : k ≠ i := fun h => hk (h ▸ hi)
    simp [blockU, hk, this]

lemma blockU_orth {n m : ℕ} (hnm : n ≤ m) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    (blockU n m U)ᵀ * blockU n m U = 1 := by
  have hU' : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 hU
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases hi : (i : ℕ) < n
  · rw [blockU_col_lt hnm U hi]
    by_cases hj : (j : ℕ) < n
    · have := congrFun (congrFun hU' ⟨i, hi⟩) ⟨j, hj⟩
      rw [Matrix.mul_apply] at this
      simp only [Matrix.transpose_apply] at this
      rw [Matrix.one_apply]
      have e : ∀ k : Fin n, blockU n m U (Fin.castLE hnm k) j = U k ⟨j, hj⟩ := by
        intro k; simp [blockU, k.2, hj]
      simp_rw [e, this, Matrix.one_apply]
      simp [Fin.ext_iff]
    · have e : ∀ k : Fin n, blockU n m U (Fin.castLE hnm k) j = 0 := by
        intro k; simp [blockU, k.2, hj]
      simp_rw [e, mul_zero, Finset.sum_const_zero]
      rw [Matrix.one_apply, if_neg]
      intro h; exact hj (h ▸ hi)
  · simp_rw [blockU_col_ge U hi]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hj : (j : ℕ) < n
    · have hij : i ≠ j := fun h => hi (by rw [h]; exact hj)
      rw [Matrix.one_apply, if_neg hij]
      simp [blockU, hi, hij]
    · rw [blockU_row_ge U hi, Matrix.one_apply]


lemma section_rot (A : ℕ → ℕ → ℝ) (G : ℕ → Ω → ℝ) (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ) (G' : ℕ → Ω → ℝ) (A' : ℕ → ℕ → ℝ)
    (hG' : ∀ i ω, G' i ω = if h : i < n then ∑ j : Fin n, U ⟨i, h⟩ j * G j ω else G i ω)
    (hA' : ∀ i j, A' i j = if hi : i < n then (if hj : j < n then
        ∑ k : Fin n, ∑ l : Fin n, U ⟨i, hi⟩ k * A k l * U ⟨j, hj⟩ l else
        ∑ k : Fin n, U ⟨i, hi⟩ k * A k j)
      else (if hj : j < n then ∑ l : Fin n, A i l * U ⟨j, hj⟩ l else A i j))
    (m : ℕ) (hnm : n ≤ m) (ω : Ω) :
    chaosSection A' G' m ω = chaosSection A G m ω := by
  have e1 : ∀ (c : ℕ → ℕ → ℝ) (H : ℕ → Ω → ℝ), chaosSection c H m ω = 1 / 2 * quadSum c H m ω :=
    fun _ _ => rfl
  rw [e1, e1, quadSum_eq, quadSum_eq]
  set V := blockU n m U with hV
  have hVV := blockU_orth hnm U hU
  set g : Fin m → ℝ := fun i => G i ω with hg
  set a : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j : Fin m => A i j with ha
  have hg' : (fun i : Fin m => G' i ω) = V *ᵥ g := by
    ext i
    simp only [Matrix.mulVec, dotProduct]
    rw [hG']
    by_cases hi : (i : ℕ) < n
    · rw [dif_pos hi, hV, blockU_row_lt hnm U hi]
      simp [hg]
    · rw [dif_neg hi, hV]
      simp_rw [blockU_row_ge U hi]
      simp [hg]
  have ha' : (Matrix.of fun i j : Fin m => A' i j) = V * a * Vᵀ := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hA']
    by_cases hj : (j : ℕ) < n
    · rw [hV, blockU_row_lt' hnm U hj (fun l => ∑ k, blockU n m U i k * a k l)]
      by_cases hi : (i : ℕ) < n
      · rw [dif_pos hi, dif_pos hj]
        simp_rw [blockU_row_lt hnm U hi, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp [ha]
      · rw [dif_neg hi, dif_pos hj]
        simp_rw [blockU_row_ge U hi]
        simp [ha]
    · rw [hV]
      simp_rw [blockU_row_ge U hj]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      by_cases hi : (i : ℕ) < n
      · rw [dif_pos hi, dif_neg hj, blockU_row_lt hnm U hi]
        simp [ha]
      · rw [dif_neg hi, dif_neg hj]
        simp_rw [blockU_row_ge U hi]
        simp [ha]
  rw [hg', ha']
  have h1 : (V * a * Vᵀ) *ᵥ (V *ᵥ g) = V *ᵥ (a *ᵥ g) := by
    rw [mulVec_mulVec, Matrix.mul_assoc (V * a), hVV, Matrix.mul_one, ← mulVec_mulVec]
  have h2 : ∀ w : Fin m → ℝ, (V *ᵥ g) ⬝ᵥ (V *ᵥ w) = g ⬝ᵥ w := by
    intro w
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hVV, one_mulVec]
  have h3 : trace (V * a * Vᵀ) = trace a := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  rw [h1, h2, h3]


lemma int_pow_gq (k : ℕ) : Integrable (fun x : ℝ => x ^ k * Real.exp (-(1/2) * x ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := 1/2) (by norm_num) (s := (k : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  simpa [Real.rpow_natCast] using this

lemma gauss_moment_eq (k : ℕ) : ∫ x, x ^ k ∂(gaussianReal 0 1) =
    (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, x ^ k * Real.exp (-(1/2) * x ^ 2) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
  have : -x ^ 2 / 2 = -(1/2) * x ^ 2 := by ring
  rw [this]; ring

lemma gauss_moment_succ_succ (n : ℕ) :
    ∫ x, x ^ (n + 2) ∂(gaussianReal 0 1) = (n + 1) * ∫ x, x ^ n ∂(gaussianReal 0 1) := by
  rw [gauss_moment_eq, gauss_moment_eq]
  set q : ℝ → ℝ := fun x => Real.exp (-(1/2) * x ^ 2) with hq
  have hv : ∀ x, HasDerivAt (fun x => -q x) (x * q x) x := by
    intro x
    have h := ((hasDerivAt_pow 2 x).const_mul (-(1/2) : ℝ)).exp.neg
    convert h using 1
    simp only [hq]; push_cast; ring
  have hu : ∀ x, HasDerivAt (fun x : ℝ => x ^ (n + 1)) (((n : ℝ) + 1) * x ^ n) x := by
    intro x
    have := hasDerivAt_pow (n + 1) x
    convert this using 1
    push_cast; ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x : ℝ => x ^ (n + 1))
    (v := fun x => -q x) (u' := fun x => ((n : ℝ) + 1) * x ^ n) (v' := fun x => x * q x)
    (fun x _ => hu x) (fun x _ => hv x)
    ((int_pow_gq (n + 2)).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, hq]; ring))
    (((int_pow_gq n).const_mul (-((n : ℝ) + 1))).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, hq]; ring))
    (((int_pow_gq (n + 1)).neg).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.neg_apply, hq]; ring))
  have e1 : ∫ x, x ^ (n + 2) * q x = ∫ x, x ^ (n + 1) * (x * q x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have e2 : ∫ x, ((n : ℝ) + 1) * x ^ n * -q x = -(((n : ℝ) + 1) * ∫ x, x ^ n * q x) := by
    rw [← integral_const_mul, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [e1, key, e2]
  ring

lemma gauss_m4 : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [gauss_moment_succ_succ 2, gauss_sq]; norm_num
lemma gauss_m6 : ∫ x, x ^ 6 ∂(gaussianReal 0 1) = 15 := by
  rw [gauss_moment_succ_succ 4, gauss_m4]; norm_num
lemma gauss_m8 : ∫ x, x ^ 8 ∂(gaussianReal 0 1) = 105 := by
  rw [gauss_moment_succ_succ 6, gauss_m6]; norm_num

lemma vGauss_eq : vGauss = 2 := by
  unfold vGauss
  have e : ∀ x : ℝ, (x ^ 2 - 1) ^ 2 = x ^ 4 - 2 * x ^ 2 + 1 := fun x => by ring
  simp_rw [e]
  have i4 := gauss_integrable_pow 4
  have i2 := gauss_integrable_pow 2
  have j1 : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2) (gaussianReal 0 1) := i4.sub (i2.const_mul 2)
  rw [integral_add j1 (integrable_const _), integral_sub i4 (i2.const_mul 2),
    integral_const_mul, gauss_m4, gauss_sq]
  simp; norm_num

lemma gauss_sqm1_four : ∫ x, (x ^ 2 - 1) ^ 4 ∂(gaussianReal 0 1) = 60 := by
  have e : ∀ x : ℝ, (x ^ 2 - 1) ^ 4 = x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2 + 1 :=
    fun x => by ring
  simp_rw [e]
  have i8 := gauss_integrable_pow 8
  have i6 := gauss_integrable_pow 6
  have i4 := gauss_integrable_pow 4
  have i2 := gauss_integrable_pow 2
  have j1 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6) (gaussianReal 0 1) := i8.sub (i6.const_mul 4)
  have j2 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4) (gaussianReal 0 1) :=
    j1.add (i4.const_mul 6)
  have j3 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2) (gaussianReal 0 1) :=
    j2.sub (i2.const_mul 4)
  rw [integral_add j3 (integrable_const _), integral_sub j2 (i2.const_mul 4),
    integral_add j1 (i4.const_mul 6), integral_sub i8 (i6.const_mul 4),
    integral_const_mul, integral_const_mul, integral_const_mul, gauss_m8, gauss_m6, gauss_m4, gauss_sq]
  simp; norm_num


lemma abs_pow_le_one_add_pow_four (x : ℝ) {k : ℕ} (hk : k ≤ 4) : |x| ^ k ≤ 1 + x ^ 4 := by
  have h4 : x ^ 4 = |x| ^ 4 := by
    rw [pow_abs]; exact (abs_of_nonneg (by positivity)).symm
  rw [h4]
  rcases le_total |x| 1 with h | h
  · have : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) h
    have : 0 ≤ |x| ^ 4 := by positivity
    linarith
  · have : |x| ^ k ≤ |x| ^ 4 := pow_le_pow_right₀ h hk
    linarith

section Indep4
variable {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} [IsProbabilityMeasure μ]

lemma integrable_pow_of_four {X : Ω' → ℝ} (hX : AEStronglyMeasurable X μ)
    (h4 : Integrable (fun ω => X ω ^ 4) μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => X ω ^ k) μ := by
  refine ((integrable_const 1).add h4).mono' (hX.pow k) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact abs_pow_le_one_add_pow_four _ hk

lemma indep_moments {X Y : Ω' → ℝ} (hXY : IndepFun X Y μ) (hXm : Measurable X) (hYm : Measurable Y)
    (hX4 : Integrable (fun ω => X ω ^ 4) μ) (hY4 : Integrable (fun ω => Y ω ^ 4) μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0) :
    Integrable (fun ω => (X ω + Y ω) ^ 4) μ ∧
    ∫ ω, (X ω + Y ω) ^ 2 ∂μ = ∫ ω, X ω ^ 2 ∂μ + ∫ ω, Y ω ^ 2 ∂μ ∧
    ∫ ω, (X ω + Y ω) ^ 4 ∂μ =
      ∫ ω, X ω ^ 4 ∂μ + 6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) + ∫ ω, Y ω ^ 4 ∂μ := by
  have iX : ∀ k ≤ 4, Integrable (fun ω => X ω ^ k) μ := fun k hk =>
    integrable_pow_of_four hXm.aestronglyMeasurable hX4 hk
  have iY : ∀ k ≤ 4, Integrable (fun ω => Y ω ^ k) μ := fun k hk =>
    integrable_pow_of_four hYm.aestronglyMeasurable hY4 hk
  have ind : ∀ a b : ℕ, IndepFun (fun ω => X ω ^ a) (fun ω => Y ω ^ b) μ := fun a b =>
    hXY.comp (measurable_id.pow_const a) (measurable_id.pow_const b)
  have iXY : ∀ a b : ℕ, a ≤ 4 → b ≤ 4 → Integrable (fun ω => X ω ^ a * Y ω ^ b) μ :=
    fun a b ha hb => (ind a b).integrable_mul (iX a ha) (iY b hb)
  have eXY : ∀ a b : ℕ, ∫ ω, X ω ^ a * Y ω ^ b ∂μ = (∫ ω, X ω ^ a ∂μ) * ∫ ω, Y ω ^ b ∂μ :=
    fun a b => (ind a b).integral_fun_mul_eq_mul_integral ((hXm.pow_const a).aestronglyMeasurable)
      ((hYm.pow_const b).aestronglyMeasurable)
  have hX1 : ∫ ω, X ω ^ 1 ∂μ = 0 := by simpa using hX0
  have hY1 : ∫ ω, Y ω ^ 1 ∂μ = 0 := by simpa using hY0
  refine ⟨?_, ?_, ?_⟩
  · have := (((((iX 4 le_rfl).add ((iXY 3 1 (by norm_num) (by norm_num)).const_mul 4)).add
      ((iXY 2 2 (by norm_num) (by norm_num)).const_mul 6)).add
      ((iXY 1 3 (by norm_num) (by norm_num)).const_mul 4)).add (iY 4 le_rfl))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]; ring
  · have e : ∀ ω, (X ω + Y ω) ^ 2 = X ω ^ 2 + (2 * (X ω ^ 1 * Y ω ^ 1) + Y ω ^ 2) :=
      fun ω => by ring
    simp_rw [e]
    have a1 : Integrable (fun ω => 2 * (X ω ^ 1 * Y ω ^ 1)) μ :=
      (iXY 1 1 (by norm_num) (by norm_num)).const_mul 2
    have a2 : Integrable (fun ω => 2 * (X ω ^ 1 * Y ω ^ 1) + Y ω ^ 2) μ := a1.add (iY 2 (by norm_num))
    rw [integral_add (iX 2 (by norm_num)) a2, integral_add a1 (iY 2 (by norm_num)),
      integral_const_mul, eXY, hX1]
    ring
  · have e : ∀ ω, (X ω + Y ω) ^ 4 = X ω ^ 4 + (4 * (X ω ^ 3 * Y ω ^ 1) +
        (6 * (X ω ^ 2 * Y ω ^ 2) + (4 * (X ω ^ 1 * Y ω ^ 3) + Y ω ^ 4))) := fun ω => by ring
    simp_rw [e]
    have i31 : Integrable (fun ω => 4 * (X ω ^ 3 * Y ω ^ 1)) μ :=
      (iXY 3 1 (by norm_num) (by norm_num)).const_mul 4
    have i22 : Integrable (fun ω => 6 * (X ω ^ 2 * Y ω ^ 2)) μ :=
      (iXY 2 2 (by norm_num) (by norm_num)).const_mul 6
    have i13 : Integrable (fun ω => 4 * (X ω ^ 1 * Y ω ^ 3)) μ :=
      (iXY 1 3 (by norm_num) (by norm_num)).const_mul 4
    have i4 := iY 4 le_rfl
    have j1 : Integrable (fun ω => 4 * (X ω ^ 1 * Y ω ^ 3) + Y ω ^ 4) μ := i13.add i4
    have j2 : Integrable (fun ω => 6 * (X ω ^ 2 * Y ω ^ 2) + (4 * (X ω ^ 1 * Y ω ^ 3) + Y ω ^ 4)) μ :=
      i22.add j1
    have j3 : Integrable (fun ω => 4 * (X ω ^ 3 * Y ω ^ 1) +
        (6 * (X ω ^ 2 * Y ω ^ 2) + (4 * (X ω ^ 1 * Y ω ^ 3) + Y ω ^ 4))) μ := i31.add j2
    rw [integral_add (iX 4 le_rfl) j3, integral_add i31 j2, integral_add i22 j1,
      integral_add i13 i4, integral_const_mul, integral_const_mul, integral_const_mul,
      eXY, eXY, eXY, hX1, hY1]
    ring

end Indep4


lemma gauss_integrable_sqm1_four : Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 4) (gaussianReal 0 1) := by
  have h := ((((gauss_integrable_pow 8).sub ((gauss_integrable_pow 6).const_mul 4)).add
    ((gauss_integrable_pow 4).const_mul 6)).sub ((gauss_integrable_pow 2).const_mul 4)).add
    (integrable_const (1 : ℝ))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]; ring

lemma pi_fourth_aux (N : ℕ) (l : Fin N → ℝ) (s : Finset (Fin N)) :
    let γN := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
    Integrable (fun y : Fin N → ℝ => (∑ k ∈ s, l k * (y k ^ 2 - 1)) ^ 4) γN ∧
    ∫ y, ∑ k ∈ s, l k * (y k ^ 2 - 1) ∂γN = 0 ∧
    ∫ y, (∑ k ∈ s, l k * (y k ^ 2 - 1)) ^ 2 ∂γN = 2 * ∑ k ∈ s, l k ^ 2 ∧
    ∫ y, (∑ k ∈ s, l k * (y k ^ 2 - 1)) ^ 4 ∂γN ≤ 60 * (∑ k ∈ s, l k ^ 2) ^ 2 := by
  intro γN
  set f : Fin N → (Fin N → ℝ) → ℝ := fun j y => l j * (y j ^ 2 - 1) with hf
  have hfm : ∀ j, Measurable (f j) := fun j => by simp only [hf]; fun_prop
  have hind : iIndepFun f γN :=
    iIndepFun_pi (μ := fun _ : Fin N => gaussianReal 0 1) (X := fun j (x : ℝ) => l j * (x ^ 2 - 1))
      (fun j => by fun_prop)
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    obtain ⟨ih4, ih0, ih2, ih4le⟩ := ih
    have hS : Measurable (fun y : Fin N → ℝ => ∑ j ∈ s, l j * (y j ^ 2 - 1)) := by fun_prop
    have hT : Measurable (fun y : Fin N → ℝ => l k * (y k ^ 2 - 1)) := by fun_prop
    have hI : IndepFun (fun y : Fin N → ℝ => ∑ j ∈ s, l j * (y j ^ 2 - 1))
        (fun y : Fin N → ℝ => l k * (y k ^ 2 - 1)) γN := by
      have := hind.indepFun_finsetSum_of_notMem hfm hk
      have e : (∑ j ∈ s, f j) = fun y : Fin N → ℝ => ∑ j ∈ s, l j * (y j ^ 2 - 1) := by
        ext y; simp [hf, Finset.sum_apply]
      rw [e] at this
      exact this
    have hT4 : Integrable (fun y : Fin N → ℝ => (l k * (y k ^ 2 - 1)) ^ 4) γN := by
      have := pi_integrable_eval N (fun x => (l k * (x ^ 2 - 1)) ^ 4) (by fun_prop)
        ((gauss_integrable_sqm1_four.const_mul (l k ^ 4)).congr
          (Filter.Eventually.of_forall fun x => by simp only; ring)) k
      exact this
    have hT0 : ∫ y, l k * (y k ^ 2 - 1) ∂γN = 0 := by
      rw [pi_integral_eval N (fun x => l k * (x ^ 2 - 1)) (by fun_prop) k, integral_const_mul,
        gauss_sqm1, mul_zero]
    have hT2 : ∫ y, (l k * (y k ^ 2 - 1)) ^ 2 ∂γN = 2 * l k ^ 2 := by
      rw [pi_integral_eval N (fun x => (l k * (x ^ 2 - 1)) ^ 2) (by fun_prop) k]
      simp_rw [mul_pow]
      rw [integral_const_mul]
      have := vGauss_eq
      unfold vGauss at this
      rw [this]; ring
    have hT4' : ∫ y, (l k * (y k ^ 2 - 1)) ^ 4 ∂γN = 60 * l k ^ 4 := by
      rw [pi_integral_eval N (fun x => (l k * (x ^ 2 - 1)) ^ 4) (by fun_prop) k]
      simp_rw [mul_pow]
      rw [integral_const_mul, gauss_sqm1_four]; ring
    obtain ⟨m4, m2, m4e⟩ := indep_moments hI hS hT ih4 hT4 ih0 hT0
    have e : ∀ y : Fin N → ℝ, ∑ j ∈ insert k s, l j * (y j ^ 2 - 1) =
        (∑ j ∈ s, l j * (y j ^ 2 - 1)) + l k * (y k ^ 2 - 1) := by
      intro y; rw [Finset.sum_insert hk, add_comm]
    simp_rw [e, Finset.sum_insert hk]
    have hSi : Integrable (fun y : Fin N → ℝ => ∑ j ∈ s, l j * (y j ^ 2 - 1)) γN := by
      simpa using integrable_pow_of_four hS.aestronglyMeasurable ih4 (k := 1) (by norm_num)
    have hTi : Integrable (fun y : Fin N → ℝ => l k * (y k ^ 2 - 1)) γN := by
      simpa using integrable_pow_of_four hT.aestronglyMeasurable hT4 (k := 1) (by norm_num)
    refine ⟨m4, ?_, ?_, ?_⟩
    · rw [integral_add hSi hTi, ih0, hT0]; simp
    · rw [m2, ih2, hT2]; ring
    · rw [m4e, ih2, hT2, hT4']
      have hs0 : 0 ≤ ∑ j ∈ s, l j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      nlinarith [sq_nonneg (l k), pow_two_nonneg (l k ^ 2), mul_nonneg hs0 (sq_nonneg (l k))]


lemma quadSum_transfer {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (c : ℕ → ℕ → ℝ)
    (hc : ∀ i j, c i j = c j i) (N : ℕ) :
    ∃ l : Fin N → ℝ, ∑ k, l k ^ 2 = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j ^ 2 ∧
      ∀ F : ℝ → ℝ, Continuous F →
        (∫ ω, F (quadSum c G N ω) ∂P = ∫ y, F (∑ k, l k * (y k ^ 2 - 1))
            ∂(Measure.pi (fun _ : Fin N => gaussianReal 0 1))) ∧
        (Integrable (fun ω => F (quadSum c G N ω)) P ↔ Integrable (fun y : Fin N → ℝ =>
            F (∑ k, l k * (y k ^ 2 - 1))) (Measure.pi (fun _ : Fin N => gaussianReal 0 1))) := by
  set a : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun i j : Fin N => c i j with ha
  have hH : a.IsHermitian := by
    ext i j
    simp [ha, Matrix.conjTranspose_apply, hc]
  obtain ⟨b, l, h1, h2, h3⟩ := quad_eig N a hH
  set γ := Measure.pi (fun _ : Fin N => gaussianReal 0 1) with hγ
  set φ : (Fin N → ℝ) → (Fin N → ℝ) := fun x k => inner ℝ (b k) (WithLp.toLp 2 x) with hφ
  have hφm : Measurable φ := by
    refine Measurable.of_eval fun k => ?_
    exact (continuous_const.inner (by fun_prop : Continuous fun x : Fin N → ℝ => WithLp.toLp 2 x)).measurable
  have hmp : MeasurePreserving φ γ γ := ⟨hφm, map_pi_coord_eq N b⟩
  set Z : Ω → (Fin N → ℝ) := fun ω i => G i ω with hZdef
  have hZ : AEMeasurable Z P := AEMeasurable.of_eval fun i => hG.aemeasurable i
  have hlaw : P.map Z = γ := law_vec hG N
  set D : (Fin N → ℝ) → ℝ := fun y => ∑ k, l k * (y k ^ 2 - 1) with hD
  have hDc : Continuous D := by simp only [hD]; fun_prop
  have hφc : Continuous φ := by
    refine continuous_pi fun k => ?_
    exact continuous_const.inner (by fun_prop : Continuous fun x : Fin N → ℝ => WithLp.toLp 2 x)
  have hpt : ∀ ω, quadSum c G N ω = D (φ (Z ω)) := by
    intro ω
    rw [quadSum_eq]
    simp only [hD, hφ, hZdef]
    rw [h1, ← h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have h3' : ∑ k, l k ^ 2 = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j ^ 2 := by
    rw [h3, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range]
    simp [ha]
  refine ⟨l, h3', fun F hF => ⟨?_, ?_⟩⟩
  · simp_rw [hpt]
    have hc1 : Continuous fun z => F (D (φ z)) := hF.comp (hDc.comp hφc)
    have e0 : (∫ ω, F (D (φ (Z ω))) ∂P) = ∫ z, F (D (φ z)) ∂(P.map Z) :=
      (integral_map hZ (f := fun z => F (D (φ z))) (by rw [hlaw]; exact hc1.aestronglyMeasurable)).symm
    rw [e0, hlaw]
    have := integral_map hmp.measurable.aemeasurable (μ := γ) (f := fun y => F (D y))
      (by rw [hmp.map_eq]; exact (hF.comp hDc).aestronglyMeasurable)
    rw [hmp.map_eq] at this
    exact this.symm
  · simp_rw [hpt]
    have hc1 : Continuous fun z => F (D (φ z)) := hF.comp (hDc.comp hφc)
    have e1 := integrable_map_measure (μ := P) (f := Z) (g := fun z => F (D (φ z)))
      (by rw [hlaw]; exact hc1.aestronglyMeasurable) hZ
    rw [hlaw] at e1
    rw [← Function.comp_def (fun z => F (D (φ z))) Z, ← e1]
    exact hmp.integrable_comp (g := fun y => F (D y)) (hF.comp hDc).aestronglyMeasurable


lemma quadSum_mean {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (c : ℕ → ℕ → ℝ)
    (hc : ∀ i j, c i j = c j i) (N : ℕ) : ∫ ω, quadSum c G N ω ∂P = 0 := by
  obtain ⟨l, -, hF⟩ := quadSum_transfer hG c hc N
  have h := (hF id continuous_id).1
  simp only [id] at h
  rw [h]
  exact (pi_fourth_aux N l Finset.univ).2.1

lemma quadSum_four {G : ℕ → Ω → ℝ} (hG : IsStdGaussianSeq P G) (c : ℕ → ℕ → ℝ)
    (hc : ∀ i j, c i j = c j i) (N : ℕ) :
    Integrable (fun ω => quadSum c G N ω ^ 4) P ∧
    ∫ ω, quadSum c G N ω ^ 4 ∂P ≤
      60 * (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j ^ 2) ^ 2 := by
  obtain ⟨l, hl, hF⟩ := quadSum_transfer hG c hc N
  have h := hF (fun x => x ^ 4) (continuous_pow 4)
  have hp := pi_fourth_aux N l Finset.univ
  refine ⟨h.2.2 hp.1, ?_⟩
  rw [h.1, ← hl]
  exact hp.2.2.2

lemma sq_integral_le_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  have h := variance_nonneg f P
  rw [variance_eq_sub hf] at h
  simp only [Pi.pow_apply] at h
  linarith

lemma L2_limit_moments {Qn : ℕ → Ω → ℝ} {Q : Ω → ℝ} (hQ : MemLp Q 2 P)
    (hmem : ∀ n, MemLp (Qn n) 2 P)
    (h : Tendsto (fun n => ∫ ω, (Qn n ω - Q ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, Qn n ω ∂P) atTop (𝓝 (∫ ω, Q ω ∂P)) ∧
    Tendsto (fun n => ∫ ω, Qn n ω ^ 2 ∂P) atTop (𝓝 (∫ ω, Q ω ^ 2 ∂P)) := by
  have hs : Tendsto (fun n => Real.sqrt (∫ ω, (Qn n ω - Q ω) ^ 2 ∂P)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h
    simp only [Function.comp_def, Real.sqrt_zero] at this
    exact this
  constructor
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hs
    rw [Real.dist_eq, ← integral_sub ((hmem n).integrable one_le_two) (hQ.integrable one_le_two)]
    exact Real.abs_le_sqrt (sq_integral_le_integral_sq ((hmem n).sub hQ))
  · set q : ℕ → Lp ℝ 2 P := fun n => (hmem n).toLp (Qn n) with hq
    set q' : Lp ℝ 2 P := hQ.toLp Q with hq'
    have hn : ∀ n, ‖q n‖ ^ 2 = ∫ ω, Qn n ω ^ 2 ∂P := by
      intro n
      rw [Lp2_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [(hmem n).coeFn_toLp] with ω hω
      simp only [hq]; rw [hω]
    have hn' : ‖q'‖ ^ 2 = ∫ ω, Q ω ^ 2 ∂P := by
      rw [Lp2_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [hQ.coeFn_toLp] with ω hω
      simp only [hq']; rw [hω]
    have hd : ∀ n, ‖q n - q'‖ = Real.sqrt (∫ ω, (Qn n ω - Q ω) ^ 2 ∂P) := by
      intro n
      rw [← Real.sqrt_sq (norm_nonneg _), Lp2_norm_sq]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (q n) q', (hmem n).coeFn_toLp, hQ.coeFn_toLp] with ω h1 h2 h3
      simp only [hq, hq'] at h1 h2 h3 ⊢
      rw [h1]; simp only [Pi.sub_apply]; rw [h2, h3]
    have hconv : Tendsto q atTop (𝓝 q') := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp_rw [hd]; exact hs
    have := ((continuous_norm.tendsto q').comp hconv).pow 2
    simp only [Function.comp_def] at this
    simp_rw [hn, hn'] at this
    exact this

lemma fatou_four {Qn : ℕ → Ω → ℝ} {Q : Ω → ℝ} (hmeas : ∀ n, AEStronglyMeasurable (Qn n) P)
    (hT : TendstoL2 P Qn Q) {C : ℝ}
    (hC : ∀ n, Integrable (fun ω => Qn n ω ^ 4) P ∧ ∫ ω, Qn n ω ^ 4 ∂P ≤ C) :
    ∫ ω, Q ω ^ 4 ∂P ≤ C := by
  have hin := tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero (hT.tendsto_eLpNorm hmeas)
  obtain ⟨ns, -, hae⟩ := hin.exists_seq_tendsto_ae
  have hC0 : 0 ≤ C := (integral_nonneg fun ω => by positivity).trans (hC 0).2
  have hc : Continuous fun x : ℝ => ENNReal.ofReal (x ^ 4) :=
    ENNReal.continuous_ofReal.comp (continuous_pow 4)
  have key : ∫⁻ ω, ENNReal.ofReal (Q ω ^ 4) ∂P ≤ ENNReal.ofReal C := by
    calc ∫⁻ ω, ENNReal.ofReal (Q ω ^ 4) ∂P
        = ∫⁻ ω, liminf (fun i => ENNReal.ofReal (Qn (ns i) ω ^ 4)) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          exact (((hc.tendsto _).comp hω).liminf_eq).symm
      _ ≤ liminf (fun i => ∫⁻ ω, ENNReal.ofReal (Qn (ns i) ω ^ 4) ∂P) atTop :=
          lintegral_liminf_le' fun i => ((hmeas _).aemeasurable.pow_const 4).ennreal_ofReal
      _ ≤ ENNReal.ofReal C := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun i => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hC _).1
            (Filter.Eventually.of_forall fun ω => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hC _).2
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => Q ω ^ 4)
    (Filter.Eventually.of_forall fun ω => by positivity)
    (hT.1.pow 4 : AEStronglyMeasurable (fun ω => Q ω ^ 4) P)]
  exact ENNReal.toReal_le_of_le_ofReal hC0 key

end ChaosAux2

section Chaos

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Proposition 7.18, display `E:eq:chaos-isometry` (lines 9784-9788), existence part:
the sections converge in `L²`; the limit is basis-independent (see `chaos_basis_independent`). -/
theorem chaos_tendsto (A : ℕ → ℕ → ℝ) (hA : IsSymmetricHS A) (G : ℕ → Ω → ℝ)
    (hG : IsStdGaussianSeq P G) :
    TendstoL2 P (chaosSection A G) (chaos P A G) := by
  obtain ⟨Q, hQmem, hQ⟩ := exists_chaos_limit hG A hA
  have hmem : ∀ n, MemLp (chaosSection A G n) 2 P := fun n => (memLp_quadSum hG A n).const_mul (1/2)
  have h : ∃ Q : Ω → ℝ, TendstoL2 P (chaosSection A G) Q := ⟨Q, tendstoL2_of_memLp hQmem hmem hQ⟩
  unfold chaos
  rw [dif_pos h]
  exact h.choose_spec

/-- Proposition 7.18, `E:eq:chaos-isometry`: `E[Q(A)] = 0`, `Var Q(A) = ½ ‖A‖²_HS`,
`E[Q(A)⁴] ≤ 15 Var(Q(A))²`. -/
theorem chaos_moments (A : ℕ → ℕ → ℝ) (hA : IsSymmetricHS A) (G : ℕ → Ω → ℝ)
    (hG : IsStdGaussianSeq P G) :
    ∫ ω, chaos P A G ω ∂P = 0 ∧
    ProbabilityTheory.variance (chaos P A G) P = (1 / 2) * hsNorm A ^ 2 ∧
    ∫ ω, chaos P A G ω ^ 4 ∂P ≤ 15 * (ProbabilityTheory.variance (chaos P A G) P) ^ 2 := by
  obtain ⟨Q', hQmem, hQ⟩ := exists_chaos_limit hG A hA
  have hmem : ∀ n, MemLp (chaosSection A G n) 2 P := fun n =>
    (memLp_quadSum hG A n).const_mul (1/2)
  have hmeas : ∀ n, AEStronglyMeasurable (chaosSection A G n) P := fun n =>
    (hmem n).aestronglyMeasurable
  have hT' : TendstoL2 P (chaosSection A G) Q' := tendstoL2_of_memLp hQmem hmem hQ
  have hT := chaos_tendsto P A hA G hG
  have hae : chaos P A G =ᵐ[P] Q' := TendstoL2.ae_unique hmeas hT hT'
  have hsec : ∀ n ω, chaosSection A G n ω = 1 / 2 * quadSum A G n ω := fun _ _ => rfl
  set S := ∑' p : ℕ × ℕ, A p.1 p.2 ^ 2 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => sq_nonneg _
  have hpS : ∀ n, 0 ≤ hsPartial A n ∧ hsPartial A n ≤ S := by
    intro n
    have e : hsPartial A n = ∑ p ∈ Finset.range n ×ˢ Finset.range n, A p.1 p.2 ^ 2 := by
      rw [Finset.sum_product]; rfl
    refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _, ?_⟩
    rw [e]
    exact hA.2.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  -- moments of the sections
  have hm0 : ∀ n, ∫ ω, chaosSection A G n ω ∂P = 0 := by
    intro n
    simp_rw [hsec]
    rw [integral_const_mul, quadSum_mean hG A hA.1, mul_zero]
  have hm2 : ∀ n, ∫ ω, chaosSection A G n ω ^ 2 ∂P = 1 / 2 * hsPartial A n := by
    intro n
    simp_rw [hsec, mul_pow]
    rw [integral_const_mul, quadSum_L2 hG A hA.1 n, vGauss_eq]
    unfold hsPartial; ring
  obtain ⟨hl1, hl2⟩ := L2_limit_moments hQmem hmem hQ
  have hQ0 : ∫ ω, Q' ω ∂P = 0 :=
    tendsto_nhds_unique hl1 (by simp_rw [hm0]; exact tendsto_const_nhds)
  have hQ2 : ∫ ω, Q' ω ^ 2 ∂P = 1 / 2 * S := by
    refine tendsto_nhds_unique hl2 ?_
    simp_rw [hm2]
    exact (hsPartial_tendsto A hA.2).const_mul _
  have hc0 : ∫ ω, chaos P A G ω ∂P = 0 := by rw [integral_congr_ae hae, hQ0]
  have hvar : ProbabilityTheory.variance (chaos P A G) P = 1 / 2 * S := by
    rw [ProbabilityTheory.variance_of_integral_eq_zero hT.1.aemeasurable hc0, ← hQ2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hω]
  have hhs : hsNorm A ^ 2 = S := Real.sq_sqrt hS0
  refine ⟨hc0, by rw [hvar, hhs], ?_⟩
  rw [hvar]
  refine fatou_four hmeas hT fun n => ?_
  obtain ⟨hi4, hle4⟩ := quadSum_four hG A hA.1 n
  have e4 : ∀ ω, chaosSection A G n ω ^ 4 = 1 / 16 * quadSum A G n ω ^ 4 := fun ω => by
    rw [hsec]; ring
  simp_rw [e4]
  refine ⟨hi4.const_mul _, ?_⟩
  rw [integral_const_mul]
  have h1 := hpS n
  have hp : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j ^ 2) = hsPartial A n := rfl
  rw [hp] at hle4
  have : hsPartial A n ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ h1.1 h1.2 2
  nlinarith

/-- Proposition 7.18, basis independence: for an orthogonal change of coordinates `U`
(`U Uᵀ = I` on `ℓ²`), `Q(UᵀAU)` computed from `G' = U G` has the same law as `Q(A)` from `G`.
Stated with `U` an orthogonal matrix on finitely many coordinates extended by the identity. -/
theorem chaos_basis_independent (A : ℕ → ℕ → ℝ) (hA : IsSymmetricHS A) (G : ℕ → Ω → ℝ)
    (hG : IsStdGaussianSeq P G) (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    let G' : ℕ → Ω → ℝ := fun i ω =>
      if h : i < n then ∑ j : Fin n, U ⟨i, h⟩ j * G j ω else G i ω
    let A' : ℕ → ℕ → ℝ := fun i j =>
      if hi : i < n then (if hj : j < n then
        ∑ k : Fin n, ∑ l : Fin n, U ⟨i, hi⟩ k * A k l * U ⟨j, hj⟩ l else
        ∑ k : Fin n, U ⟨i, hi⟩ k * A k j)
      else (if hj : j < n then ∑ l : Fin n, A i l * U ⟨j, hj⟩ l else A i j)
    chaos P A' G' =ᵐ[P] chaos P A G := by
  intro G' A'
  have hsec : ∀ m, n ≤ m → chaosSection A' G' m = chaosSection A G m := fun m hm =>
    funext fun ω => section_rot A G n U hU G' A' (fun _ _ => rfl) (fun _ _ => rfl) m hm ω
  have hev : ∀ (Q : Ω → ℝ), (fun m => ∫⁻ ω, ‖chaosSection A' G' m ω - Q ω‖ₑ ^ 2 ∂P) =ᶠ[atTop]
      (fun m => ∫⁻ ω, ‖chaosSection A G m ω - Q ω‖ₑ ^ 2 ∂P) := fun Q =>
    Filter.eventually_atTop.2 ⟨n, fun m hm => by simp only [hsec m hm]⟩
  have hT := chaos_tendsto P A hA G hG
  have hT' : TendstoL2 P (chaosSection A' G') (chaos P A G) :=
    ⟨hT.1, hT.2.congr' (hev _).symm⟩
  have hex : ∃ Q, TendstoL2 P (chaosSection A' G') Q := ⟨_, hT'⟩
  have hC : TendstoL2 P (chaosSection A' G') (chaos P A' G') := by
    unfold chaos; rw [dif_pos hex]; exact hex.choose_spec
  have hC2 : TendstoL2 P (chaosSection A G) (chaos P A' G') := ⟨hC.1, hC.2.congr' (hev _)⟩
  have hmeas : ∀ m, AEStronglyMeasurable (chaosSection A G m) P := fun m =>
    ((memLp_quadSum hG A m).const_mul (1/2)).aestronglyMeasurable
  exact TendstoL2.ae_unique hmeas hC2 hT

end Chaos

/-! ### Lemma 7.3: Banach-valued Gaussian contractions (work package EDGE-01) -/

section Contractions

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- A random element `D : Ω → B` of the centered second chaos of the Gaussian space spanned by
i.i.d. standard Gaussian coordinates `ξ`: an `L^q(B)` limit of centered quadratic polynomials in
finitely many coordinates (source lines 7815-7818). -/
def InSecondChaos (ξ : ℕ → Ω → ℝ) (q : ℝ) (D : Ω → B) : Prop :=
  AEStronglyMeasurable D P ∧ ∃ (n : ℕ → ℕ) (c : ℕ → ℕ → ℕ → B),
    Tendsto (fun m => ∫⁻ ω, ‖(∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m),
      (ξ i ω * ξ j ω - if i = j then 1 else 0) • c m i j) - D ω‖ₑ ^ q ∂P) atTop (𝓝 0)

/-- A random element of the first chaos: `L^q(B)` limit of linear polynomials. -/
def InFirstChaos (ξ : ℕ → Ω → ℝ) (q : ℝ) (J : Ω → B) : Prop :=
  AEStronglyMeasurable J P ∧ ∃ (n : ℕ → ℕ) (c : ℕ → ℕ → B),
    Tendsto (fun m => ∫⁻ ω, ‖(∑ i ∈ Finset.range (n m), ξ i ω • c m i) - J ω‖ₑ ^ q ∂P)
      atTop (𝓝 0)

/-! #### Auxiliary lemmas for Lemma 7.3 (proof of `gaussian_second_contraction`)

Route: Stein-type integration by parts for the finite-dimensional standard Gaussian measure
(one-dimensional Stein from Mathlib's integration by parts, Fubini over `Fin (n+1)`), the
resulting exact identities for finite polynomials `linP`, `quadP`, and then `L^p` limits:
Hölder, a quantitative Fernique moment-4 bound, and Fatou. (The manuscript's route via
`gaussian_ibp` is replaced by this direct finite-dimensional argument.) -/

namespace Contr

section Aux_Hlp1
open ProbabilityTheory

lemma hasDerivAt_gaussianPDFReal01 (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(x * gaussianPDFReal 0 1 x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) (-x) x := by
    have := ((hasDerivAt_id x).sub_const 0).pow 2
    have := this.neg.div_const (2 * ((1 : ℝ≥0) : ℝ))
    convert this using 1
    · ext y; simp
    · simp; ring
  have h2 := (h1.exp).const_mul ((√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹)
  convert h2 using 1
  · ext y; simp [gaussianPDFReal_def]
  · simp [gaussianPDFReal_def]; ring

lemma stein_real {h h' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (h1 : Integrable h (gaussianReal 0 1)) (h2 : Integrable (fun x => x * h x) (gaussianReal 0 1))
    (h3 : Integrable h' (gaussianReal 0 1)) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, h' x ∂(gaussianReal 0 1) := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  have hden : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero 0 hv
  have tr : ∀ g : ℝ → ℝ, Integrable g (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * g x) volume := by
    intro g
    rw [hden, integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    simp [toReal_gaussianPDF]
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have h1' := (tr _).1 h1
  have h2' := (tr _).1 h2
  have h3' := (tr _).1 h3
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := h) (u' := h') (v := fun x => -gaussianPDFReal 0 1 x)
    (v' := fun x => x * gaussianPDFReal 0 1 x) (fun x _ => hd x)
    (fun x _ => by simpa using (hasDerivAt_gaussianPDFReal01 x).fun_neg)
    (by
      refine h2'.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by
      refine (h3'.neg).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by
      refine (h1'.neg).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have e1 : ∫ x, gaussianPDFReal 0 1 x * (x * h x) = ∫ x, h x * (x * gaussianPDFReal 0 1 x) := by
    congr 1; ext x; ring
  have e2 : ∫ x, h' x * -gaussianPDFReal 0 1 x = - ∫ x, gaussianPDFReal 0 1 x * h' x := by
    rw [← integral_neg]; congr 1; ext x; ring
  rw [e1, key, e2]; ring


/-- The standard Gaussian product measure on `ℝ^N`. -/
abbrev gpi (N : ℕ) : Measure (Fin N → ℝ) := Measure.pi fun _ => gaussianReal 0 1

lemma stein_pi {N : ℕ} (i : Fin N) {F F' : (Fin N → ℝ) → ℝ}
    (hd : ∀ z, HasDerivAt (fun x => F (Function.update z i x)) (F' z) (z i))
    (h1 : Integrable F (gpi N)) (h2 : Integrable (fun z => z i * F z) (gpi N))
    (h3 : Integrable F' (gpi N)) :
    ∫ z, z i * F z ∂(gpi N) = ∫ z, F' z ∂(gpi N) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i.pos; omega⟩
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i with he
  have hsymm := hmp.symm e
  have tr : ∀ g : (Fin (n+1) → ℝ) → ℝ, ∫ z, g z ∂(gpi (n+1)) =
      ∫ p, g (e.symm p) ∂((gaussianReal 0 1).prod (Measure.pi fun j : Fin n => gaussianReal 0 1)) := by
    intro g
    exact (hsymm.integral_comp' g).symm
  have trI : ∀ g : (Fin (n+1) → ℝ) → ℝ, Integrable g (gpi (n+1)) →
      Integrable (fun p => g (e.symm p))
        ((gaussianReal 0 1).prod (Measure.pi fun j : Fin n => gaussianReal 0 1)) := by
    intro g hg
    exact (hsymm.integrable_comp_emb e.symm.measurableEmbedding).2 hg
  have ins : ∀ (x : ℝ) (w : Fin n → ℝ), e.symm (x, w) = Fin.insertNth i x w := by
    intro x w; rfl
  rw [tr, tr]
  simp only [ins]
  have i1 := trI _ h1
  have i2 := trI _ h2
  have i3 := trI _ h3
  simp only [ins] at i1 i2 i3
  rw [integral_prod_symm _ i2, integral_prod_symm _ i3]
  refine integral_congr_ae ?_
  filter_upwards [i1.prod_left_ae, i2.prod_left_ae, i3.prod_left_ae] with w hw1 hw2 hw3
  simp only [Fin.insertNth_apply_same] at hw2 ⊢
  refine stein_real (h := fun x => F (Fin.insertNth i x w))
    (h' := fun x => F' (Fin.insertNth i x w)) (fun x => ?_) hw1 hw2 hw3
  have := hd (Fin.insertNth i x w)
  simpa [Fin.update_insertNth] using this


instance gpi_isGaussian (N : ℕ) : IsGaussian (gpi N) := by
  have h : HasGaussianLaw (fun (z : Fin N → ℝ) (i : Fin N) => z i) (gpi N) := by
    refine iIndepFun.hasGaussianLaw (X := fun (i : Fin N) (z : Fin N → ℝ) => z i) (fun i => ?_) ?_
    · refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
      have : (gpi N).map (fun z : Fin N → ℝ => z i) = gaussianReal 0 1 :=
        (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) i).map_eq
      rw [this]; infer_instance
    · exact iIndepFun_pi (fun i => aemeasurable_id)
  have := h.isGaussian_map
  simpa using this

lemma integrable_one_add_norm_pow (N p : ℕ) :
    Integrable (fun z : Fin N → ℝ => (1 + ‖z‖) ^ p) (gpi N) := by
  by_cases hp : p = 0
  · subst hp; simp
  have h1 := IsGaussian.memLp_id (gpi N) (p : ℝ≥0∞) (ENNReal.natCast_ne_top p)
  have h1' : MemLp (fun z : Fin N → ℝ => ‖z‖) (p : ℝ≥0∞) (gpi N) := h1.norm
  have h2 : MemLp (fun z : Fin N → ℝ => 1 + ‖z‖) (p : ℝ≥0∞) (gpi N) :=
    (memLp_const (1:ℝ)).add h1'
  have := h2.integrable_norm_pow hp
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖z‖)]

lemma integrable_of_poly {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : AEStronglyMeasurable f (gpi N))
    {C : ℝ} {k : ℕ} (hb : ∀ z, |f z| ≤ C * (1 + ‖z‖) ^ k) : Integrable f (gpi N) :=
  ((integrable_one_add_norm_pow N k).const_mul C).mono' hf
    (Eventually.of_forall fun z => by simpa using hb z)


lemma dstein_pi {N : ℕ} (i j : Fin N) {F Fi Fij : (Fin N → ℝ) → ℝ}
    (hFi : ∀ z, HasDerivAt (fun x => F (Function.update z i x)) (Fi z) (z i))
    (hFij : ∀ z, HasDerivAt (fun x => Fi (Function.update z j x)) (Fij z) (z j))
    (hFc : Continuous F) (hFic : Continuous Fi) (hFijc : Continuous Fij)
    {C : ℝ} {p : ℕ} (hb : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ p ∧ |Fi z| ≤ C * (1 + ‖z‖) ^ p ∧
      |Fij z| ≤ C * (1 + ‖z‖) ^ p) :
    ∫ z, (z i * z j - if i = j then 1 else 0) * F z ∂(gpi N) = ∫ z, Fij z ∂(gpi N) := by
  have hz : ∀ (k : Fin N) (z : Fin N → ℝ), |z k| ≤ 1 + ‖z‖ := fun k z => by
    have := norm_le_pi_norm z k
    rw [Real.norm_eq_abs] at this; linarith [norm_nonneg z]
  have hpow : ∀ z : Fin N → ℝ, (1 : ℝ) ≤ 1 + ‖z‖ := fun z => by linarith [norm_nonneg z]
  have iF : Integrable F (gpi N) := integrable_of_poly hFc.aestronglyMeasurable (fun z => (hb z).1)
  have iFi : Integrable Fi (gpi N) :=
    integrable_of_poly hFic.aestronglyMeasurable (fun z => (hb z).2.1)
  have iFij : Integrable Fij (gpi N) :=
    integrable_of_poly hFijc.aestronglyMeasurable (fun z => (hb z).2.2)
  have hC : 0 ≤ C := by
    have := (hb 0).1
    have h0 : (0 : ℝ) ≤ (1 + ‖(0 : Fin N → ℝ)‖) ^ p := by positivity
    by_contra hneg
    push Not at hneg
    have : C * (1 + ‖(0 : Fin N → ℝ)‖) ^ p < 0 ∨ (1 + ‖(0 : Fin N → ℝ)‖) ^ p = 0 := by
      rcases h0.lt_or_eq with h | h
      · left; exact mul_neg_of_neg_of_pos hneg h
      · right; exact h.symm
    rcases this with h | h
    · linarith [abs_nonneg (F 0)]
    · simp at h
  -- integrability of z_j * F, z_i * z_j * F, z_j * Fi
  have iJF : Integrable (fun z => z j * F z) (gpi N) :=
    integrable_of_poly ((measurable_pi_apply j).aestronglyMeasurable.mul hFc.aestronglyMeasurable)
      (C := C) (k := p + 1) (fun z => by
        rw [abs_mul, pow_succ]
        calc |z j| * |F z| ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ p) :=
              mul_le_mul (hz j z) (hb z).1 (abs_nonneg _) (by linarith [norm_nonneg z])
          _ = C * ((1 + ‖z‖) ^ p * (1 + ‖z‖)) := by ring)
  have iIJF : Integrable (fun z => z i * (z j * F z)) (gpi N) :=
    integrable_of_poly ((measurable_pi_apply i).aestronglyMeasurable.mul iJF.aestronglyMeasurable)
      (C := C) (k := p + 2) (fun z => by
        rw [abs_mul, abs_mul, pow_succ, pow_succ]
        calc |z i| * (|z j| * |F z|) ≤ (1 + ‖z‖) * ((1 + ‖z‖) * (C * (1 + ‖z‖) ^ p)) :=
              mul_le_mul (hz i z) (mul_le_mul (hz j z) (hb z).1 (abs_nonneg _)
                (by linarith [norm_nonneg z])) (by positivity) (by linarith [norm_nonneg z])
          _ = C * ((1 + ‖z‖) ^ p * (1 + ‖z‖) * (1 + ‖z‖)) := by ring)
  have iJFi : Integrable (fun z => z j * Fi z) (gpi N) :=
    integrable_of_poly ((measurable_pi_apply j).aestronglyMeasurable.mul hFic.aestronglyMeasurable)
      (C := C) (k := p + 1) (fun z => by
        rw [abs_mul, pow_succ]
        calc |z j| * |Fi z| ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ p) :=
              mul_le_mul (hz j z) (hb z).2.1 (abs_nonneg _) (by linarith [norm_nonneg z])
          _ = C * ((1 + ‖z‖) ^ p * (1 + ‖z‖)) := by ring)
  -- step 1
  have step1 : ∫ z, z i * (z j * F z) ∂(gpi N) =
      ∫ z, ((if j = i then 1 else 0) * F z + z j * Fi z) ∂(gpi N) := by
    refine stein_pi i (F := fun z => z j * F z)
      (F' := fun z => (if j = i then 1 else 0) * F z + z j * Fi z) (fun z => ?_) iJF iIJF ?_
    · have h1 : HasDerivAt (fun x => (Function.update z i x) j) (if j = i then 1 else 0) (z i) := by
        by_cases h : j = i
        · subst h
          convert hasDerivAt_id (z j) using 1
          · ext x; simp
          · simp
        · simp only [h, ite_false]
          have : (fun x => (Function.update z i x) j) = fun _ => z j := by
            ext x; simp [Function.update_of_ne h]
          rw [this]; exact hasDerivAt_const _ _
      have h2 := h1.mul (hFi z)
      convert h2 using 1
      simp
    · exact (iF.const_mul _).add iJFi
  have step2 : ∫ z, z j * Fi z ∂(gpi N) = ∫ z, Fij z ∂(gpi N) :=
    stein_pi j (F := Fi) (F' := Fij) hFij iFi iJFi iFij
  have e1 : ∫ z, (z i * z j - if i = j then 1 else 0) * F z ∂(gpi N) =
      ∫ z, z i * (z j * F z) ∂(gpi N) - (if i = j then 1 else 0) * ∫ z, F z ∂(gpi N) := by
    rw [← integral_const_mul, ← integral_sub iIJF (iF.const_mul _)]
    congr 1; ext z; ring
  rw [e1, step1, integral_add (iF.const_mul _) iJFi, integral_const_mul, step2]
  by_cases h : i = j
  · subst h; simp
  · have : ¬ (j = i) := fun h' => h h'.symm
    simp [h, this]


section FiniteStage
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma hasDerivAt_iter {Φ : B → ℝ} {k : ℕ} (hΦ : ContDiff ℝ (k + 1) Φ) {N : ℕ}
    (T : (Fin N → ℝ) →L[ℝ] B) (z : Fin N → ℝ) (i : Fin N) (v : Fin k → B) :
    HasDerivAt (fun x => iteratedFDeriv ℝ k Φ (T (Function.update z i x)) v)
      (iteratedFDeriv ℝ (k + 1) Φ (T z) (Fin.cons (T (Pi.single i 1)) v)) (z i) := by
  have hu : HasDerivAt (fun x => T (Function.update z i x)) (T (Pi.single i 1)) (z i) := by
    have h1 := hasDerivAt_update z i (z i)
    have h2 := T.hasFDerivAt.comp_hasDerivAt (z i) h1
    exact h2
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ k Φ) (T z) :=
    (hΦ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) (T z)
  have hu' : HasDerivAt (fun x => T (Function.update z i x)) (T (Pi.single i 1)) (z i) := hu
  have hz : T (Function.update z i (z i)) = T z := by rw [Function.update_eq_self]
  have hF := hD.hasFDerivAt.continuousMultilinear_apply_const v
  rw [← hz] at hF
  have h3 := hF.comp_hasDerivAt (z i) hu'
  rw [hz] at h3
  have := iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := Φ) (x := T z)
    (Fin.cons (T (Pi.single i 1)) v : Fin (k + 1) → B)
  convert h3 using 1
  all_goals first | rfl | simpa using this


lemma iter2_swap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : B → F}
    (hΦ : ContDiff ℝ 2 Φ) (y a b : B) :
    iteratedFDeriv ℝ 2 Φ y ![a, b] = iteratedFDeriv ℝ 2 Φ y ![b, a] := by
  have h := (hΦ.contDiffAt (x := y)).isSymmSndFDerivAt (by simp)
  simp only [iteratedFDeriv_two_apply]
  exact h.eq a b

lemma iter3_swap23 {Φ : B → ℝ} (hΦ : ContDiff ℝ 3 Φ) (y u a b : B) :
    iteratedFDeriv ℝ 3 Φ y ![u, a, b] = iteratedFDeriv ℝ 3 Φ y ![u, b, a] := by
  have hd : ∀ v : Fin 2 → B, fderiv ℝ (fun y' => iteratedFDeriv ℝ 2 Φ y' v) y =
      (fderiv ℝ (iteratedFDeriv ℝ 2 Φ) y).flipMultilinear v := fun v =>
    fderiv_continuousMultilinear_apply_const
      ((hΦ.differentiable_iteratedFDeriv (by norm_num)) y) v
  have h1 : ∀ a b : B, iteratedFDeriv ℝ 3 Φ y ![u, a, b] =
      fderiv ℝ (fun y' => iteratedFDeriv ℝ 2 Φ y' ![a, b]) y u := by
    intro a b
    rw [hd]
    have := iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := Φ) (x := y) (n := 2) ![u, a, b]
    simpa using this
  rw [h1, h1]
  congr 2
  ext y'
  exact iter2_swap (hΦ.of_le (by norm_num)) y' a b

lemma iter3_swap12 {Φ : B → ℝ} (hΦ : ContDiff ℝ 3 Φ) (y u a b : B) :
    iteratedFDeriv ℝ 3 Φ y ![u, a, b] = iteratedFDeriv ℝ 3 Φ y ![a, u, b] := by
  have h1 : ∀ u a b : B, iteratedFDeriv ℝ 3 Φ y ![u, a, b] =
      iteratedFDeriv ℝ 2 (fun y => fderiv ℝ Φ y) y ![u, a] b := by
    intro u a b
    have := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := Φ) (x := y) (n := 2) ![u, a, b]
    have hi : Fin.init ![u, a, b] = ![u, a] := by ext i; fin_cases i <;> rfl
    rw [hi] at this
    simpa using this
  rw [h1, h1]
  have hd : ContDiff ℝ 2 (fun y => fderiv ℝ Φ y) := hΦ.fderiv_right (by norm_num)
  have := iter2_swap hd y u a
  rw [this]


lemma iter3_cyc {Φ : B → ℝ} (hΦ : ContDiff ℝ 3 Φ) (y a p q : B) :
    iteratedFDeriv ℝ 3 Φ y ![a, p, q] = iteratedFDeriv ℝ 3 Φ y ![p, q, a] := by
  rw [iter3_swap12 hΦ y a p q, iter3_swap23 hΦ y p a q]

lemma iter3_rev {Φ : B → ℝ} (hΦ : ContDiff ℝ 3 Φ) (y a b c : B) :
    iteratedFDeriv ℝ 3 Φ y ![b, a, c] = iteratedFDeriv ℝ 3 Φ y ![c, a, b] := by
  rw [iter3_swap23 hΦ y b a c, iter3_swap12 hΦ y b c a, iter3_swap23 hΦ y c b a]

section Tri
variable (M : B [×3]→L[ℝ] ℝ) (c : B)

lemma tri_add2 (x x' y : B) : M ![c, x + x', y] = M ![c, x, y] + M ![c, x', y] := by
  have h := M.map_update_add ![c, x, y] 1 x x'
  have e : ∀ z : B, Function.update (![c, x, y] : Fin 3 → B) 1 z = ![c, z, y] := by
    intro z; ext i; fin_cases i <;> simp [Function.update]
  simpa [e] using h

lemma tri_add3 (x y y' : B) : M ![c, x, y + y'] = M ![c, x, y] + M ![c, x, y'] := by
  have h := M.map_update_add ![c, x, y] 2 y y'
  have e : ∀ z : B, Function.update (![c, x, y] : Fin 3 → B) 2 z = ![c, x, z] := by
    intro z; ext i; fin_cases i <;> simp [Function.update]
  simpa [e] using h

lemma tri_smul2 (t : ℝ) (x y : B) : M ![c, t • x, y] = t * M ![c, x, y] := by
  have h := M.map_update_smul ![c, x, y] 1 t x
  have e : ∀ z : B, Function.update (![c, x, y] : Fin 3 → B) 1 z = ![c, z, y] := by
    intro z; ext i; fin_cases i <;> simp [Function.update]
  simpa [e] using h

lemma tri_smul3 (t : ℝ) (x y : B) : M ![c, x, t • y] = t * M ![c, x, y] := by
  have h := M.map_update_smul ![c, x, y] 2 t y
  have e : ∀ z : B, Function.update (![c, x, y] : Fin 3 → B) 2 z = ![c, x, z] := by
    intro z; ext i; fin_cases i <;> simp [Function.update]
  simpa [e] using h

lemma tri_expand (a w b v : B) (t s : ℝ) :
    M ![c, a + t • w, b + s • v] =
      M ![c, a, b] + s * M ![c, a, v] + t * M ![c, w, b] + t * s * M ![c, w, v] := by
  rw [tri_add2, tri_add3, tri_add3, tri_smul2, tri_smul2, tri_smul3, tri_smul3]
  ring

end Tri


/-- The linear map `z ↦ ∑ z_k • w_k`. -/
def Tmap {N : ℕ} (w : Fin N → B) : (Fin N → ℝ) →L[ℝ] B :=
  ∑ k, (ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ).smulRight (w k)

lemma Tmap_apply {N : ℕ} (w : Fin N → B) (z : Fin N → ℝ) : Tmap w z = ∑ k, z k • w k := by
  simp [Tmap]

lemma Tmap_single {N : ℕ} (w : Fin N → B) (i : Fin N) : Tmap w (Pi.single i 1) = w i := by
  rw [Tmap_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Pi.single_apply, hk]
  · simp

lemma Tmap_update {N : ℕ} (w : Fin N → B) (z : Fin N → ℝ) (i : Fin N) (x : ℝ) :
    Tmap w (Function.update z i x) = Tmap w z + (x - z i) • w i := by
  have : Function.update z i x = z + (x - z i) • Pi.single i 1 := by
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Function.update_of_ne h, Pi.single_apply, h]
  rw [this, map_add, map_smul, Tmap_single]

lemma norm_Tmap_le {N : ℕ} (w : Fin N → B) (z : Fin N → ℝ) :
    ‖Tmap w z‖ ≤ (∑ k, ‖w k‖) * ‖z‖ := by
  rw [Tmap_apply]
  calc ‖∑ k, z k • w k‖ ≤ ∑ k, ‖z k • w k‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖z‖ * ‖w k‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm z k) (norm_nonneg _)
    _ = (∑ k, ‖w k‖) * ‖z‖ := by rw [← Finset.mul_sum]; ring

section Tri2
variable (M : B [×3]→L[ℝ] ℝ) (c : B)

lemma hasDerivAt_quad (a w : B) (x0 : ℝ) :
    HasDerivAt (fun x => M ![c, a + (x - x0) • w, a + (x - x0) • w])
      (M ![c, w, a] + M ![c, a, w]) x0 := by
  have e : (fun x => M ![c, a + (x - x0) • w, a + (x - x0) • w]) = fun x =>
      M ![c, a, a] + (x - x0) * M ![c, a, w] + (x - x0) * M ![c, w, a] +
        (x - x0) * (x - x0) * M ![c, w, w] := by
    ext x; exact tri_expand M c a w a w (x - x0) (x - x0)
  rw [e]
  have h1 : HasDerivAt (fun x : ℝ => x - x0) 1 x0 := (hasDerivAt_id x0).sub_const x0
  have h2 := (((hasDerivAt_const x0 (M ![c, a, a])).add (h1.mul_const (M ![c, a, w]))).add
    (h1.mul_const (M ![c, w, a]))).add ((h1.mul h1).mul_const (M ![c, w, w]))
  convert h2 using 1
  simp; ring

lemma hasDerivAt_lin3 (u a w : B) (x0 : ℝ) :
    HasDerivAt (fun x => M ![c, u, a + (x - x0) • w]) (M ![c, u, w]) x0 := by
  have e : (fun x => M ![c, u, a + (x - x0) • w]) = fun x =>
      M ![c, u, a] + (x - x0) * M ![c, u, w] := by
    ext x; rw [tri_add3, tri_smul3]
  rw [e]
  have h1 : HasDerivAt (fun x : ℝ => x - x0) 1 x0 := (hasDerivAt_id x0).sub_const x0
  convert (hasDerivAt_const x0 (M ![c, u, a])).add (h1.mul_const (M ![c, u, w])) using 1
  simp

lemma hasDerivAt_lin2 (u a w : B) (x0 : ℝ) :
    HasDerivAt (fun x => M ![c, a + (x - x0) • w, u]) (M ![c, w, u]) x0 := by
  have e : (fun x => M ![c, a + (x - x0) • w, u]) = fun x =>
      M ![c, a, u] + (x - x0) * M ![c, w, u] := by
    ext x; rw [tri_add2, tri_smul2]
  rw [e]
  have h1 : HasDerivAt (fun x : ℝ => x - x0) 1 x0 := (hasDerivAt_id x0).sub_const x0
  convert (hasDerivAt_const x0 (M ![c, a, u])).add (h1.mul_const (M ![c, w, u])) using 1
  simp

end Tri2

end FiniteStage

end Aux_Hlp1

section Aux_Hlp2
open ProbabilityTheory

section OmegaStage
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

/-- The coordinate vector `(ξ_0, …, ξ_{N-1})`. -/
def Zvec (ξ : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : Fin N → ℝ := fun i => ξ i ω

lemma aemeasurable_Zvec (hξ : IsStdGaussianSeq P ξ) (N : ℕ) : AEMeasurable (Zvec ξ N) P :=
  AEMeasurable.of_eval fun i => hξ.aemeasurable i

lemma map_Zvec (hξ : IsStdGaussianSeq P ξ) (N : ℕ) : P.map (Zvec ξ N) = gpi N :=
  law_vec hξ N

lemma integral_comp_Zvec (hξ : IsStdGaussianSeq P ξ) (N : ℕ) {g : (Fin N → ℝ) → ℝ}
    (hg : Continuous g) : ∫ ω, g (Zvec ξ N ω) ∂P = ∫ z, g z ∂(gpi N) := by
  rw [← map_Zvec hξ N]
  exact (integral_map (aemeasurable_Zvec hξ N) hg.aestronglyMeasurable).symm

lemma integrable_comp_Zvec (hξ : IsStdGaussianSeq P ξ) (N : ℕ) {g : (Fin N → ℝ) → ℝ}
    (hg : Continuous g) {C : ℝ} {k : ℕ} (hb : ∀ z, |g z| ≤ C * (1 + ‖z‖) ^ k) :
    Integrable (fun ω => g (Zvec ξ N ω)) P := by
  have h1 : Integrable g (gpi N) := integrable_of_poly hg.aestronglyMeasurable hb
  rw [← map_Zvec hξ N] at h1
  exact (integrable_map_measure hg.aestronglyMeasurable (aemeasurable_Zvec hξ N)).1 h1

lemma stein_Z (hξ : IsStdGaussianSeq P ξ) {N : ℕ} (i : Fin N) {F F' : (Fin N → ℝ) → ℝ}
    (hd : ∀ z, HasDerivAt (fun x => F (Function.update z i x)) (F' z) (z i))
    (hFc : Continuous F) (hF'c : Continuous F') {C : ℝ} {p : ℕ}
    (hb : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ p ∧ |F' z| ≤ C * (1 + ‖z‖) ^ p) :
    ∫ ω, ξ i ω * F (Zvec ξ N ω) ∂P = ∫ ω, F' (Zvec ξ N ω) ∂P := by
  have e1 := integral_comp_Zvec hξ N (g := fun z => z i * F z)
    ((continuous_apply i).mul hFc)
  have e2 := integral_comp_Zvec hξ N hF'c
  have hz : ∀ z : Fin N → ℝ, |z i| ≤ 1 + ‖z‖ := fun z => by
    have := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at this; linarith [norm_nonneg z]
  have iF : Integrable F (gpi N) := integrable_of_poly hFc.aestronglyMeasurable (fun z => (hb z).1)
  have iF' : Integrable F' (gpi N) :=
    integrable_of_poly hF'c.aestronglyMeasurable (fun z => (hb z).2)
  have iZF : Integrable (fun z => z i * F z) (gpi N) :=
    integrable_of_poly ((continuous_apply i).mul hFc).aestronglyMeasurable (C := C) (k := p + 1)
      (fun z => by
        rw [abs_mul, pow_succ]
        calc |z i| * |F z| ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ p) :=
              mul_le_mul (hz z) (hb z).1 (abs_nonneg _) (by linarith [norm_nonneg z])
          _ = C * ((1 + ‖z‖) ^ p * (1 + ‖z‖)) := by ring)
  have := stein_pi i hd iF iZF iF'
  show ∫ ω, (fun z => z i * F z) (Zvec ξ N ω) ∂P = _
  rw [e1, e2]
  exact this

lemma dstein_Z (hξ : IsStdGaussianSeq P ξ) {N : ℕ} (i j : Fin N) {F Fi Fij : (Fin N → ℝ) → ℝ}
    (hFi : ∀ z, HasDerivAt (fun x => F (Function.update z i x)) (Fi z) (z i))
    (hFij : ∀ z, HasDerivAt (fun x => Fi (Function.update z j x)) (Fij z) (z j))
    (hFc : Continuous F) (hFic : Continuous Fi) (hFijc : Continuous Fij)
    {C : ℝ} {p : ℕ} (hb : ∀ z, |F z| ≤ C * (1 + ‖z‖) ^ p ∧ |Fi z| ≤ C * (1 + ‖z‖) ^ p ∧
      |Fij z| ≤ C * (1 + ‖z‖) ^ p) :
    ∫ ω, (ξ i ω * ξ j ω - if i = j then 1 else 0) * F (Zvec ξ N ω) ∂P =
      ∫ ω, Fij (Zvec ξ N ω) ∂P := by
  have e1 := integral_comp_Zvec hξ N (g := fun z => (z i * z j - if i = j then 1 else 0) * F z)
    ((((continuous_apply i).mul (continuous_apply j)).sub continuous_const).mul hFc)
  have e2 := integral_comp_Zvec hξ N hFijc
  show ∫ ω, (fun z => (z i * z j - if i = j then 1 else 0) * F z) (Zvec ξ N ω) ∂P = _
  rw [e1, e2]
  exact dstein_pi i j hFi hFij hFc hFic hFijc hb

end OmegaStage

end Aux_Hlp2

section Aux_Hlp3
open ProbabilityTheory

section PhiStage
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

lemma memCb_bound {Φ : B → ℝ} {k : ℕ} (hΦ : MemCb k Φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ K := by
  have h : ∀ j : Fin (k + 1), ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ K := fun j => by
    obtain ⟨K, hK⟩ := hΦ.2 j (by omega)
    exact ⟨K, fun x => hK ⟨x, rfl⟩⟩
  choose Kf hKf using h
  refine ⟨∑ j, |Kf j|, Finset.sum_nonneg fun j _ => abs_nonneg _, fun j hj x => ?_⟩
  have hj' : j < k + 1 := by omega
  calc ‖iteratedFDeriv ℝ j Φ x‖ ≤ Kf ⟨j, hj'⟩ := hKf ⟨j, hj'⟩ x
    _ ≤ |Kf ⟨j, hj'⟩| := le_abs_self _
    _ ≤ ∑ j, |Kf j| :=
        Finset.single_le_sum (f := fun j => |Kf j|) (fun j _ => abs_nonneg _) (Finset.mem_univ _)

lemma abs_iter_le {Φ : B → ℝ} {K : ℝ} {j : ℕ} {y : B} (h : ‖iteratedFDeriv ℝ j Φ y‖ ≤ K)
    (v : Fin j → B) : |iteratedFDeriv ℝ j Φ y v| ≤ K * ∏ i, ‖v i‖ := by
  have := (iteratedFDeriv ℝ j Φ y).le_opNorm v
  rw [Real.norm_eq_abs] at this
  exact this.trans (mul_le_mul_of_nonneg_right h (Finset.prod_nonneg fun i _ => norm_nonneg _))

lemma le_prod_one_add (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ≤ (1 + a) * (1 + b) * (1 + c) ∧ a * b ≤ (1 + a) * (1 + b) * (1 + c) ∧
      a * b * c ≤ (1 + a) * (1 + b) * (1 + c) := by
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc,
    mul_nonneg (mul_nonneg ha hb) hc]

lemma fin2_termA (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (cc : B) (i j : Fin N) :
    ∫ ω, (ξ i ω * ξ j ω - if i = j then 1 else 0) * fderiv ℝ Φ (Tmap w (Zvec ξ N ω)) cc ∂P =
      ∫ ω, iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N ω)) ![cc, w i, w j] ∂P := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  set T := Tmap w with hT
  have hcont : ∀ k ≤ 3, ∀ v : Fin k → B, Continuous fun z => iteratedFDeriv ℝ k Φ (T z) v := by
    intro k hk v
    have h1 : Continuous (iteratedFDeriv ℝ k Φ) :=
      hΦ3.continuous_iteratedFDeriv (by exact_mod_cast hk)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => B) ℝ v).continuous.comp
      (h1.comp T.continuous)
  have key := dstein_Z hξ i j (N := N) (P := P)
    (F := fun z => iteratedFDeriv ℝ 1 Φ (T z) ![cc])
    (Fi := fun z => iteratedFDeriv ℝ 2 Φ (T z) ![w i, cc])
    (Fij := fun z => iteratedFDeriv ℝ 3 Φ (T z) ![w j, w i, cc])
    (fun z => by
      have := hasDerivAt_iter (Φ := Φ) (k := 1) (hΦ3.of_le (by norm_num)) T z i ![cc]
      rw [Tmap_single] at this
      exact this)
    (fun z => by
      have := hasDerivAt_iter (Φ := Φ) (k := 2) (hΦ3.of_le (by norm_num)) T z j ![w i, cc]
      rw [Tmap_single] at this
      exact this)
    (hcont 1 (by norm_num) _) (hcont 2 (by norm_num) _) (hcont 3 (le_refl _) _)
    (C := K * (1 + ‖cc‖) * (1 + ‖w i‖) * (1 + ‖w j‖)) (p := 0) (fun z => by
      have b1 := abs_iter_le (hK 1 (by norm_num) (T z)) ![cc]
      have b2 := abs_iter_le (hK 2 (by norm_num) (T z)) ![w i, cc]
      have b3 := abs_iter_le (hK 3 (by norm_num) (T z)) ![w j, w i, cc]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, mul_one, Fin.succ_zero_eq_one] at b1 b2 b3
      simp only [pow_zero, mul_one]
      obtain ⟨l1, l2, l3⟩ := le_prod_one_add ‖cc‖ ‖w i‖ ‖w j‖ (norm_nonneg _) (norm_nonneg _)
        (norm_nonneg _)
      have e1 : K * ‖cc‖ ≤ K * (1 + ‖cc‖) * (1 + ‖w i‖) * (1 + ‖w j‖) := by
        calc K * ‖cc‖ ≤ K * ((1 + ‖cc‖) * (1 + ‖w i‖) * (1 + ‖w j‖)) :=
              mul_le_mul_of_nonneg_left l1 hK0
          _ = _ := by ring
      have e2 : K * (‖w i‖ * ‖cc‖) ≤ K * (1 + ‖cc‖) * (1 + ‖w i‖) * (1 + ‖w j‖) := by
        calc K * (‖w i‖ * ‖cc‖) = K * (‖cc‖ * ‖w i‖) := by ring
          _ ≤ K * ((1 + ‖cc‖) * (1 + ‖w i‖) * (1 + ‖w j‖)) :=
              mul_le_mul_of_nonneg_left l2 hK0
          _ = _ := by ring
      have e3 : K * (‖w j‖ * (‖w i‖ * ‖cc‖)) ≤ K * (1 + ‖cc‖) * (1 + ‖w i‖) * (1 + ‖w j‖) := by
        calc K * (‖w j‖ * (‖w i‖ * ‖cc‖)) = K * (‖cc‖ * ‖w i‖ * ‖w j‖) := by ring
          _ ≤ K * ((1 + ‖cc‖) * (1 + ‖w i‖) * (1 + ‖w j‖)) :=
              mul_le_mul_of_nonneg_left l3 hK0
          _ = _ := by ring
      exact ⟨b1.trans e1, b2.trans e2, b3.trans e3⟩)
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero] at key
  rw [key]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  exact iter3_rev hΦ3 _ (w i) (w j) cc


lemma abs_tri_le (M : B [×3]→L[ℝ] ℝ) (a b c : B) : |M ![a, b, c]| ≤ ‖M‖ * (‖a‖ * ‖b‖ * ‖c‖) := by
  have := M.le_opNorm ![a, b, c]
  rw [Real.norm_eq_abs] at this
  simpa [Fin.prod_univ_succ, mul_assoc] using this

lemma continuous_tri (M : B [×3]→L[ℝ] ℝ) {X : Type*} [TopologicalSpace X] {f g h : X → B}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun x => M ![f x, g x, h x] := by
  refine M.cont.comp (continuous_pi fun k => ?_)
  fin_cases k <;> simpa

lemma fin2_termB (hξ : IsStdGaussianSeq P ξ) {N : ℕ} (w : Fin N → B) (M : B [×3]→L[ℝ] ℝ)
    (cc : B) (i j : Fin N) :
    ∫ ω, (ξ i ω * ξ j ω - if i = j then 1 else 0) *
        M ![cc, Tmap w (Zvec ξ N ω), Tmap w (Zvec ξ N ω)] ∂P =
      M ![cc, w i, w j] + M ![cc, w j, w i] := by
  set T := Tmap w with hT
  set A : ℝ := ∑ k, ‖w k‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => norm_nonneg _
  have key := dstein_Z hξ i j (N := N) (P := P)
    (F := fun z => M ![cc, T z, T z])
    (Fi := fun z => M ![cc, w i, T z] + M ![cc, T z, w i])
    (Fij := fun _ => M ![cc, w i, w j] + M ![cc, w j, w i])
    (fun z => by
      have := hasDerivAt_quad M cc (T z) (w i) (z i)
      simp only [hT, Tmap_update]
      exact this)
    (fun z => by
      have h1 := hasDerivAt_lin3 M cc (w i) (T z) (w j) (z j)
      have h2 := hasDerivAt_lin2 M cc (w i) (T z) (w j) (z j)
      simp only [hT, Tmap_update]
      exact h1.add h2)
    (continuous_tri M continuous_const T.continuous T.continuous)
    ((continuous_tri M continuous_const continuous_const T.continuous).add
      (continuous_tri M continuous_const T.continuous continuous_const))
    continuous_const
    (C := ‖M‖ * ‖cc‖ * (A ^ 2 + 2 * ‖w i‖ * A + 2 * ‖w i‖ * ‖w j‖)) (p := 2) (fun z => by
      have hz0 := norm_nonneg z
      have hT' : ‖T z‖ ≤ A * ‖z‖ := by rw [hT, hA]; rw [mul_comm]; exact (by
        have := norm_Tmap_le w z; linarith)
      have hTn := norm_nonneg (T z)
      have b1 := abs_tri_le M cc (T z) (T z)
      have b2 := abs_tri_le M cc (w i) (T z)
      have b3 := abs_tri_le M cc (T z) (w i)
      have b4 := abs_tri_le M cc (w i) (w j)
      have b5 := abs_tri_le M cc (w j) (w i)
      have hM := norm_nonneg M
      have hc := norm_nonneg cc
      have hwi := norm_nonneg (w i)
      have hwj := norm_nonneg (w j)
      set S : ℝ := (1 + ‖z‖) ^ 2 with hS
      have hs : ‖z‖ ≤ S := by rw [hS]; nlinarith
      have hs2 : ‖z‖ ^ 2 ≤ S := by rw [hS]; nlinarith
      have hs1 : (1 : ℝ) ≤ S := by rw [hS]; nlinarith
      have hS0 : 0 ≤ S := by linarith
      have hMc : 0 ≤ ‖M‖ * ‖cc‖ := mul_nonneg hM hc
      set q : ℝ := A ^ 2 + 2 * ‖w i‖ * A + 2 * ‖w i‖ * ‖w j‖ with hq
      have hq1 : A ^ 2 * S ≤ q * S := by
        apply mul_le_mul_of_nonneg_right _ hS0
        rw [hq]; nlinarith [mul_nonneg hwi hA0, mul_nonneg hwi hwj]
      have hq2 : 2 * ‖w i‖ * A * S ≤ q * S := by
        apply mul_le_mul_of_nonneg_right _ hS0
        rw [hq]; nlinarith [sq_nonneg A, mul_nonneg hwi hwj]
      have hq3 : 2 * ‖w i‖ * ‖w j‖ * S ≤ q * S := by
        apply mul_le_mul_of_nonneg_right _ hS0
        rw [hq]; nlinarith [sq_nonneg A, mul_nonneg hwi hA0]
      refine ⟨?_, ?_, ?_⟩
      · calc |M ![cc, T z, T z]| ≤ ‖M‖ * (‖cc‖ * ‖T z‖ * ‖T z‖) := b1
          _ ≤ ‖M‖ * (‖cc‖ * (A * ‖z‖) * (A * ‖z‖)) := by gcongr
          _ = ‖M‖ * ‖cc‖ * (A ^ 2 * ‖z‖ ^ 2) := by ring
          _ ≤ ‖M‖ * ‖cc‖ * (A ^ 2 * S) := by
              apply mul_le_mul_of_nonneg_left _ hMc
              exact mul_le_mul_of_nonneg_left hs2 (sq_nonneg A)
          _ ≤ ‖M‖ * ‖cc‖ * (q * S) := mul_le_mul_of_nonneg_left hq1 hMc
          _ = _ := by ring
      · calc |M ![cc, w i, T z] + M ![cc, T z, w i]|
            ≤ |M ![cc, w i, T z]| + |M ![cc, T z, w i]| := abs_add_le _ _
          _ ≤ ‖M‖ * (‖cc‖ * ‖w i‖ * ‖T z‖) + ‖M‖ * (‖cc‖ * ‖T z‖ * ‖w i‖) := add_le_add b2 b3
          _ ≤ ‖M‖ * (‖cc‖ * ‖w i‖ * (A * ‖z‖)) + ‖M‖ * (‖cc‖ * (A * ‖z‖) * ‖w i‖) := by gcongr
          _ = ‖M‖ * ‖cc‖ * (2 * ‖w i‖ * A * ‖z‖) := by ring
          _ ≤ ‖M‖ * ‖cc‖ * (2 * ‖w i‖ * A * S) := by
              apply mul_le_mul_of_nonneg_left _ hMc
              exact mul_le_mul_of_nonneg_left hs (by positivity)
          _ ≤ ‖M‖ * ‖cc‖ * (q * S) := mul_le_mul_of_nonneg_left hq2 hMc
          _ = _ := by ring
      · calc |M ![cc, w i, w j] + M ![cc, w j, w i]|
            ≤ |M ![cc, w i, w j]| + |M ![cc, w j, w i]| := abs_add_le _ _
          _ ≤ ‖M‖ * (‖cc‖ * ‖w i‖ * ‖w j‖) + ‖M‖ * (‖cc‖ * ‖w j‖ * ‖w i‖) := add_le_add b4 b5
          _ = ‖M‖ * ‖cc‖ * (2 * ‖w i‖ * ‖w j‖) := by ring
          _ ≤ ‖M‖ * ‖cc‖ * (2 * ‖w i‖ * ‖w j‖ * S) := by
              apply mul_le_mul_of_nonneg_left _ hMc
              exact le_mul_of_one_le_right (by positivity) hs1
          _ ≤ ‖M‖ * ‖cc‖ * (q * S) := mul_le_mul_of_nonneg_left hq3 hMc
          _ = _ := by ring)
  simpa using key

end PhiStage

end Aux_Hlp3

section Aux_Hlp4
open ProbabilityTheory

section Assemble2
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

/-- The finite centered quadratic polynomial `∑ (ξ_i ξ_j - δ_ij) c_ij`. -/
def Dfin (ξ : ℕ → Ω → ℝ) (N : ℕ) (c : Fin N → Fin N → B) (ω : Ω) : B :=
  ∑ i : Fin N, ∑ j : Fin N, (ξ i ω * ξ j ω - if i = j then 1 else 0) • c i j

lemma abs_zz_le {N : ℕ} (i j : Fin N) (z : Fin N → ℝ) :
    |z i * z j - if i = j then 1 else 0| ≤ (1 + ‖z‖) ^ 2 := by
  have hi : |z i| ≤ ‖z‖ := by simpa using norm_le_pi_norm z i
  have hj : |z j| ≤ ‖z‖ := by simpa using norm_le_pi_norm z j
  have h0 := norm_nonneg z
  have : |z i * z j| ≤ ‖z‖ ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hi hj (abs_nonneg _) h0
  calc |z i * z j - if i = j then 1 else 0| ≤ |z i * z j| + |(if i = j then (1 : ℝ) else 0)| :=
        abs_sub _ _
    _ ≤ ‖z‖ ^ 2 + 1 := by
        refine add_le_add this ?_
        split_ifs <;> simp
    _ ≤ (1 + ‖z‖) ^ 2 := by nlinarith

lemma continuous_zz {N : ℕ} (i j : Fin N) :
    Continuous fun z : Fin N → ℝ => z i * z j - if i = j then (1 : ℝ) else 0 :=
  (((continuous_apply i).mul (continuous_apply j)).sub continuous_const)

lemma integrable_zz_quad (hξ : IsStdGaussianSeq P ξ) {N : ℕ} (w : Fin N → B)
    (M : B [×3]→L[ℝ] ℝ) (cc : B) (i j : Fin N) :
    Integrable (fun ω => (ξ i ω * ξ j ω - if i = j then 1 else 0) *
      M ![cc, Tmap w (Zvec ξ N ω), Tmap w (Zvec ξ N ω)]) P := by
  set T := Tmap w
  set A : ℝ := ∑ k, ‖w k‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => norm_nonneg _
  refine integrable_comp_Zvec hξ N (g := fun z => (z i * z j - if i = j then 1 else 0) *
      M ![cc, T z, T z]) ((continuous_zz i j).mul
        (continuous_tri M continuous_const T.continuous T.continuous))
    (C := ‖M‖ * ‖cc‖ * A ^ 2) (k := 4) (fun z => ?_)
  have hz0 := norm_nonneg z
  have hT' : ‖T z‖ ≤ A * ‖z‖ := by
    exact norm_Tmap_le w z
  have b1 := abs_tri_le M cc (T z) (T z)
  have hM := norm_nonneg M
  have hc := norm_nonneg cc
  have hTn := norm_nonneg (T z)
  rw [abs_mul]
  have e1 := abs_zz_le i j z
  have e2 : |M ![cc, T z, T z]| ≤ ‖M‖ * ‖cc‖ * A ^ 2 * (1 + ‖z‖) ^ 2 := by
    calc |M ![cc, T z, T z]| ≤ ‖M‖ * (‖cc‖ * ‖T z‖ * ‖T z‖) := b1
      _ ≤ ‖M‖ * (‖cc‖ * (A * ‖z‖) * (A * ‖z‖)) := by gcongr
      _ = ‖M‖ * ‖cc‖ * A ^ 2 * ‖z‖ ^ 2 := by ring
      _ ≤ ‖M‖ * ‖cc‖ * A ^ 2 * (1 + ‖z‖) ^ 2 := by
          gcongr; nlinarith
  calc |z i * z j - if i = j then 1 else 0| * |M ![cc, T z, T z]|
      ≤ (1 + ‖z‖) ^ 2 * (‖M‖ * ‖cc‖ * A ^ 2 * (1 + ‖z‖) ^ 2) :=
        mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
    _ = ‖M‖ * ‖cc‖ * A ^ 2 * (1 + ‖z‖) ^ 4 := by ring


lemma abs_fderiv_le {Φ : B → ℝ} {K : ℝ} (hK : ∀ y, ‖iteratedFDeriv ℝ 1 Φ y‖ ≤ K) (y cc : B) :
    |fderiv ℝ Φ y cc| ≤ K * ‖cc‖ := by
  have := abs_iter_le (hK y) ![cc]
  simpa using this

lemma integrable_termA (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (cc : B) (i j : Fin N) :
    Integrable (fun ω => (ξ i ω * ξ j ω - if i = j then 1 else 0) *
      fderiv ℝ Φ (Tmap w (Zvec ξ N ω)) cc) P := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  set T := Tmap w
  have hc : Continuous fun z => fderiv ℝ Φ (T z) cc :=
    (ContinuousLinearMap.apply ℝ ℝ cc).continuous.comp
      ((hΦ3.continuous_fderiv (by norm_num)).comp T.continuous)
  refine integrable_comp_Zvec hξ N (g := fun z => (z i * z j - if i = j then 1 else 0) *
      fderiv ℝ Φ (T z) cc) ((continuous_zz i j).mul hc) (C := K * ‖cc‖) (k := 2) (fun z => ?_)
  rw [abs_mul]
  calc |z i * z j - if i = j then 1 else 0| * |fderiv ℝ Φ (T z) cc|
      ≤ (1 + ‖z‖) ^ 2 * (K * ‖cc‖) :=
        mul_le_mul (abs_zz_le i j z) (abs_fderiv_le (fun y => hK 1 (by norm_num) y) _ _)
          (abs_nonneg _) (by positivity)
    _ = K * ‖cc‖ * (1 + ‖z‖) ^ 2 := by ring

lemma fin2_A (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (c : Fin N → Fin N → B) :
    ∫ ω, fderiv ℝ Φ (Tmap w (Zvec ξ N ω)) (Dfin ξ N c ω) ∂P =
      ∑ i : Fin N, ∑ j : Fin N, ∫ ω, iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N ω)) ![c i j, w i, w j] ∂P := by
  have e : ∀ ω, fderiv ℝ Φ (Tmap w (Zvec ξ N ω)) (Dfin ξ N c ω) =
      ∑ i : Fin N, ∑ j : Fin N, (ξ i ω * ξ j ω - if i = j then 1 else 0) *
        fderiv ℝ Φ (Tmap w (Zvec ξ N ω)) (c i j) := by
    intro ω
    simp only [Dfin, map_sum, map_smul, smul_eq_mul]
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_termA hξ hΦ w (c i j) i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => integrable_termA hξ hΦ w (c i j) i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact fin2_termA hξ hΦ w (c i j) i j


/-- the polynomial `Dfin` as a function of the coordinate vector -/
def Qfun {N : ℕ} (c : Fin N → Fin N → B) (z : Fin N → ℝ) : B :=
  ∑ i : Fin N, ∑ j : Fin N, (z i * z j - if i = j then 1 else 0) • c i j

lemma Dfin_eq (ξ : ℕ → Ω → ℝ) {N : ℕ} (c : Fin N → Fin N → B) (ω : Ω) :
    Dfin ξ N c ω = Qfun c (Zvec ξ N ω) := rfl

lemma continuous_Qfun {N : ℕ} (c : Fin N → Fin N → B) : Continuous (Qfun c) := by
  unfold Qfun
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_zz i j).smul continuous_const

lemma norm_Qfun_le {N : ℕ} (c : Fin N → Fin N → B) (z : Fin N → ℝ) :
    ‖Qfun c z‖ ≤ (∑ i : Fin N, ∑ j : Fin N, ‖c i j‖) * (1 + ‖z‖) ^ 2 := by
  unfold Qfun
  calc ‖∑ i : Fin N, ∑ j : Fin N, (z i * z j - if i = j then 1 else 0) • c i j‖
      ≤ ∑ i : Fin N, ‖∑ j : Fin N, (z i * z j - if i = j then 1 else 0) • c i j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, (1 + ‖z‖) ^ 2 * ‖c i j‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (abs_zz_le i j z) (norm_nonneg _)
    _ = (∑ i : Fin N, ∑ j : Fin N, ‖c i j‖) * (1 + ‖z‖) ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma integrable_prodB (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (c : Fin N → Fin N → B) :
    Integrable (fun p : Ω × Ω => iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N p.1))
      ![Dfin ξ N c p.2, Tmap w (Zvec ξ N p.2), Tmap w (Zvec ξ N p.2)]) (P.prod P) := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  set T := Tmap w with hT
  set A : ℝ := ∑ k, ‖w k‖ with hA
  set Cc : ℝ := ∑ i : Fin N, ∑ j : Fin N, ‖c i j‖ with hCc
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hcont3 : Continuous (iteratedFDeriv ℝ 3 Φ) :=
    hΦ3.continuous_iteratedFDeriv (by norm_num)
  let F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun q =>
    iteratedFDeriv ℝ 3 Φ (T q.1) ![Qfun c q.2, T q.2, T q.2]
  have hFc : Continuous F := by
    refine Continuous.eval (hcont3.comp (T.continuous.comp continuous_fst)) ?_
    refine continuous_pi fun k => ?_
    fin_cases k
    · exact (continuous_Qfun c).comp continuous_snd
    · exact T.continuous.comp continuous_snd
    · exact T.continuous.comp continuous_snd
  have hmeas : AEStronglyMeasurable (fun p : Ω × Ω => F (Zvec ξ N p.1, Zvec ξ N p.2))
      (P.prod P) := by
    have hZ : AEStronglyMeasurable (Zvec ξ N) P := (aemeasurable_Zvec hξ N).aestronglyMeasurable
    exact hFc.comp_aestronglyMeasurable (hZ.comp_fst.prodMk hZ.comp_snd)
  have hbd : Integrable (fun y : Ω => K * (‖Qfun c (Zvec ξ N y)‖ * ‖T (Zvec ξ N y)‖ *
      ‖T (Zvec ξ N y)‖)) P := by
    refine integrable_comp_Zvec hξ N (g := fun z => K * (‖Qfun c z‖ * ‖T z‖ * ‖T z‖))
      (continuous_const.mul ((((continuous_Qfun c).norm).mul T.continuous.norm).mul
        T.continuous.norm)) (C := K * Cc * A ^ 2) (k := 4) (fun z => ?_)
    have hz0 := norm_nonneg z
    have hT' : ‖T z‖ ≤ A * ‖z‖ := norm_Tmap_le w z
    have hq := norm_Qfun_le c z
    rw [abs_of_nonneg (by positivity)]
    calc K * (‖Qfun c z‖ * ‖T z‖ * ‖T z‖)
        ≤ K * ((Cc * (1 + ‖z‖) ^ 2) * (A * ‖z‖) * (A * ‖z‖)) := by gcongr
      _ = K * Cc * A ^ 2 * ((1 + ‖z‖) ^ 2 * ‖z‖ ^ 2) := by ring
      _ ≤ K * Cc * A ^ 2 * ((1 + ‖z‖) ^ 2 * (1 + ‖z‖) ^ 2) := by
          gcongr; nlinarith
      _ = K * Cc * A ^ 2 * (1 + ‖z‖) ^ 4 := by ring
  refine Integrable.mono' (hbd.comp_snd P) hmeas (Eventually.of_forall fun p => ?_)
  have := abs_iter_le (hK 3 (le_refl _) (T (Zvec ξ N p.1))) ![Qfun c (Zvec ξ N p.2),
    T (Zvec ξ N p.2), T (Zvec ξ N p.2)]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    mul_one] at this
  simpa [F, Dfin_eq, mul_assoc] using this


lemma tri_sum0 {ι : Type*} (M : B [×3]→L[ℝ] ℝ) (s : Finset ι) (f : ι → B) (a b : B) :
    M ![∑ i ∈ s, f i, a, b] = ∑ i ∈ s, M ![f i, a, b] := by
  have h : ∀ x : B, M ![x, a, b] = (M.toContinuousLinearMap ![0, a, b] 0) x := by
    intro x
    simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    ext k; fin_cases k <;> simp [Function.update]
  simp_rw [h]
  exact map_sum _ _ _

lemma tri_smul0 (M : B [×3]→L[ℝ] ℝ) (t : ℝ) (x a b : B) : M ![t • x, a, b] = t * M ![x, a, b] := by
  have h := M.map_update_smul ![x, a, b] 0 t x
  have e : ∀ z : B, Function.update (![x, a, b] : Fin 3 → B) 0 z = ![z, a, b] := by
    intro z; ext i; fin_cases i <;> simp [Function.update]
  simpa [e] using h

lemma integrable_termC (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (cc u v : B) :
    Integrable (fun ω => iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N ω)) ![cc, u, v]) P := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hcont3 : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  refine integrable_comp_Zvec hξ N (g := fun z => iteratedFDeriv ℝ 3 Φ (Tmap w z) ![cc, u, v])
    ?_ (C := K * (‖cc‖ * ‖u‖ * ‖v‖)) (k := 0) (fun z => ?_)
  · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => B) ℝ ![cc, u, v]).continuous.comp
      (hcont3.comp (Tmap w).continuous)
  · have := abs_iter_le (hK 3 (le_refl _) (Tmap w z)) ![cc, u, v]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      mul_one] at this
    simpa [mul_assoc] using this

lemma fin2_B (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (c : Fin N → Fin N → B) :
    ∫ p : Ω × Ω, iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N p.1))
        ![Dfin ξ N c p.2, Tmap w (Zvec ξ N p.2), Tmap w (Zvec ξ N p.2)] ∂(P.prod P) =
      2 * ∑ i : Fin N, ∑ j : Fin N,
        ∫ ω, iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N ω)) ![c i j, w i, w j] ∂P := by
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  rw [integral_prod _ (integrable_prodB hξ hΦ w c)]
  have inner : ∀ x : Ω, ∫ y, iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N x))
      ![Dfin ξ N c y, Tmap w (Zvec ξ N y), Tmap w (Zvec ξ N y)] ∂P =
      2 * ∑ i : Fin N, ∑ j : Fin N,
        iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N x)) ![c i j, w i, w j] := by
    intro x
    set M := iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N x)) with hM
    have e : ∀ y, M ![Dfin ξ N c y, Tmap w (Zvec ξ N y), Tmap w (Zvec ξ N y)] =
        ∑ i : Fin N, ∑ j : Fin N, (ξ i y * ξ j y - if i = j then 1 else 0) *
          M ![c i j, Tmap w (Zvec ξ N y), Tmap w (Zvec ξ N y)] := by
      intro y
      simp only [Dfin]
      rw [tri_sum0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tri_sum0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [tri_smul0]
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_zz_quad hξ w M (c i j) i j)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => integrable_zz_quad hξ w M (c i j) i j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fin2_termB hξ w M (c i j) i j, hM, iter3_swap23 hΦ3 _ (c i j) (w j) (w i)]
    ring
  simp_rw [inner]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_termC hξ hΦ w (c i j) (w i) (w j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => integrable_termC hξ hΦ w (c i j) (w i) (w j))]

lemma fin2_identity (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (c : Fin N → Fin N → B) :
    ∫ ω, fderiv ℝ Φ (Tmap w (Zvec ξ N ω)) (Dfin ξ N c ω) ∂P =
      (1 / 2) * ∫ p : Ω × Ω, iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N p.1))
        ![Dfin ξ N c p.2, Tmap w (Zvec ξ N p.2), Tmap w (Zvec ξ N p.2)] ∂(P.prod P) := by
  rw [fin2_A hξ hΦ w c, fin2_B hξ hΦ w c]
  ring

end Assemble2

end Aux_Hlp4

section Aux_s9
open ProbabilityTheory
open ProbabilityTheory.Fernique

section Moment4
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

lemma three_quarters_gt : (2 : ℝ≥0∞)⁻¹ < 3 / 4 := by
  rw [ENNReal.inv_lt_iff_inv_lt]
  have : (3 / 4 : ℝ≥0∞)⁻¹ = 4 / 3 := by
    rw [ENNReal.inv_div (by norm_num) (by norm_num)]
  rw [this, ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

lemma three_quarters_lt : (3 / 4 : ℝ≥0∞) < 1 := by
  rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
  norm_num

lemma three_ratio : ((3 / 4 : ℝ≥0∞) / (1 - 3 / 4)).toReal = 3 := by
  have h34 : (3 / 4 : ℝ≥0∞) = ENNReal.ofReal (3 / 4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have h14 : (1 - 3 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4) := by
    rw [h34, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  rw [h14, h34, ENNReal.toReal_div, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- The Fernique constant for `c = 3/4`. -/
def fernK1 : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (logRatio (3 / 4 : ℝ≥0∞))) +
    ∑' n : ℕ, ENNReal.ofReal (Real.exp (-2⁻¹ * Real.log ((3 / 4 : ℝ≥0∞) / (1 - 3 / 4)).toReal * 2 ^ n))

lemma fernK1_lt_top : fernK1 < ∞ := by
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
  refine Summable.tsum_ofReal_lt_top <|
    Real.summable_exp_nat_mul_of_ge ?_ (fun i ↦ mod_cast (Nat.lt_pow_self (by simp)).le)
  refine mul_neg_of_neg_of_pos (by simp) (Real.log_pos ?_)
  rw [three_ratio]; norm_num

lemma logRatio_pos' : 0 < logRatio (3 / 4 : ℝ≥0∞) := logRatio_pos three_quarters_gt three_quarters_lt

/-- Moment-4 bound for centered Gaussian measures in terms of the second moment. -/
lemma gaussian_moment4_le {μ : Measure B} [IsProbabilityMeasure μ] (hμ : IsCenteredGaussian μ) :
    ∫⁻ x, ‖x‖ₑ ^ 4 ∂μ ≤
      ENNReal.ofReal (32 / logRatio (3 / 4 : ℝ≥0∞) ^ 2) * fernK1 * (∫⁻ x, ‖x‖ₑ ^ 2 ∂μ) ^ 2 := by
  set L := logRatio (3 / 4 : ℝ≥0∞) with hL
  have hLpos : 0 < L := logRatio_pos'
  set m := ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ with hm
  have hmfin : m < ∞ := by
    have := (gaussian_sqnorm_integrable hμ)
    have h2 := this.lintegral_lt_top
    rw [hm]
    refine lt_of_le_of_lt (le_of_eq ?_) h2
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rcases eq_or_ne m 0 with h0 | h0
  · have hae : ∀ᵐ x ∂μ, ‖x‖ₑ ^ 2 = 0 := by
      have := (lintegral_eq_zero_iff (by fun_prop)).1 h0
      exact this
    have : ∫⁻ x, ‖x‖ₑ ^ 4 ∂μ = 0 := by
      refine lintegral_eq_zero_iff (by fun_prop) |>.2 ?_
      filter_upwards [hae] with x hx
      have : ‖x‖ₑ = 0 := by simpa using hx
      simp [this]
    rw [this]; simp
  · have hmpos : 0 < m.toReal := ENNReal.toReal_pos h0 hmfin.ne
    set s := m.toReal with hs
    set a : ℝ := 2 * Real.sqrt s with ha_def
    have ha : 0 < a := by positivity
    have ha2 : a ^ 2 = 4 * s := by
      rw [ha_def, mul_pow, Real.sq_sqrt hmpos.le]; norm_num
    have hms : ENNReal.ofReal s = m := ENNReal.ofReal_toReal hmfin.ne
    -- Markov
    have hS : MeasurableSet {x : B | a < ‖x‖} := measurableSet_lt measurable_const measurable_norm
    have hmark : 4 * m * μ {x : B | a < ‖x‖} ≤ m := by
      have h1 := mul_meas_ge_le_lintegral₀ (μ := μ) (f := fun x : B => ‖x‖ₑ ^ 2)
        (by fun_prop) (4 * m)
      refine le_trans (mul_le_mul' le_rfl (measure_mono ?_)) h1
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have : (4 * m) = ENNReal.ofReal (a ^ 2) := by
        rw [ha2, ENNReal.ofReal_mul (by norm_num), hms]; norm_num
      rw [this, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha.le hx.le 2)
    have hcompl : 4 * μ {x : B | a < ‖x‖} ≤ 1 := by
      have : (4 * μ {x : B | a < ‖x‖}) * m ≤ 1 * m := by
        rw [one_mul]; calc _ = 4 * m * μ {x : B | a < ‖x‖} := by ring
          _ ≤ m := hmark
      exact (ENNReal.mul_le_mul_iff_left h0 hmfin.ne).1 this
    have hc : (3 / 4 : ℝ≥0∞) ≤ μ {x : B | ‖x‖ ≤ a} := by
      have e : {x : B | ‖x‖ ≤ a} = {x : B | a < ‖x‖}ᶜ := by
        ext x; simp
      rw [e, prob_compl_eq_one_sub hS]
      refine ENNReal.le_sub_of_add_le_right (measure_ne_top _ _) ?_
      have h4 : (4 : ℝ≥0∞) * (3 / 4 + μ {x : B | a < ‖x‖}) ≤ 4 * 1 := by
        rw [mul_add, mul_one]
        have : (4 : ℝ≥0∞) * (3 / 4) = 3 := by
          rw [mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
        rw [this]
        calc (3 : ℝ≥0∞) + 4 * μ {x : B | a < ‖x‖} ≤ 3 + 1 := by gcongr
          _ = 4 := by norm_num
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h4
    have := hμ.1
    have h_rot := IsGaussian.map_rotation_eq_self (μ := μ) (gaussian_integral_id_eq_zero hμ) (-(Real.pi / 4))
    have hF := lintegral_exp_mul_sq_norm_le_of_map_rotation_eq_self (a := a) h_rot hc three_quarters_gt
    have hF' : ∫⁻ x, ENNReal.ofReal (Real.exp (L * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ ≤ fernK1 := hF
    -- pointwise bound
    set C : ℝ := 32 / L ^ 2 * s ^ 2 with hC
    have hpt : ∀ x : B, ‖x‖ₑ ^ 4 ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.exp (L * a⁻¹ ^ 2 * ‖x‖ ^ 2)) := by
      intro x
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set t : ℝ := L * a⁻¹ ^ 2 with ht
      have htpos : 0 < t := by positivity
      have hy := Real.quadratic_le_exp_of_nonneg (x := t * ‖x‖ ^ 2) (by positivity)
      have e1 : C = 2 / t ^ 2 := by
        rw [hC, ht, mul_pow, inv_pow, ha2]
        field_simp
        ring
      rw [e1, show L * a⁻¹ ^ 2 * ‖x‖ ^ 2 = t * ‖x‖ ^ 2 from by rw [ht]]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (t * ‖x‖ ^ 2), mul_pos htpos htpos, norm_nonneg x, pow_nonneg (norm_nonneg x) 2]
    calc ∫⁻ x, ‖x‖ₑ ^ 4 ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (Real.exp (L * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (Real.exp (L * a⁻¹ ^ 2 * ‖x‖ ^ 2)) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * fernK1 := by gcongr
      _ = ENNReal.ofReal (32 / L ^ 2) * fernK1 * m ^ 2 := by
          rw [hC, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hmpos.le, hms]
          ring

end Moment4

end Aux_s9

section Aux_s10
open ProbabilityTheory

section HolderPart
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

instance holderTriple_442 : ENNReal.HolderTriple 4 4 2 where
  inv_add_inv_eq_inv := by
    have h : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h, ENNReal.mul_inv (by simp) (by simp), ← two_mul, ← mul_assoc]
    rw [ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

instance holderTriple_221 : ENNReal.HolderTriple 2 2 1 where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_two_add_inv_two]; simp

lemma lintegral_mul3_le {E1 E2 E3 : Type*} [NormedAddCommGroup E1] [NormedAddCommGroup E2]
    [NormedAddCommGroup E3] {f1 : Ω → E1} {f2 : Ω → E2} {f3 : Ω → E3}
    (h1 : AEStronglyMeasurable f1 P) (h2 : AEStronglyMeasurable f2 P)
    (h3 : AEStronglyMeasurable f3 P) :
    ∫⁻ ω, ‖f1 ω‖ₑ * ‖f2 ω‖ₑ * ‖f3 ω‖ₑ ∂P ≤ eLpNorm f1 2 P * eLpNorm f2 4 P * eLpNorm f3 4 P := by
  have hA : eLpNorm (fun ω => ‖f2 ω‖ * ‖f3 ω‖) 2 P ≤ eLpNorm f2 4 P * eLpNorm f3 4 P := by
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 4) (q := 4) (r := 2) (μ := P)
      (f := fun ω => ‖f2 ω‖) (g := fun ω => ‖f3 ω‖) (fun a b : ℝ => a * b) 1
      (by fun_prop) h2.norm h3.norm (by simp)
    rw [eLpNorm_norm _ h2, eLpNorm_norm _ h3] at this
    simpa using this
  have hB : eLpNorm (fun ω => ‖f1 ω‖ * (‖f2 ω‖ * ‖f3 ω‖)) 1 P ≤
      eLpNorm f1 2 P * eLpNorm (fun ω => ‖f2 ω‖ * ‖f3 ω‖) 2 P := by
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1) (μ := P)
      (f := fun ω => ‖f1 ω‖) (g := fun ω => ‖f2 ω‖ * ‖f3 ω‖) (fun a b : ℝ => a * b) 1
      (by fun_prop) h1.norm (h2.norm.mul h3.norm) (by simp)
    rw [eLpNorm_norm _ h1] at this
    simpa using this
  rw [eLpNorm_one_eq_lintegral_enorm] at hB
  calc ∫⁻ ω, ‖f1 ω‖ₑ * ‖f2 ω‖ₑ * ‖f3 ω‖ₑ ∂P
      = ∫⁻ ω, ‖‖f1 ω‖ * (‖f2 ω‖ * ‖f3 ω‖)‖ₑ ∂P := by
        refine lintegral_congr fun ω => ?_
        simp [enorm_mul, mul_assoc]
    _ ≤ eLpNorm f1 2 P * eLpNorm (fun ω => ‖f2 ω‖ * ‖f3 ω‖) 2 P := hB
    _ ≤ eLpNorm f1 2 P * (eLpNorm f2 4 P * eLpNorm f3 4 P) := by gcongr
    _ = _ := by ring
  exact h1.norm.mul (h2.norm.mul h3.norm)

lemma lintegral_mul2_le {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedAddCommGroup E2]
    {f1 : Ω → E1} {f2 : Ω → E2}
    (h1 : AEStronglyMeasurable f1 P) (h2 : AEStronglyMeasurable f2 P) :
    ∫⁻ ω, ‖f1 ω‖ₑ * ‖f2 ω‖ₑ ∂P ≤ eLpNorm f1 2 P * eLpNorm f2 2 P := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1) (μ := P)
      (f := fun ω => ‖f1 ω‖) (g := fun ω => ‖f2 ω‖) (fun a b : ℝ => a * b) 1
      (by fun_prop) h1.norm h2.norm (by simp)
  rw [eLpNorm_one_eq_lintegral_enorm] at this
  rw [eLpNorm_norm _ h1, eLpNorm_norm _ h2] at this
  · simpa [enorm_mul] using this
  · exact h1.norm.mul h2.norm

end HolderPart

end Aux_s10

section Aux_s11
open ProbabilityTheory

section PointwiseBounds
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma tri_add1 (M : B [×3]→L[ℝ] ℝ) (x x' y z : B) :
    M ![x + x', y, z] = M ![x, y, z] + M ![x', y, z] := by
  have h := M.map_update_add ![x, y, z] 0 x x'
  have e : ∀ w : B, Function.update (![x, y, z] : Fin 3 → B) 0 w = ![w, y, z] := by
    intro w; ext i; fin_cases i <;> simp [Function.update]
  simpa [e] using h

lemma tri_sub1 (M : B [×3]→L[ℝ] ℝ) (x x' y z : B) :
    M ![x - x', y, z] = M ![x, y, z] - M ![x', y, z] := by
  have := tri_add1 M (x - x') x' y z
  rw [sub_add_cancel] at this
  linarith

lemma tri_sub2 (M : B [×3]→L[ℝ] ℝ) (c x x' y : B) :
    M ![c, x - x', y] = M ![c, x, y] - M ![c, x', y] := by
  have := tri_add2 M c (x - x') x' y
  rw [sub_add_cancel] at this
  linarith

lemma tri_sub3 (M : B [×3]→L[ℝ] ℝ) (c x y y' : B) :
    M ![c, x, y - y'] = M ![c, x, y] - M ![c, x, y'] := by
  have := tri_add3 M c x (y - y') y'
  rw [sub_add_cancel] at this
  linarith

lemma tri_diff_bound (M M' : B [×3]→L[ℝ] ℝ) (d d' g g' : B) :
    |M ![d, g, g] - M' ![d', g', g']| ≤
      ‖M - M'‖ * (‖d'‖ * ‖g'‖ * ‖g'‖) +
        ‖M‖ * (‖d - d'‖ * ‖g‖ * ‖g‖ + ‖d'‖ * ‖g - g'‖ * ‖g‖ + ‖d'‖ * ‖g'‖ * ‖g - g'‖) := by
  have e : M ![d, g, g] - M' ![d', g', g'] =
      (M - M') ![d', g', g'] + (M ![d - d', g, g] + M ![d', g - g', g] + M ![d', g', g - g']) := by
    rw [tri_sub1, tri_sub2, tri_sub3]
    simp only [sub_apply]
    ring
  rw [e]
  have h1 := abs_tri_le (M - M') d' g' g'
  have h2 := abs_tri_le M (d - d') g g
  have h3 := abs_tri_le M d' (g - g') g
  have h4 := abs_tri_le M d' g' (g - g')
  have a1 := abs_add_le ((M - M') ![d', g', g']) (M ![d - d', g, g] + M ![d', g - g', g] + M ![d', g', g - g'])
  have a2 := abs_add_le (M ![d - d', g, g] + M ![d', g - g', g]) (M ![d', g', g - g'])
  have a3 := abs_add_le (M ![d - d', g, g]) (M ![d', g - g', g])
  nlinarith

lemma enorm_tri_diff_le (M M' : B [×3]→L[ℝ] ℝ) (d d' g g' : B) :
    ‖M ![d, g, g] - M' ![d', g', g']‖ₑ ≤
      ‖M - M'‖ₑ * (‖d'‖ₑ * ‖g'‖ₑ * ‖g'‖ₑ) +
        ‖M‖ₑ * (‖d - d'‖ₑ * ‖g‖ₑ * ‖g‖ₑ + ‖d'‖ₑ * ‖g - g'‖ₑ * ‖g‖ₑ + ‖d'‖ₑ * ‖g'‖ₑ * ‖g - g'‖ₑ) := by
  have h := tri_diff_bound M M' d d' g g'
  calc ‖M ![d, g, g] - M' ![d', g', g']‖ₑ
      = ENNReal.ofReal |M ![d, g, g] - M' ![d', g', g']| := by
        rw [← Real.norm_eq_abs, ofReal_norm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h
    _ = _ := by
        simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul, ofReal_norm]

/-- Lipschitz bound for iterated derivatives. -/
lemma lip_iter {Φ : B → ℝ} {k : ℕ} (hΦ : ContDiff ℝ (k + 1) Φ) {K : ℝ}
    (hK : ∀ y, ‖iteratedFDeriv ℝ (k + 1) Φ y‖ ≤ K) (x y : B) :
    ‖iteratedFDeriv ℝ k Φ x - iteratedFDeriv ℝ k Φ y‖ ≤ K * ‖x - y‖ := by
  have hd : ∀ z : B, DifferentiableAt ℝ (iteratedFDeriv ℝ k Φ) z := fun z =>
    hΦ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k) z
  have := (convex_univ (𝕜 := ℝ) (E := B)).norm_image_sub_le_of_norm_fderiv_le
    (f := iteratedFDeriv ℝ k Φ) (C := K) (fun z _ => hd z)
    (fun z _ => by rw [norm_fderiv_iteratedFDeriv]; exact hK z) (Set.mem_univ y) (Set.mem_univ x)
  exact this

lemma abs_fderiv_diff_le {Φ : B → ℝ} (hΦ : ContDiff ℝ 2 Φ) {K1 K2 : ℝ}
    (hK1 : ∀ y, ‖iteratedFDeriv ℝ 1 Φ y‖ ≤ K1) (hK2 : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ K2)
    (y y' d d' : B) :
    |fderiv ℝ Φ y d - fderiv ℝ Φ y' d'| ≤ K1 * ‖d - d'‖ + K2 * (‖y - y'‖ * ‖d'‖) := by
  have e : fderiv ℝ Φ y d - fderiv ℝ Φ y' d' =
      fderiv ℝ Φ y (d - d') + (iteratedFDeriv ℝ 1 Φ y - iteratedFDeriv ℝ 1 Φ y') ![d'] := by
    simp only [map_sub, sub_apply]
    simp
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add (abs_fderiv_le hK1 _ _) ?_)
  have hl : ‖iteratedFDeriv ℝ 1 Φ y - iteratedFDeriv ℝ 1 Φ y'‖ ≤ K2 * ‖y - y'‖ :=
    lip_iter (k := 1) hΦ (fun z => hK2 z) y y'
  have := (iteratedFDeriv ℝ 1 Φ y - iteratedFDeriv ℝ 1 Φ y').le_opNorm ![d']
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, Matrix.cons_val_zero]
  calc _ ≤ K2 * ‖y - y'‖ * ‖d'‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    _ = _ := by ring

lemma enorm_fderiv_diff_le {Φ : B → ℝ} (hΦ : ContDiff ℝ 2 Φ) {K1 K2 : ℝ} (hK10 : 0 ≤ K1)
    (hK20 : 0 ≤ K2)
    (hK1 : ∀ y, ‖iteratedFDeriv ℝ 1 Φ y‖ ≤ K1) (hK2 : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ K2)
    (y y' d d' : B) :
    ‖fderiv ℝ Φ y d - fderiv ℝ Φ y' d'‖ₑ ≤
      ENNReal.ofReal K1 * ‖d - d'‖ₑ + ENNReal.ofReal K2 * (‖y - y'‖ₑ * ‖d'‖ₑ) := by
  have h := abs_fderiv_diff_le hΦ hK1 hK2 y y' d d'
  calc ‖fderiv ℝ Φ y d - fderiv ℝ Φ y' d'‖ₑ
      = ENNReal.ofReal |fderiv ℝ Φ y d - fderiv ℝ Φ y' d'| := by
        rw [← Real.norm_eq_abs, ofReal_norm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h
    _ = _ := by
        simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul, ofReal_norm]

end PointwiseBounds

end Aux_s11

section Aux_s13
open ProbabilityTheory

section Abstract
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma tendsto_integral_of_lintegral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℕ → α → E} {f : α → E} (hf : Integrable f μ) (hFm : ∀ m, AEStronglyMeasurable (F m) μ)
    (h : Tendsto (fun m => ∫⁻ x, ‖F m x - f x‖ₑ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, F m x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hf.1 ?_ h
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with m hm
  have h1 : Integrable (fun x => F m x - f x) μ :=
    ⟨(hFm m).sub hf.1, by
      simpa [HasFiniteIntegral] using hm.trans ENNReal.one_lt_top⟩
  exact (h1.add hf).congr (Eventually.of_forall fun x => by simp)

lemma tendsto_zero_of_le {f g : ℕ → ℝ≥0∞} (hg : Tendsto g atTop (𝓝 0)) (h : ∀ m, f m ≤ g m) :
    Tendsto f atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun _ => zero_le) h

lemma tendsto_zero_of_eventually_le {f g : ℕ → ℝ≥0∞} (hg : Tendsto g atTop (𝓝 0))
    (h : ∀ᶠ m in atTop, f m ≤ g m) : Tendsto f atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall fun _ => zero_le) h

lemma second_lhs_tendsto {Φ : B → ℝ} (hΦ : MemCb 3 Φ)
    {G D : Ω → B} {Gm Dm : ℕ → Ω → B}
    (hG : AEStronglyMeasurable G P) (hD : AEStronglyMeasurable D P)
    (hGm : ∀ m, AEStronglyMeasurable (Gm m) P) (hDm : ∀ m, AEStronglyMeasurable (Dm m) P)
    (hG4 : Tendsto (fun m => eLpNorm (fun ω => Gm m ω - G ω) 4 P) atTop (𝓝 0))
    (hD2 : Tendsto (fun m => eLpNorm (fun ω => Dm m ω - D ω) 2 P) atTop (𝓝 0))
    (hD2fin : eLpNorm D 2 P < ∞)
    (hint1 : Integrable (fun ω => fderiv ℝ Φ (G ω) (D ω)) P) :
    Tendsto (fun m => ∫ ω, fderiv ℝ Φ (Gm m ω) (Dm m ω) ∂P) atTop
      (𝓝 (∫ ω, fderiv ℝ Φ (G ω) (D ω) ∂P)) := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hΦ2 : ContDiff ℝ 2 Φ := hΦ3.of_le (by norm_num)
  have hcont : Continuous (Function.uncurry fun a b : B => fderiv ℝ Φ a b) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B) (F := ℝ)).continuous.comp
      (((hΦ3.continuous_fderiv (by norm_num)).comp continuous_fst).prodMk continuous_snd)
  have hmeas : ∀ m, AEStronglyMeasurable (fun ω => fderiv ℝ Φ (Gm m ω) (Dm m ω)) P := fun m =>
    hcont.comp_aestronglyMeasurable₂ (hGm m) (hDm m)
  have hmeas0 : AEStronglyMeasurable (fun ω => fderiv ℝ Φ (G ω) (D ω)) P :=
    hcont.comp_aestronglyMeasurable₂ hG hD
  refine tendsto_integral_of_lintegral hint1 hmeas ?_
  have hK1 : ∀ y, ‖iteratedFDeriv ℝ 1 Φ y‖ ≤ K := fun y => hK 1 (by norm_num) y
  have hK2 : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ K := fun y => hK 2 (by norm_num) y
  have hpt : ∀ m ω, ‖fderiv ℝ Φ (Gm m ω) (Dm m ω) - fderiv ℝ Φ (G ω) (D ω)‖ₑ ≤
      ENNReal.ofReal K * ‖Dm m ω - D ω‖ₑ + ENNReal.ofReal K * (‖Gm m ω - G ω‖ₑ * ‖D ω‖ₑ) :=
    fun m ω => enorm_fderiv_diff_le hΦ2 hK0 hK0 hK1 hK2 _ _ _ _
  have hbound : ∀ m, ∫⁻ ω, ‖fderiv ℝ Φ (Gm m ω) (Dm m ω) - fderiv ℝ Φ (G ω) (D ω)‖ₑ ∂P ≤
      ENNReal.ofReal K * eLpNorm (fun ω => Dm m ω - D ω) 2 P +
        ENNReal.ofReal K * (eLpNorm (fun ω => Gm m ω - G ω) 4 P * eLpNorm D 2 P) := by
    intro m
    have hD' : AEStronglyMeasurable (fun ω => Dm m ω - D ω) P := (hDm m).sub hD
    have hG' : AEStronglyMeasurable (fun ω => Gm m ω - G ω) P := (hGm m).sub hG
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal K * ‖Dm m ω - D ω‖ₑ +
            ENNReal.ofReal K * (‖Gm m ω - G ω‖ₑ * ‖D ω‖ₑ)) ∂P := lintegral_mono (hpt m)
      _ = ENNReal.ofReal K * ∫⁻ ω, ‖Dm m ω - D ω‖ₑ ∂P +
            ENNReal.ofReal K * ∫⁻ ω, ‖Gm m ω - G ω‖ₑ * ‖D ω‖ₑ ∂P := by
          rw [lintegral_add_left' (hD'.enorm.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          · rw [← eLpNorm_one_eq_lintegral_enorm hD']
            exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
          · refine (lintegral_mul2_le hG' hD).trans ?_
            gcongr
            exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  refine tendsto_zero_of_le ?_ hbound
  have h1 : Tendsto (fun m => ENNReal.ofReal K * eLpNorm (fun ω => Dm m ω - D ω) 2 P) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hD2 (Or.inr ENNReal.ofReal_ne_top)
  have h2 : Tendsto (fun m => ENNReal.ofReal K * (eLpNorm (fun ω => Gm m ω - G ω) 4 P * eLpNorm D 2 P))
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const hG4 (Or.inr hD2fin.ne)
    simpa using ENNReal.Tendsto.const_mul this (Or.inr ENNReal.ofReal_ne_top)
  simpa using h1.add h2

end Abstract

end Aux_s13

section Aux_s14
open ProbabilityTheory

section Abstract2
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma continuous_trieval :
    Continuous (fun x : (B [×3]→L[ℝ] ℝ) × (B × B × B) => x.1 ![x.2.1, x.2.2.1, x.2.2.2]) := by
  refine ContinuousEval.continuous_eval.comp (continuous_fst.prodMk (continuous_pi fun k => ?_))
  fin_cases k
  · exact continuous_snd.fst
  · exact continuous_snd.snd.fst
  · exact continuous_snd.snd.snd

lemma lintegral_prod_snd' {g : Ω → ℝ≥0∞} (hg : AEMeasurable g P) :
    ∫⁻ p : Ω × Ω, g p.2 ∂(P.prod P) = ∫⁻ ω, g ω ∂P := by
  have := lintegral_prod_mul (μ := P) (ν := P) (f := fun _ => (1 : ℝ≥0∞)) (g := g)
    aemeasurable_const hg
  simpa using this

lemma aesm_tri {Φ : B → ℝ} (hΦ : ContDiff ℝ 3 Φ) {G D H : Ω → B} (hG : AEStronglyMeasurable G P)
    (hD : AEStronglyMeasurable D P) (hH : AEStronglyMeasurable H P) :
    AEStronglyMeasurable (fun p : Ω × Ω => iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, H p.2, H p.2])
      (P.prod P) := by
  have hc : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ.continuous_iteratedFDeriv (by norm_num)
  have h1 : AEStronglyMeasurable (fun p : Ω × Ω => iteratedFDeriv ℝ 3 Φ (G p.1)) (P.prod P) :=
    hc.comp_aestronglyMeasurable hG.comp_fst
  exact continuous_trieval.comp_aestronglyMeasurable
    (h1.prodMk (hD.comp_snd.prodMk (hH.comp_snd.prodMk hH.comp_snd)))

lemma second_rhs_tendsto {Φ : B → ℝ} (hΦ : MemCb 3 Φ)
    {G D : Ω → B} {Gm Dm : ℕ → Ω → B}
    (hG : AEStronglyMeasurable G P) (hD : AEStronglyMeasurable D P)
    (hGm : ∀ m, AEStronglyMeasurable (Gm m) P) (hDm : ∀ m, AEStronglyMeasurable (Dm m) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun m => Gm m ω) atTop (𝓝 (G ω)))
    (hG4 : Tendsto (fun m => eLpNorm (fun ω => Gm m ω - G ω) 4 P) atTop (𝓝 0))
    (hD2 : Tendsto (fun m => eLpNorm (fun ω => Dm m ω - D ω) 2 P) atTop (𝓝 0))
    (hG4fin : eLpNorm G 4 P < ∞) (hD2fin : eLpNorm D 2 P < ∞)
    (hint3 : Integrable
      (fun p : Ω × Ω => iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, G p.2, G p.2]) (P.prod P)) :
    Tendsto (fun m => ∫ p : Ω × Ω,
      iteratedFDeriv ℝ 3 Φ (Gm m p.1) ![Dm m p.2, Gm m p.2, Gm m p.2] ∂(P.prod P)) atTop
      (𝓝 (∫ p : Ω × Ω, iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, G p.2, G p.2] ∂(P.prod P))) := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hK3 : ∀ y, ‖iteratedFDeriv ℝ 3 Φ y‖ ≤ K := fun y => hK 3 le_rfl y
  have hc : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  refine tendsto_integral_of_lintegral hint3 (fun m => aesm_tri hΦ3 (hGm m) (hDm m) (hGm m)) ?_
  -- the pieces
  set a : ℕ → Ω → ℝ≥0∞ :=
    fun m ω => ‖iteratedFDeriv ℝ 3 Φ (Gm m ω) - iteratedFDeriv ℝ 3 Φ (G ω)‖ₑ with ha_def
  set g0 : Ω → ℝ≥0∞ := fun ω => ‖D ω‖ₑ * ‖G ω‖ₑ * ‖G ω‖ₑ with hg0_def
  set g1 : ℕ → Ω → ℝ≥0∞ := fun m ω => ‖Dm m ω - D ω‖ₑ * ‖Gm m ω‖ₑ * ‖Gm m ω‖ₑ +
    ‖D ω‖ₑ * ‖Gm m ω - G ω‖ₑ * ‖Gm m ω‖ₑ + ‖D ω‖ₑ * ‖G ω‖ₑ * ‖Gm m ω - G ω‖ₑ with hg1_def
  have ha_meas : ∀ m, AEMeasurable (a m) P := fun m =>
    ((hc.comp_aestronglyMeasurable (hGm m)).sub (hc.comp_aestronglyMeasurable hG)).enorm
  have hg0_meas : AEMeasurable g0 P := (hD.enorm.mul hG.enorm).mul hG.enorm
  have hg1_meas : ∀ m, AEMeasurable (g1 m) P := fun m => by
    have h1 := ((hDm m).sub hD).enorm
    have h2 := (hGm m).enorm
    have h3 := ((hGm m).sub hG).enorm
    have h4 := hD.enorm
    have h5 := hG.enorm
    exact (((h1.mul h2).mul h2).add ((h4.mul h3).mul h2)).add ((h4.mul h5).mul h3)
  have hpt : ∀ m (p : Ω × Ω),
      ‖iteratedFDeriv ℝ 3 Φ (Gm m p.1) ![Dm m p.2, Gm m p.2, Gm m p.2] -
        iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, G p.2, G p.2]‖ₑ ≤
        a m p.1 * g0 p.2 + ENNReal.ofReal K * g1 m p.2 := by
    intro m p
    refine (enorm_tri_diff_le _ _ _ _ _ _).trans ?_
    have hKe : ‖iteratedFDeriv ℝ 3 Φ (Gm m p.1)‖ₑ ≤ ENNReal.ofReal K := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hK3 _)
    gcongr
  have hint : ∀ m, ∫⁻ p : Ω × Ω, ‖iteratedFDeriv ℝ 3 Φ (Gm m p.1) ![Dm m p.2, Gm m p.2, Gm m p.2] -
        iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, G p.2, G p.2]‖ₑ ∂(P.prod P) ≤
      (∫⁻ ω, a m ω ∂P) * (∫⁻ ω, g0 ω ∂P) + ENNReal.ofReal K * ∫⁻ ω, g1 m ω ∂P := by
    intro m
    calc _ ≤ ∫⁻ p : Ω × Ω, (a m p.1 * g0 p.2 + ENNReal.ofReal K * g1 m p.2) ∂(P.prod P) :=
          lintegral_mono (hpt m)
      _ = _ := by
          have hAE : AEMeasurable (fun p : Ω × Ω => a m p.1 * g0 p.2) (P.prod P) :=
            (ha_meas m).comp_fst.mul hg0_meas.comp_snd
          rw [lintegral_add_left' hAE,
            lintegral_prod_mul (ha_meas m) hg0_meas,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod_snd' (hg1_meas m)]
  -- finiteness of the fixed factor
  have hg0_fin : ∫⁻ ω, g0 ω ∂P ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hD2fin hG4fin) hG4fin).ne
      (lintegral_mul3_le hD hG hG)
  -- dominated convergence for the derivative part
  have ha_lim : Tendsto (fun m => ∫⁻ ω, a m ω ∂P) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := P) (F := a)
      (f := fun _ => (0 : ℝ≥0∞)) (fun _ => 2 * ENNReal.ofReal K) ha_meas ?_ ?_ ?_
    · simpa using this
    · intro m
      refine Eventually.of_forall fun ω => ?_
      have h1 : ‖iteratedFDeriv ℝ 3 Φ (Gm m ω)‖ₑ ≤ ENNReal.ofReal K := by
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hK3 _)
      have h2 : ‖iteratedFDeriv ℝ 3 Φ (G ω)‖ₑ ≤ ENNReal.ofReal K := by
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hK3 _)
      calc a m ω ≤ ‖iteratedFDeriv ℝ 3 Φ (Gm m ω)‖ₑ + ‖iteratedFDeriv ℝ 3 Φ (G ω)‖ₑ :=
            enorm_sub_le
        _ ≤ ENNReal.ofReal K + ENNReal.ofReal K := add_le_add h1 h2
        _ = 2 * ENNReal.ofReal K := by rw [two_mul]
    · simp [ENNReal.mul_eq_top]
    · filter_upwards [hae] with ω hω
      exact tendsto_iff_enorm_sub_tendsto_zero.1 ((hc.tendsto (G ω)).comp hω)
  -- L^4 bound on `Gm`
  have hev : ∀ᶠ m in atTop, eLpNorm (Gm m) 4 P ≤ eLpNorm G 4 P + 1 := by
    filter_upwards [hG4.eventually (gt_mem_nhds zero_lt_one)] with m hm
    have : Gm m = (fun ω => Gm m ω - G ω) + G := by ext ω; simp
    calc eLpNorm (Gm m) 4 P = eLpNorm ((fun ω => Gm m ω - G ω) + G) 4 P := by rw [← this]
      _ ≤ eLpNorm (fun ω => Gm m ω - G ω) 4 P + eLpNorm G 4 P :=
          eLpNorm_add_le (by norm_num)
      _ ≤ 1 + eLpNorm G 4 P := by gcongr
      _ = _ := add_comm _ _
  set S : ℝ≥0∞ := eLpNorm G 4 P + 1 with hS
  have hSfin : S ≠ ∞ := (ENNReal.add_lt_top.2 ⟨hG4fin, ENNReal.one_lt_top⟩).ne
  set x : ℕ → ℝ≥0∞ := fun m => eLpNorm (fun ω => Dm m ω - D ω) 2 P with hx
  set y : ℕ → ℝ≥0∞ := fun m => eLpNorm (fun ω => Gm m ω - G ω) 4 P with hy
  set C1 : ℝ≥0∞ := S * S with hC1
  set C2 : ℝ≥0∞ := eLpNorm D 2 P * S + eLpNorm D 2 P * eLpNorm G 4 P with hC2
  have hC1fin : C1 ≠ ∞ := ENNReal.mul_ne_top hSfin hSfin
  have hC2fin : C2 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hD2fin.ne hSfin, ENNReal.mul_ne_top hD2fin.ne hG4fin.ne⟩
  have hg1_le : ∀ᶠ m in atTop, ∫⁻ ω, g1 m ω ∂P ≤ x m * C1 + C2 * y m := by
    filter_upwards [hev] with m hm
    have hD' : AEStronglyMeasurable (fun ω => Dm m ω - D ω) P := (hDm m).sub hD
    have hG' : AEStronglyMeasurable (fun ω => Gm m ω - G ω) P := (hGm m).sub hG
    have m1 := lintegral_mul3_le hD' (hGm m) (hGm m)
    have m2 := lintegral_mul3_le hD hG' (hGm m)
    have m3 := lintegral_mul3_le hD hG hG'
    have e1 : AEMeasurable (fun ω => ‖Dm m ω - D ω‖ₑ * ‖Gm m ω‖ₑ * ‖Gm m ω‖ₑ) P :=
      (hD'.enorm.mul (hGm m).enorm).mul (hGm m).enorm
    have e2 : AEMeasurable (fun ω => ‖D ω‖ₑ * ‖Gm m ω - G ω‖ₑ * ‖Gm m ω‖ₑ) P :=
      (hD.enorm.mul hG'.enorm).mul (hGm m).enorm
    have e3 : AEMeasurable (fun ω => ‖D ω‖ₑ * ‖G ω‖ₑ * ‖Gm m ω - G ω‖ₑ) P :=
      (hD.enorm.mul hG.enorm).mul hG'.enorm
    calc ∫⁻ ω, g1 m ω ∂P
        = ∫⁻ ω, ‖Dm m ω - D ω‖ₑ * ‖Gm m ω‖ₑ * ‖Gm m ω‖ₑ ∂P +
          ∫⁻ ω, ‖D ω‖ₑ * ‖Gm m ω - G ω‖ₑ * ‖Gm m ω‖ₑ ∂P +
          ∫⁻ ω, ‖D ω‖ₑ * ‖G ω‖ₑ * ‖Gm m ω - G ω‖ₑ ∂P := by
          simp only [hg1_def]
          have e12 : AEMeasurable (fun ω => ‖Dm m ω - D ω‖ₑ * ‖Gm m ω‖ₑ * ‖Gm m ω‖ₑ +
              ‖D ω‖ₑ * ‖Gm m ω - G ω‖ₑ * ‖Gm m ω‖ₑ) P := e1.add e2
          rw [lintegral_add_left' e12, lintegral_add_left' e1]
      _ ≤ x m * (eLpNorm (Gm m) 4 P * eLpNorm (Gm m) 4 P) +
          eLpNorm D 2 P * y m * eLpNorm (Gm m) 4 P + eLpNorm D 2 P * eLpNorm G 4 P * y m := by
          rw [← mul_assoc]; gcongr
      _ ≤ x m * (S * S) + eLpNorm D 2 P * y m * S + eLpNorm D 2 P * eLpNorm G 4 P * y m := by
          have : eLpNorm (Gm m) 4 P ≤ S := hm
          gcongr
      _ = x m * C1 + C2 * y m := by rw [hC1, hC2]; ring
  have hlim : Tendsto (fun m => (∫⁻ ω, a m ω ∂P) * (∫⁻ ω, g0 ω ∂P) +
      ENNReal.ofReal K * (x m * C1 + C2 * y m)) atTop (𝓝 0) := by
    have t1 : Tendsto (fun m => (∫⁻ ω, a m ω ∂P) * (∫⁻ ω, g0 ω ∂P)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const ha_lim (Or.inr hg0_fin)
    have t2 : Tendsto (fun m => x m * C1) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hD2 (Or.inr hC1fin)
    have t3 : Tendsto (fun m => C2 * y m) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hG4 (Or.inr hC2fin)
    have t4 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) (t2.add t3) (Or.inr ENNReal.ofReal_ne_top)
    simpa using t1.add t4
  refine tendsto_zero_of_eventually_le hlim ?_
  filter_upwards [hg1_le] with m hm
  exact (hint m).trans (by gcongr)

end Abstract2

end Aux_s14

section Aux_s16
open ProbabilityTheory

section LinPGen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

lemma eLpNorm_pow_eq {E : Type*} [NormedAddCommGroup E] {f : Ω → E} (hf : AEStronglyMeasurable f P)
    {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) (n : ℕ) (hn : p.toReal = n) :
    eLpNorm f p P ^ n = ∫⁻ ω, ‖f ω‖ₑ ^ n ∂P := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf, hn]
  have hn0 : (n : ℝ) ≠ 0 := by
    rw [← hn]; exact (ENNReal.toReal_pos hp0 hpt).ne'
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0, ENNReal.rpow_one]
  simp [ENNReal.rpow_natCast]

/-- The finite linear polynomial `∑_{i<n} ξ_i • f i`. -/
def linP (ξ : ℕ → Ω → ℝ) (n : ℕ) (f : ℕ → E) (ω : Ω) : E :=
  ∑ i ∈ Finset.range n, ξ i ω • f i

lemma linP_eq_Tmap (ξ : ℕ → Ω → ℝ) (n : ℕ) (f : ℕ → E) (ω : Ω) :
    linP ξ n f ω = Tmap (fun i : Fin n => f i) (Zvec ξ n ω) := by
  rw [Tmap_apply, linP, Finset.sum_range]
  rfl

/-- Zero-padding of a coefficient sequence. -/
def padv (n : ℕ) (f : ℕ → E) : ℕ → E := fun i => if i < n then f i else 0

lemma linP_pad (ξ : ℕ → Ω → ℝ) {n N : ℕ} (h : n ≤ N) (f : ℕ → E) (ω : Ω) :
    linP ξ n f ω = linP ξ N (padv n f) ω := by
  unfold linP
  symm
  rw [← Finset.sum_subset (Finset.range_subset_range.2 h)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp [padv, Finset.mem_range.1 hi]
  · intro i _ hi
    have : ¬ i < n := fun hh => hi (Finset.mem_range.2 hh)
    simp [padv, this]

lemma linP_sub (ξ : ℕ → Ω → ℝ) (N : ℕ) (f f' : ℕ → E) (ω : Ω) :
    linP ξ N f ω - linP ξ N f' ω = linP ξ N (f - f') ω := by
  unfold linP
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_sub]

lemma aesm_linP (hξ : IsStdGaussianSeq P ξ) (n : ℕ) (f : ℕ → E) :
    AEStronglyMeasurable (linP ξ n f) P := by
  have : linP ξ n f = fun ω => ∑ i ∈ Finset.range n, ξ i ω • f i := rfl
  rw [this]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (hξ.aemeasurable i).aestronglyMeasurable.smul aestronglyMeasurable_const

lemma eLpNorm_linP_lt_top (hξ : IsStdGaussianSeq P ξ) (n : ℕ) (f : ℕ → E) :
    eLpNorm (linP ξ n f) 2 P < ∞ := by
  set w : Fin n → E := fun i => f i with hw
  set S : ℝ := ∑ i : Fin n, ‖w i‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hint : Integrable (fun ω => ‖Tmap w (Zvec ξ n ω)‖ ^ 2) P := by
    refine integrable_comp_Zvec hξ n (g := fun z => ‖Tmap w z‖ ^ 2)
      ((Tmap w).continuous.norm.pow 2) (C := S ^ 2) (k := 2) fun z => ?_
    rw [abs_of_nonneg (by positivity)]
    calc ‖Tmap w z‖ ^ 2 ≤ (S * ‖z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_Tmap_le w z) 2
      _ ≤ S ^ 2 * (1 + ‖z‖) ^ 2 := by
          rw [mul_pow]
          gcongr
          linarith
  have h1 := hint.lintegral_lt_top
  have hq : linP ξ n f = fun ω => Tmap w (Zvec ξ n ω) := funext fun ω => linP_eq_Tmap ξ n f ω
  have hs := aesm_linP hξ n f
  have : eLpNorm (linP ξ n f) 2 P ^ 2 < ∞ := by
    rw [eLpNorm_pow_eq hs (by norm_num) (by norm_num) 2 (by norm_num)]
    refine lt_of_le_of_lt (le_of_eq ?_) h1
    refine lintegral_congr fun ω => ?_
    rw [hq, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at this
  simp at this

end LinPGen

section LinP
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

lemma gpi_integral_coord (N : ℕ) (k : Fin N) : ∫ z, z k ∂(gpi N) = 0 := by
  have := pi_integral_eval N id continuous_id k
  simpa using this

lemma gpi_integrable_coord (N : ℕ) (k : Fin N) : Integrable (fun z : Fin N → ℝ => z k) (gpi N) := by
  refine integrable_of_poly (C := 1) (k := 1) (continuous_apply k).aestronglyMeasurable fun z => ?_
  have := norm_le_pi_norm z k
  rw [Real.norm_eq_abs] at this
  simp only [one_mul, pow_one]
  linarith [norm_nonneg z]

lemma isCenteredGaussian_Tmap (hξ : IsStdGaussianSeq P ξ) {N : ℕ} (w : Fin N → B) :
    IsCenteredGaussian (P.map (fun ω => Tmap w (Zvec ξ N ω))) := by
  have hmap : P.map (fun ω => Tmap w (Zvec ξ N ω)) = (gpi N).map (Tmap w) := by
    rw [← map_Zvec hξ N]
    exact ((Tmap w).continuous.measurable.aemeasurable.map_map_of_aemeasurable
      (aemeasurable_Zvec hξ N)).symm
  rw [hmap]
  refine ⟨inferInstance, fun L => ?_⟩
  rw [integral_map (Tmap w).continuous.measurable.aemeasurable L.continuous.aestronglyMeasurable]
  have e : ∀ z : Fin N → ℝ, L (Tmap w z) = ∑ k, z k * L (w k) := fun z => by
    rw [Tmap_apply, map_sum]; simp
  simp_rw [e]
  rw [integral_finset_sum _ (fun k _ => (gpi_integrable_coord N k).mul_const _)]
  simp [integral_mul_const, gpi_integral_coord]

lemma isCenteredGaussian_linP (hξ : IsStdGaussianSeq P ξ) (n : ℕ) (f : ℕ → B) :
    IsCenteredGaussian (P.map (linP ξ n f)) := by
  have : linP ξ n f = fun ω => Tmap (fun i : Fin n => f i) (Zvec ξ n ω) :=
    funext (linP_eq_Tmap ξ n f)
  rw [this]
  exact isCenteredGaussian_Tmap hξ _

lemma isCenteredGaussian_linP_sub (hξ : IsStdGaussianSeq P ξ) (n n' : ℕ) (f f' : ℕ → B) :
    IsCenteredGaussian (P.map (fun ω => linP ξ n f ω - linP ξ n' f' ω)) := by
  have : (fun ω => linP ξ n f ω - linP ξ n' f' ω) = linP ξ (n + n') (padv n f - padv n' f') := by
    funext ω
    rw [linP_pad ξ (Nat.le_add_right n n') f ω, linP_pad ξ (Nat.le_add_left n' n) f' ω,
      linP_sub]
  rw [this]
  exact isCenteredGaussian_linP hξ _ _

end LinP

end Aux_s16

section Aux_s17
open ProbabilityTheory
open ProbabilityTheory.Fernique

section GaussL4
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

lemma eLpNorm_four_pow {f : Ω → B} (hf : AEStronglyMeasurable f P) :
    eLpNorm f 4 P ^ 4 = ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂P :=
  eLpNorm_pow_eq hf (by norm_num) (by norm_num) 4 (by norm_num)

lemma eLpNorm_two_pow {f : Ω → B} (hf : AEStronglyMeasurable f P) :
    eLpNorm f 2 P ^ 2 = ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P :=
  eLpNorm_pow_eq hf (by norm_num) (by norm_num) 2 (by norm_num)

/-- The moment-4 constant. -/
def gK : ℝ≥0∞ := ENNReal.ofReal (32 / logRatio (3 / 4 : ℝ≥0∞) ^ 2) * fernK1

lemma gK_ne_top : gK ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top fernK1_lt_top.ne

lemma gaussian_lintegral_sq_lt_top {μ : Measure B} [IsProbabilityMeasure μ]
    (hμ : IsCenteredGaussian μ) : ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ < ∞ := by
  have h2 := (gaussian_sqnorm_integrable hμ).lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma gauss_N4_le {X : Ω → B} (hX : AEMeasurable X P) (hg : IsCenteredGaussian (P.map X)) :
    eLpNorm X 2 P < ∞ ∧ eLpNorm X 4 P ^ 4 ≤ gK * eLpNorm X 2 P ^ 4 := by
  have hXs : AEStronglyMeasurable X P := hX.aestronglyMeasurable
  have hm : ∀ k : ℕ, ∫⁻ x, ‖x‖ₑ ^ k ∂(P.map X) = ∫⁻ ω, ‖X ω‖ₑ ^ k ∂P := fun k =>
    lintegral_map' (Measurable.aemeasurable (by fun_prop)) hX
  have h4 := gaussian_moment4_le hg
  have h2 := gaussian_lintegral_sq_lt_top hg
  rw [hm, hm] at h4
  rw [hm] at h2
  refine ⟨?_, ?_⟩
  · rw [← eLpNorm_two_pow hXs] at h2
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at h2
    simp at h2
  · rw [eLpNorm_four_pow hXs, show eLpNorm X 2 P ^ 4 = (eLpNorm X 2 P ^ 2) ^ 2 by ring,
      eLpNorm_two_pow hXs]
    simpa [gK, mul_assoc] using h4

lemma le_of_pow4_le {x y K : ℝ≥0∞} (h : x ^ 4 ≤ K * y ^ 4) : x ≤ K ^ (1 / 4 : ℝ) * y := by
  have := ENNReal.rpow_le_rpow h (z := 1 / 4) (by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at this
  have e : ∀ t : ℝ≥0∞, (t ^ 4) ^ (1 / 4 : ℝ) = t := fun t => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rwa [e, e] at this

lemma ne_top_of_pow4_ne_top {x : ℝ≥0∞} (h : x ^ 4 ≠ ∞) : x ≠ ∞ := by
  rintro rfl
  simp at h

lemma chaos1_L4 (hξ : IsStdGaussianSeq P ξ) (n : ℕ → ℕ) (c : ℕ → ℕ → B) {G : Ω → B}
    (hG : AEStronglyMeasurable G P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun m => linP ξ (n m) (c m) ω) atTop (𝓝 (G ω)))
    (h2 : Tendsto (fun m => eLpNorm (fun ω => linP ξ (n m) (c m) ω - G ω) 2 P) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun ω => linP ξ (n m) (c m) ω - G ω) 4 P) atTop (𝓝 0) ∧
      eLpNorm G 4 P < ∞ := by
  set Gm : ℕ → Ω → B := fun m => linP ξ (n m) (c m) with hGm_def
  have hGm : ∀ m, AEStronglyMeasurable (Gm m) P := fun m => aesm_linP hξ _ _
  -- Step A
  have stepA : ∀ m, eLpNorm (fun ω => Gm m ω - G ω) 4 P ^ 4 ≤
      gK * eLpNorm (fun ω => Gm m ω - G ω) 2 P ^ 4 := by
    intro m
    set a := eLpNorm (fun ω => Gm m ω - G ω) 2 P with ha
    set e : ℕ → ℝ≥0∞ := fun k => eLpNorm (fun ω => Gm k ω - G ω) 2 P with he
    have hdm : ∀ k, ∫⁻ ω, ‖Gm m ω - Gm k ω‖ₑ ^ 4 ∂P ≤ gK * (a + e k) ^ 4 := by
      intro k
      have hX : AEMeasurable (fun ω => linP ξ (n m) (c m) ω - linP ξ (n k) (c k) ω) P :=
        ((hGm m).sub (hGm k)).aemeasurable
      have hg := isCenteredGaussian_linP_sub hξ (n m) (n k) (c m) (c k)
      obtain ⟨_, h4⟩ := gauss_N4_le hX hg
      have hXs := hX.aestronglyMeasurable
      rw [eLpNorm_four_pow hXs] at h4
      refine h4.trans ?_
      gcongr
      have : (fun ω => linP ξ (n m) (c m) ω - linP ξ (n k) (c k) ω) =
          (fun ω => Gm m ω - G ω) + (G - Gm k) := by ext ω; simp [hGm_def]
      rw [this]
      refine (eLpNorm_add_le (by norm_num)).trans ?_
      gcongr
      rw [he]
      simp only
      rw [show (G - Gm k) = -(fun ω => Gm k ω - G ω) by ext ω; simp, eLpNorm_neg]
    have hlimsup : Tendsto (fun k => gK * (a + e k) ^ 4) atTop (𝓝 (gK * a ^ 4)) := by
      have t1 : Tendsto (fun k => a + e k) atTop (𝓝 (a + 0)) := tendsto_const_nhds.add h2
      have t2 : Tendsto (fun k => (a + e k) ^ 4) atTop (𝓝 ((a + 0) ^ 4)) :=
        ((ENNReal.continuous_pow 4).tendsto _).comp t1
      simpa using ENNReal.Tendsto.const_mul t2 (Or.inr gK_ne_top)
    have hmeasd : ∀ k, AEMeasurable (fun ω => ‖Gm m ω - Gm k ω‖ₑ ^ 4) P := fun k =>
      ((hGm m).sub (hGm k)).enorm.pow_const _
    have hpt : ∀ᵐ ω ∂P, Tendsto (fun k => ‖Gm m ω - Gm k ω‖ₑ ^ 4) atTop
        (𝓝 (‖Gm m ω - G ω‖ₑ ^ 4)) := by
      filter_upwards [hae] with ω hω
      have : Tendsto (fun k => Gm m ω - Gm k ω) atTop (𝓝 (Gm m ω - G ω)) :=
        tendsto_const_nhds.sub hω
      exact ((ENNReal.continuous_pow 4).tendsto _).comp ((continuous_enorm.tendsto _).comp this)
    have hG' : AEStronglyMeasurable (fun ω => Gm m ω - G ω) P := (hGm m).sub hG
    rw [eLpNorm_four_pow hG']
    calc ∫⁻ ω, ‖Gm m ω - G ω‖ₑ ^ 4 ∂P
        = ∫⁻ ω, liminf (fun k => ‖Gm m ω - Gm k ω‖ₑ ^ 4) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hpt] with ω hω
          exact hω.liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ ω, ‖Gm m ω - Gm k ω‖ₑ ^ 4 ∂P) atTop := lintegral_liminf_le' hmeasd
      _ ≤ liminf (fun k => gK * (a + e k) ^ 4) atTop := liminf_le_liminf (Eventually.of_forall hdm)
      _ = gK * a ^ 4 := hlimsup.liminf_eq
  -- Step B, C
  have stepB : ∀ m, eLpNorm (fun ω => Gm m ω - G ω) 4 P ≤
      gK ^ (1 / 4 : ℝ) * eLpNorm (fun ω => Gm m ω - G ω) 2 P := fun m => le_of_pow4_le (stepA m)
  have hKne : gK ^ (1 / 4 : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) gK_ne_top
  have hlim4 : Tendsto (fun m => eLpNorm (fun ω => Gm m ω - G ω) 4 P) atTop (𝓝 0) := by
    refine tendsto_zero_of_le ?_ stepB
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hKne)
  refine ⟨hlim4, ?_⟩
  -- finiteness of the fourth moment of `G`
  obtain ⟨m, hm⟩ := (hlim4.eventually (gt_mem_nhds zero_lt_one)).exists
  have hGmfin : eLpNorm (Gm m) 4 P < ∞ := by
    obtain ⟨h2fin, h4⟩ := gauss_N4_le (hGm m).aemeasurable (isCenteredGaussian_linP hξ (n m) (c m))
    refine lt_top_iff_ne_top.2 (ne_top_of_pow4_ne_top ?_)
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top gK_ne_top
      (ENNReal.pow_ne_top h2fin.ne)) h4
  have : G = (Gm m) - (fun ω => Gm m ω - G ω) := by ext ω; simp
  calc eLpNorm G 4 P = eLpNorm ((Gm m) - (fun ω => Gm m ω - G ω)) 4 P := by rw [← this]
    _ ≤ eLpNorm (Gm m) 4 P + eLpNorm (fun ω => Gm m ω - G ω) 4 P := eLpNorm_sub_le (by norm_num)
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hGmfin, hm.trans ENNReal.one_lt_top⟩

end GaussL4

end Aux_s17

section Aux_s18
open ProbabilityTheory

section QuadP
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

/-- The finite centered quadratic polynomial `∑_{i,j<n} (ξ_i ξ_j - δ_ij) • C i j`. -/
def quadP (ξ : ℕ → Ω → ℝ) (n : ℕ) (C : ℕ → ℕ → B) (ω : Ω) : B :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (ξ i ω * ξ j ω - if i = j then 1 else 0) • C i j

lemma quadP_eq_Dfin (ξ : ℕ → Ω → ℝ) (n : ℕ) (C : ℕ → ℕ → B) (ω : Ω) :
    quadP ξ n C ω = Dfin ξ n (fun i j : Fin n => C i j) ω := by
  unfold quadP Dfin
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Fin.ext_iff]

lemma aesm_quadP (hξ : IsStdGaussianSeq P ξ) (n : ℕ) (C : ℕ → ℕ → B) :
    AEStronglyMeasurable (quadP ξ n C) P := by
  have : quadP ξ n C = fun ω => Qfun (fun i j : Fin n => C i j) (Zvec ξ n ω) :=
    funext fun ω => quadP_eq_Dfin ξ n C ω
  rw [this]
  exact ((continuous_Qfun _).measurable.comp_aemeasurable (aemeasurable_Zvec hξ n)).aestronglyMeasurable

lemma eLpNorm_quadP_lt_top (hξ : IsStdGaussianSeq P ξ) (n : ℕ) (C : ℕ → ℕ → B) :
    eLpNorm (quadP ξ n C) 2 P < ∞ := by
  set c : Fin n → Fin n → B := fun i j => C i j with hc
  set S : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖c i j‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hint : Integrable (fun ω => ‖Qfun c (Zvec ξ n ω)‖ ^ 2) P := by
    refine integrable_comp_Zvec hξ n (g := fun z => ‖Qfun c z‖ ^ 2)
      ((continuous_Qfun c).norm.pow 2) (C := S ^ 2) (k := 4) fun z => ?_
    rw [abs_of_nonneg (by positivity)]
    calc ‖Qfun c z‖ ^ 2 ≤ (S * (1 + ‖z‖) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_Qfun_le c z) 2
      _ = S ^ 2 * (1 + ‖z‖) ^ 4 := by ring
  have h1 := hint.lintegral_lt_top
  have hq : quadP ξ n C = fun ω => Qfun c (Zvec ξ n ω) := funext fun ω => quadP_eq_Dfin ξ n C ω
  have hs := (aesm_quadP hξ n C)
  have : eLpNorm (quadP ξ n C) 2 P ^ 2 < ∞ := by
    rw [eLpNorm_two_pow hs]
    refine lt_of_le_of_lt (le_of_eq ?_) h1
    refine lintegral_congr fun ω => ?_
    rw [hq, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at this
  simp at this

/-- Zero-padding of a double coefficient array. -/
def padm (n : ℕ) (C : ℕ → ℕ → B) : ℕ → ℕ → B := fun i j => if i < n ∧ j < n then C i j else 0

lemma quadP_pad (ξ : ℕ → Ω → ℝ) {n N : ℕ} (h : n ≤ N) (C : ℕ → ℕ → B) (ω : Ω) :
    quadP ξ n C ω = quadP ξ N (padm n C) ω := by
  unfold quadP
  symm
  rw [← Finset.sum_subset (Finset.range_subset_range.2 h)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [← Finset.sum_subset (Finset.range_subset_range.2 h)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp [padm, hi', Finset.mem_range.1 hj]
    · intro j _ hj
      have : ¬ j < n := fun hh => hj (Finset.mem_range.2 hh)
      simp [padm, this]
  · intro i _ hi
    have : ¬ i < n := fun hh => hi (Finset.mem_range.2 hh)
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [padm, this]

end QuadP

end Aux_s18

section Aux_s19
open ProbabilityTheory

section Glue
set_option maxSynthPendingDepth 3
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

lemma second_finite (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) (n n' : ℕ)
    (f : ℕ → B) (C : ℕ → ℕ → B) :
    ∫ ω, fderiv ℝ Φ (linP ξ n f ω) (quadP ξ n' C ω) ∂P =
      (1 / 2) * ∫ p : Ω × Ω, iteratedFDeriv ℝ 3 Φ (linP ξ n f p.1)
        ![quadP ξ n' C p.2, linP ξ n f p.2, linP ξ n f p.2] ∂(P.prod P) := by
  set N := n + n' with hN
  set w : Fin N → B := fun i => padv n f i with hw
  set c : Fin N → Fin N → B := fun i j => padm n' C i j with hc
  have e1 : ∀ ω, linP ξ n f ω = Tmap w (Zvec ξ N ω) := fun ω => by
    rw [linP_pad ξ (Nat.le_add_right n n') f ω, linP_eq_Tmap]
  have e2 : ∀ ω, quadP ξ n' C ω = Dfin ξ N c ω := fun ω => by
    rw [quadP_pad ξ (Nat.le_add_left n' n) C ω, quadP_eq_Dfin]
  simp_rw [e1, e2]
  exact fin2_identity hξ hΦ w c

end Glue

end Aux_s19

section Aux_s20
open ProbabilityTheory

section Final
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma eLpNorm_tendsto_of_lintegral {E : Type*} [NormedAddCommGroup E] {F : ℕ → Ω → E}
    {f : Ω → E} {q : ℝ} (hq : 0 < q) (hF : ∀ m, AEStronglyMeasurable (F m) P)
    (hf : AEStronglyMeasurable f P)
    (h : Tendsto (fun m => ∫⁻ ω, ‖F m ω - f ω‖ₑ ^ q ∂P) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm (fun ω => F m ω - f ω) (ENNReal.ofReal q) P) atTop (𝓝 0) := by
  have e : ∀ m, eLpNorm (fun ω => F m ω - f ω) (ENNReal.ofReal q) P =
      (∫⁻ ω, ‖F m ω - f ω‖ₑ ^ q ∂P) ^ (1 / q) := fun m => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq) ENNReal.ofReal_ne_top
      (show AEStronglyMeasurable (fun ω => F m ω - f ω) P from (hF m).sub hf),
      ENNReal.toReal_ofReal hq.le]
  simp_rw [e]
  have := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto 0).comp h
  have h0 : (0 : ℝ≥0∞) ^ (1 / q) = 0 := ENNReal.zero_rpow_of_pos (one_div_pos.2 hq)
  rw [h0] at this
  exact this

lemma eLpNorm_lt_top_of_approx {E : Type*} [NormedAddCommGroup E] {F : ℕ → Ω → E} {f : Ω → E}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hF : ∀ m, eLpNorm (F m) p P < ∞)
    (h : Tendsto (fun m => eLpNorm (fun ω => F m ω - f ω) p P) atTop (𝓝 0)) :
    eLpNorm f p P < ∞ := by
  obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
  have : f = (F m) - (fun ω => F m ω - f ω) := by ext ω; simp
  calc eLpNorm f p P = eLpNorm ((F m) - (fun ω => F m ω - f ω)) p P := by rw [← this]
    _ ≤ eLpNorm (F m) p P + eLpNorm (fun ω => F m ω - f ω) p P := eLpNorm_sub_le hp
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hF m, hm.trans ENNReal.one_lt_top⟩

end Final

end Aux_s20

end Contr

open Contr

/-- Lemma 7.3 `M:F:lem:contractions`, display `F:eq:secondcontract` (lines 7805-7819): for `G`
centered Gaussian measurable with respect to the Gaussian space of `ξ`, and `D` in its centered
second chaos (for sufficiently large finite `q`), with all displayed moments finite,
`E[DΦ(G)[D]] = ½ E[⟨D³Φ(G), E[D ⊗ G ⊗ G]⟩]`, the right side represented by an independent
copy `(D', G')` of `(D, G)`. -/
theorem gaussian_second_contraction (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ)
    (G : Ω → B) (hG : IsCenteredGaussian (law P G)) (hGmeas : InFirstChaos P ξ 2 G)
    (D : Ω → B) (q : ℝ) (hq : 3 ≤ q) (hD : InSecondChaos P ξ q D)
    (Φ : B → ℝ) (hΦ : MemCb 3 Φ)
    (hint1 : Integrable (fun ω => fderiv ℝ Φ (G ω) (D ω)) P)
    (hint3 : Integrable (fun p : Ω × Ω => iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, G p.2, G p.2])
      (P.prod P)) :
    ∫ ω, fderiv ℝ Φ (G ω) (D ω) ∂P =
      (1 / 2) * ∫ p : Ω × Ω, iteratedFDeriv ℝ 3 Φ (G p.1) ![D p.2, G p.2, G p.2] ∂(P.prod P) := by
  obtain ⟨hGas, n, c, hGlim⟩ := hGmeas
  obtain ⟨hDas, n', C, hDlim⟩ := hD
  have hGm : ∀ m, AEStronglyMeasurable (linP ξ (n m) (c m)) P := fun m => aesm_linP hξ _ _
  have hDm : ∀ m, AEStronglyMeasurable (quadP ξ (n' m) (C m)) P := fun m => aesm_quadP hξ _ _
  have hG2 : Tendsto (fun m => eLpNorm (fun ω => linP ξ (n m) (c m) ω - G ω) 2 P) atTop (𝓝 0) := by
    have := eLpNorm_tendsto_of_lintegral (q := 2) (by norm_num) hGm hGas hGlim
    simpa using this
  have hD2 : Tendsto (fun m => eLpNorm (fun ω => quadP ξ (n' m) (C m) ω - D ω) 2 P) atTop (𝓝 0) := by
    have := eLpNorm_tendsto_of_lintegral (q := q) (by linarith) hDm hDas hDlim
    refine tendsto_zero_of_le this fun m => eLpNorm_le_eLpNorm_of_exponent_le ?_
    calc (2 : ℝ≥0∞) ≤ ENNReal.ofReal 3 := by norm_num
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq
  -- a.e.-convergent subsequence
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (f := fun m => linP ξ (n m) (c m))
    (g := G) (p := 2) (by norm_num) hG2).exists_seq_tendsto_ae
  have hG2φ := hG2.comp hφ.tendsto_atTop
  have hD2φ := hD2.comp hφ.tendsto_atTop
  obtain ⟨hG4, hG4fin⟩ := chaos1_L4 hξ (fun k => n (φ k)) (fun k => c (φ k)) hGas hae hG2φ
  have hD2fin : eLpNorm D 2 P < ∞ :=
    eLpNorm_lt_top_of_approx (F := fun k => quadP ξ (n' (φ k)) (C (φ k))) (by norm_num)
      (fun k => eLpNorm_quadP_lt_top hξ _ _) hD2φ
  have hL := second_lhs_tendsto hΦ hGas hDas (fun k => hGm (φ k)) (fun k => hDm (φ k)) hG4 hD2φ
    hD2fin hint1
  have hR := second_rhs_tendsto hΦ hGas hDas (fun k => hGm (φ k)) (fun k => hDm (φ k)) hae hG4
    hD2φ hG4fin hD2fin hint3
  have hR' := hR.const_mul (1 / 2 : ℝ)
  have hL' : Tendsto (fun k => (1 / 2 : ℝ) * ∫ p : Ω × Ω, iteratedFDeriv ℝ 3 Φ
      (linP ξ (n (φ k)) (c (φ k)) p.1) ![quadP ξ (n' (φ k)) (C (φ k)) p.2,
        linP ξ (n (φ k)) (c (φ k)) p.2, linP ξ (n (φ k)) (c (φ k)) p.2] ∂(P.prod P)) atTop
      (𝓝 (∫ ω, fderiv ℝ Φ (G ω) (D ω) ∂P)) :=
    hL.congr fun k => (second_finite hξ hΦ _ _ _ _)
  exact tendsto_nhds_unique hL' hR'

/-! #### Representation of `B ⊗̂π B` and `B^{⊗̂π 3}` for display `F:eq:firstcontract`

The source (M L7805-7819) takes `J ∈ B^{⊗̂π 2}` (completed projective tensor square) in the first
chaos and pairs `D²Φ(G)` with `J` and `D³Φ(G)` with `E[J ⊗ G] ∈ B^{⊗̂π 3}`. Mathlib at this pin has
the projective seminorm only on the algebraic tensor product (`PiTensorProduct.projectiveSeminorm`,
with `PiTensorProduct.norm_eval_le_projectiveSeminorm : ‖⟨M, x⟩‖ ≤ ‖M‖ ‖x‖_π`), no completion and
no `J ⊗ G`. We therefore represent `B^{⊗̂π k}` through its canonical isometric image in the dual of
the bounded `k`-linear forms:

* `TensorDual B k := (B [×k]→L[ℝ] ℝ) →L[ℝ] ℝ`; the elementary tensor `x₁ ⊗ ⋯ ⊗ x_k` is the
  evaluation functional `elemTensor x = (M ↦ M x)`;
* `projTensor B k` is the closed linear span of the elementary tensors in `TensorDual B k`.

This is faithful: `(B^{⊗̂π k})* = (B [×k]→L[ℝ] ℝ)` isometrically (Ryan, *Introduction to Tensor
Products of Banach Spaces*, Thm. 2.9), so by Hahn–Banach the dual norm of an algebraic tensor
`∑ x₁ ⊗ ⋯ ⊗ x_k` in `TensorDual B k` is its projective norm; the completion `B^{⊗̂π k}` is thus
isometric to the closure `projTensor B k`, the pairing `⟨M, u⟩` is the evaluation `u M`, and the
projective inequality `|⟨M, u⟩| ≤ ‖M‖ ‖u‖_π` used in the source (M L7829-7830) is the operator
norm bound of `u`. For `u ∈ B ⊗̂π B` and `g ∈ B` the tensor `u ⊗ g ∈ B^{⊗̂π 3}` acts on a trilinear
form `M` by `⟨M, u ⊗ g⟩ = u (lastSlot M g)` with `lastSlot M g = ((a, b) ↦ M[a, b, g])`
(true on elementary tensors, extended by linearity and continuity). -/

variable (B) in
/-- The dual of the bounded `k`-linear forms on `B`; carries `B^{⊗̂π k}` (see `projTensor`). -/
abbrev TensorDual (k : ℕ) : Type _ := (B [×k]→L[ℝ] ℝ) →L[ℝ] ℝ

/-- The elementary tensor `x₁ ⊗ ⋯ ⊗ x_k` as the evaluation functional `M ↦ M[x₁, …, x_k]`. -/
def elemTensor {k : ℕ} (v : Fin k → B) : TensorDual B k :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => B) ℝ v

set_option maxSynthPendingDepth 3 in
variable (B) in
/-- `B^{⊗̂π k}` (source `B^{\piten 2}`, M L7808): the closed linear span of the elementary
tensors in `TensorDual B k`; its norm is the projective norm (see the section comment). -/
def projTensor (k : ℕ) : Submodule ℝ (TensorDual B k) :=
  (Submodule.span ℝ (Set.range (elemTensor (B := B) (k := k)))).topologicalClosure

set_option maxSynthPendingDepth 3 in
instance projTensor.instNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (projTensor B k) :=
  Submodule.normedAddCommGroup _

set_option maxSynthPendingDepth 3 in
instance projTensor.instNormedSpace (k : ℕ) : NormedSpace ℝ (projTensor B k) :=
  Submodule.normedSpace _

/-- `lastSlot M g = ((a, b) ↦ M[a, b, g])`: the bounded bilinear form obtained by filling the last
slot of the trilinear form `M` with `g`; `⟨M, u ⊗ g⟩ = u (lastSlot M g)` for `u ∈ B ⊗̂π B`. -/
def lastSlot (M : B [×3]→L[ℝ] ℝ) (g : B) : B [×2]→L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ g).compContinuousMultilinearMap
    (continuousMultilinearCurryRightEquiv' ℝ 2 B ℝ M)

omit [CompleteSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] in
@[simp] lemma elemTensor_apply {k : ℕ} (v : Fin k → B) (M : B [×k]→L[ℝ] ℝ) :
    elemTensor v M = M v := rfl

omit [CompleteSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] in
@[simp] lemma lastSlot_apply (M : B [×3]→L[ℝ] ℝ) (g a b : B) :
    lastSlot M g ![a, b] = M ![a, b, g] := by
  have h : (Fin.snoc ![a, b] g : Fin 3 → B) = ![a, b, g] := by
    ext i; fin_cases i <;> rfl
  simp only [lastSlot, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  show M (Fin.snoc ![a, b] g) = M ![a, b, g]
  rw [h]

/-! #### Auxiliary lemmas for Lemma 7.3 (proof of `gaussian_first_contraction`) -/

namespace Contr

section Aux_s8
open ProbabilityTheory

section Stage1
set_option maxSynthPendingDepth 3
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

lemma hasDerivAt_iterM {Φ : B → ℝ} {k : ℕ} (hΦ : ContDiff ℝ (k + 1) Φ) {N : ℕ}
    (T : (Fin N → ℝ) →L[ℝ] B) (z : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (fun x => iteratedFDeriv ℝ k Φ (T (Function.update z i x)))
      (fderiv ℝ (iteratedFDeriv ℝ k Φ) (T z) (T (Pi.single i 1))) (z i) := by
  have hu : HasDerivAt (fun x => T (Function.update z i x)) (T (Pi.single i 1)) (z i) := by
    have h1 := hasDerivAt_update z i (z i)
    have h2 := T.hasFDerivAt.comp_hasDerivAt (z i) h1
    exact h2
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ k Φ) (T z) :=
    (hΦ.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) (T z)
  have hz : T (Function.update z i (z i)) = T z := by rw [Function.update_eq_self]
  have hF := hD.hasFDerivAt
  rw [← hz] at hF
  have h3 := hF.comp_hasDerivAt (z i) hu
  rw [hz] at h3
  exact h3

lemma fderiv_iter2_eq {Φ : B → ℝ} (hΦ3 : ContDiff ℝ 3 Φ) (y a : B) :
    fderiv ℝ (iteratedFDeriv ℝ 2 Φ) y a = lastSlot (iteratedFDeriv ℝ 3 Φ y) a := by
  ext m
  have hm : m = ![m 0, m 1] := by ext k; fin_cases k <;> rfl
  have h1 := iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := Φ) (x := y) (n := 2)
    (Fin.cons a ![m 0, m 1] : Fin 3 → B)
  have h2 : (Fin.cons a ![m 0, m 1] : Fin 3 → B) = ![a, m 0, m 1] := rfl
  rw [h2] at h1
  rw [hm]
  rw [lastSlot_apply, ← iter3_cyc hΦ3 y a (m 0) (m 1), h1]
  rfl

lemma norm_lastSlot_le (M : B [×3]→L[ℝ] ℝ) (g : B) : ‖lastSlot M g‖ ≤ ‖M‖ * ‖g‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hm : m = ![m 0, m 1] := by ext k; fin_cases k <;> rfl
  have h := abs_tri_le M (m 0) (m 1) g
  rw [Real.norm_eq_abs]
  conv_lhs => rw [hm, lastSlot_apply]
  simp only [Fin.prod_univ_two]
  calc |M ![m 0, m 1, g]| ≤ ‖M‖ * (‖m 0‖ * ‖m 1‖ * ‖g‖) := h
    _ = ‖M‖ * ‖g‖ * (‖m 0‖ * ‖m 1‖) := by ring

/-- `M ↦ (g ↦ lastSlot M g)` as a continuous map into continuous linear maps. -/
def lastSlotL (M : B [×3]→L[ℝ] ℝ) : B →L[ℝ] (B [×2]→L[ℝ] ℝ) :=
  (ContinuousLinearMap.flipMultilinearEquiv ℝ (fun _ : Fin 2 => B) B ℝ).symm
    (continuousMultilinearCurryRightEquiv' ℝ 2 B ℝ M)

lemma lastSlotL_apply (M : B [×3]→L[ℝ] ℝ) (g : B) : lastSlotL M g = lastSlot M g := by
  ext m
  rfl

lemma continuous_lastSlotL : Continuous fun M : B [×3]→L[ℝ] ℝ => lastSlotL M :=
  (ContinuousLinearMap.flipMultilinearEquiv ℝ (fun _ : Fin 2 => B) B ℝ).symm.continuous.comp
    (continuousMultilinearCurryRightEquiv' ℝ 2 B ℝ).continuous

lemma continuous_lastSlot2 {X : Type*} [TopologicalSpace X] {f : X → B [×3]→L[ℝ] ℝ} {h : X → B}
    (hf : Continuous f) (hh : Continuous h) : Continuous fun x => lastSlot (f x) (h x) := by
  have := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B) (F := B [×2]→L[ℝ] ℝ)).continuous
  exact this.comp ((continuous_lastSlotL.comp hf).prodMk hh)

lemma lastSlot_sum {ι : Type*} (M : B [×3]→L[ℝ] ℝ) (s : Finset ι) (f : ι → ℝ) (w : ι → B) :
    lastSlot M (∑ i ∈ s, f i • w i) = ∑ i ∈ s, f i • lastSlot M (w i) := by
  simp only [← lastSlotL_apply, map_sum, map_smul]


/-- the polynomial `∑ z_i • t_i` with values in `TensorDual B 2` -/
def Jfun {N : ℕ} (t : Fin N → TensorDual B 2) (z : Fin N → ℝ) : TensorDual B 2 :=
  ∑ i, z i • t i

lemma continuous_Jfun {N : ℕ} (t : Fin N → TensorDual B 2) : Continuous (Jfun t) := by
  unfold Jfun
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

lemma norm_Jfun_le {N : ℕ} (t : Fin N → TensorDual B 2) (z : Fin N → ℝ) :
    ‖Jfun t z‖ ≤ (∑ i, ‖t i‖) * ‖z‖ := by
  unfold Jfun
  calc ‖∑ i, z i • t i‖ ≤ ∑ i, ‖z i • t i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖z‖ * ‖t i‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm z i) (norm_nonneg _)
    _ = (∑ i, ‖t i‖) * ‖z‖ := by rw [← Finset.mul_sum]; ring

lemma Jfun_apply {N : ℕ} (t : Fin N → TensorDual B 2) (z : Fin N → ℝ)
    (m : B [×2]→L[ℝ] ℝ) : Jfun t z m = ∑ i, z i * t i m := by
  simp [Jfun]

lemma integrable_fin1A (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (tt : TensorDual B 2) (i : Fin N) :
    Integrable (fun ω => ξ i ω * tt (iteratedFDeriv ℝ 2 Φ (Tmap w (Zvec ξ N ω)))) P := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hc2 : Continuous (iteratedFDeriv ℝ 2 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  refine integrable_comp_Zvec hξ N (g := fun z => z i * tt (iteratedFDeriv ℝ 2 Φ (Tmap w z)))
    ((continuous_apply i).mul (tt.continuous.comp (hc2.comp (Tmap w).continuous)))
    (C := ‖tt‖ * K) (k := 1) (fun z => ?_)
  rw [abs_mul]
  have h1 : |z i| ≤ 1 + ‖z‖ := by
    have := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at this; linarith [norm_nonneg z]
  have h2 : |tt (iteratedFDeriv ℝ 2 Φ (Tmap w z))| ≤ ‖tt‖ * K := by
    rw [← Real.norm_eq_abs]
    exact (tt.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hK 2 (by norm_num) _) (norm_nonneg _))
  calc |z i| * |tt (iteratedFDeriv ℝ 2 Φ (Tmap w z))| ≤ (1 + ‖z‖) * (‖tt‖ * K) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by linarith [norm_nonneg z])
    _ = ‖tt‖ * K * (1 + ‖z‖) ^ 1 := by ring

lemma integrable_fin1C (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (tt : TensorDual B 2) (u : B) :
    Integrable (fun ω => tt (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N ω))) u)) P := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hc3 : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  refine integrable_comp_Zvec hξ N
    (g := fun z => tt (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w z)) u))
    (tt.continuous.comp (continuous_lastSlot2 (hc3.comp (Tmap w).continuous) continuous_const))
    (C := ‖tt‖ * (K * ‖u‖)) (k := 0) (fun z => ?_)
  rw [← Real.norm_eq_abs]
  calc ‖tt (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w z)) u)‖
      ≤ ‖tt‖ * ‖lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w z)) u‖ := tt.le_opNorm _
    _ ≤ ‖tt‖ * (K * ‖u‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_lastSlot_le _ _).trans
          (mul_le_mul_of_nonneg_right (hK 3 (le_refl _) _) (norm_nonneg _))
    _ = ‖tt‖ * (K * ‖u‖) * (1 + ‖z‖) ^ 0 := by ring

lemma fin1_termA (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (tt : TensorDual B 2) (i : Fin N) :
    ∫ ω, ξ i ω * tt (iteratedFDeriv ℝ 2 Φ (Tmap w (Zvec ξ N ω))) ∂P =
      ∫ ω, tt (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N ω))) (w i)) ∂P := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hc2 : Continuous (iteratedFDeriv ℝ 2 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  have hc3 : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  set T := Tmap w with hT
  refine stein_Z hξ i (F := fun z => tt (iteratedFDeriv ℝ 2 Φ (T z)))
    (F' := fun z => tt (lastSlot (iteratedFDeriv ℝ 3 Φ (T z)) (w i))) (fun z => ?_)
    (tt.continuous.comp (hc2.comp T.continuous))
    (tt.continuous.comp (continuous_lastSlot2 (hc3.comp T.continuous) continuous_const))
    (C := ‖tt‖ * (K * (1 + ‖w i‖))) (p := 0) (fun z => ?_)
  · have h1 := hasDerivAt_iterM (Φ := Φ) (k := 2) (hΦ3.of_le (by norm_num)) T z i
    rw [Tmap_single, fderiv_iter2_eq hΦ3] at h1
    exact tt.hasFDerivAt.comp_hasDerivAt (z i) h1
  · have e1 : |tt (iteratedFDeriv ℝ 2 Φ (T z))| ≤ ‖tt‖ * K := by
      rw [← Real.norm_eq_abs]
      exact (tt.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hK 2 (by norm_num) _)
        (norm_nonneg _))
    have e2 : |tt (lastSlot (iteratedFDeriv ℝ 3 Φ (T z)) (w i))| ≤ ‖tt‖ * (K * ‖w i‖) := by
      rw [← Real.norm_eq_abs]
      calc ‖tt (lastSlot (iteratedFDeriv ℝ 3 Φ (T z)) (w i))‖
          ≤ ‖tt‖ * ‖lastSlot (iteratedFDeriv ℝ 3 Φ (T z)) (w i)‖ := tt.le_opNorm _
        _ ≤ ‖tt‖ * (K * ‖w i‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact (norm_lastSlot_le _ _).trans
              (mul_le_mul_of_nonneg_right (hK 3 (le_refl _) _) (norm_nonneg _))
    have hn := norm_nonneg tt
    have hw := norm_nonneg (w i)
    simp only [pow_zero, mul_one]
    constructor
    · refine e1.trans ?_
      nlinarith [mul_nonneg hn hK0, mul_nonneg (mul_nonneg hn hK0) hw]
    · refine e2.trans ?_
      nlinarith [mul_nonneg hn hK0, mul_nonneg (mul_nonneg hn hK0) hw]


lemma Zvec_apply (ξ : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) (i : Fin N) : Zvec ξ N ω i = ξ i ω := rfl

lemma E_xi_xi (hξ : IsStdGaussianSeq P ξ) {N : ℕ} (i k : Fin N) :
    ∫ ω, ξ i ω * ξ k ω ∂P = if k = i then 1 else 0 := by
  have := stein_Z hξ i (N := N) (F := fun z => z k) (F' := fun _ => if k = i then 1 else 0)
    (fun z => by
      by_cases h : k = i
      · subst h
        simp only [ite_true]
        convert hasDerivAt_id (z k) using 1
        ext x; simp
      · simp only [h, ite_false]
        have : (fun x => (Function.update z i x) k) = fun _ => z k := by
          ext x; simp [Function.update_of_ne h]
        simp only [this]
        exact hasDerivAt_const _ _)
    (continuous_apply k) continuous_const (C := 1) (p := 1) (fun z => by
      have h : |z k| ≤ 1 + ‖z‖ := by
        have := norm_le_pi_norm z k
        rw [Real.norm_eq_abs] at this; linarith [norm_nonneg z]
      refine ⟨by simpa using h, ?_⟩
      have : (|(if k = i then (1 : ℝ) else 0)|) ≤ 1 := by split_ifs <;> simp
      have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      simpa using this.trans h1)
  simpa [Zvec] using this

lemma fin1_A (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (t : Fin N → TensorDual B 2) :
    ∫ ω, Jfun t (Zvec ξ N ω) (iteratedFDeriv ℝ 2 Φ (Tmap w (Zvec ξ N ω))) ∂P =
      ∑ i : Fin N, ∫ ω, t i (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N ω))) (w i)) ∂P := by
  simp_rw [Jfun_apply, Zvec_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_fin1A hξ hΦ w (t i) i)]
  exact Finset.sum_congr rfl fun i _ => fin1_termA hξ hΦ w (t i) i

lemma integrable_prod1 (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (t : Fin N → TensorDual B 2) :
    Integrable (fun p : Ω × Ω => Jfun t (Zvec ξ N p.2)
      (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N p.1))) (Tmap w (Zvec ξ N p.2))))
      (P.prod P) := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hc3 : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  set T := Tmap w with hT
  set A : ℝ := ∑ k, ‖w k‖ with hA
  set Ct : ℝ := ∑ i, ‖t i‖ with hCt
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg fun i _ => norm_nonneg _
  let F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun q =>
    Jfun t q.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (T q.1)) (T q.2))
  have hFc : Continuous F := by
    have := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B [×2]→L[ℝ] ℝ) (F := ℝ)).continuous
    exact this.comp (((continuous_Jfun t).comp continuous_snd).prodMk
      (continuous_lastSlot2 (hc3.comp (T.continuous.comp continuous_fst))
        (T.continuous.comp continuous_snd)))
  have hmeas : AEStronglyMeasurable (fun p : Ω × Ω => F (Zvec ξ N p.1, Zvec ξ N p.2))
      (P.prod P) := by
    have hZ : AEStronglyMeasurable (Zvec ξ N) P := (aemeasurable_Zvec hξ N).aestronglyMeasurable
    exact hFc.comp_aestronglyMeasurable (hZ.comp_fst.prodMk hZ.comp_snd)
  have hbd : Integrable (fun y : Ω => K * (Ct * ‖Zvec ξ N y‖) * ‖T (Zvec ξ N y)‖) P := by
    refine integrable_comp_Zvec hξ N (g := fun z => K * (Ct * ‖z‖) * ‖T z‖)
      ((continuous_const.mul (continuous_const.mul continuous_norm)).mul T.continuous.norm)
      (C := K * Ct * A) (k := 2) (fun z => ?_)
    have hz0 := norm_nonneg z
    have hT' : ‖T z‖ ≤ A * ‖z‖ := norm_Tmap_le w z
    rw [abs_of_nonneg (by positivity)]
    calc K * (Ct * ‖z‖) * ‖T z‖ ≤ K * (Ct * ‖z‖) * (A * ‖z‖) := by gcongr
      _ = K * Ct * A * ‖z‖ ^ 2 := by ring
      _ ≤ K * Ct * A * (1 + ‖z‖) ^ 2 := by gcongr; nlinarith
  refine Integrable.mono' (hbd.comp_snd P) hmeas (Eventually.of_forall fun p => ?_)
  show ‖F (Zvec ξ N p.1, Zvec ξ N p.2)‖ ≤ _
  simp only [F]
  calc ‖Jfun t (Zvec ξ N p.2) (lastSlot (iteratedFDeriv ℝ 3 Φ (T (Zvec ξ N p.1)))
        (T (Zvec ξ N p.2)))‖
      ≤ ‖Jfun t (Zvec ξ N p.2)‖ * ‖lastSlot (iteratedFDeriv ℝ 3 Φ (T (Zvec ξ N p.1)))
        (T (Zvec ξ N p.2))‖ := (Jfun t _).le_opNorm _
    _ ≤ (Ct * ‖Zvec ξ N p.2‖) * (K * ‖T (Zvec ξ N p.2)‖) := by
        refine mul_le_mul (norm_Jfun_le t _) ((norm_lastSlot_le _ _).trans
          (mul_le_mul_of_nonneg_right (hK 3 (le_refl _) _) (norm_nonneg _))) (norm_nonneg _)
          (by positivity)
    _ = K * (Ct * ‖Zvec ξ N p.2‖) * ‖T (Zvec ξ N p.2)‖ := by ring


lemma integrable_xx (hξ : IsStdGaussianSeq P ξ) {N : ℕ} (i k : Fin N) (c : ℝ) :
    Integrable (fun ω => ξ i ω * ξ k ω * c) P := by
  refine integrable_comp_Zvec hξ N (g := fun z => z i * z k * c)
    (((continuous_apply i).mul (continuous_apply k)).mul continuous_const)
    (C := |c|) (k := 2) (fun z => ?_)
  have hi : |z i| ≤ ‖z‖ := by simpa using norm_le_pi_norm z i
  have hk : |z k| ≤ ‖z‖ := by simpa using norm_le_pi_norm z k
  have h0 := norm_nonneg z
  rw [abs_mul, abs_mul]
  have : |z i| * |z k| ≤ (1 + ‖z‖) ^ 2 := by
    calc |z i| * |z k| ≤ ‖z‖ * ‖z‖ := mul_le_mul hi hk (abs_nonneg _) h0
      _ ≤ (1 + ‖z‖) ^ 2 := by nlinarith
  calc |z i| * |z k| * |c| ≤ (1 + ‖z‖) ^ 2 * |c| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = |c| * (1 + ‖z‖) ^ 2 := by ring

lemma fin1_B (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (t : Fin N → TensorDual B 2) :
    ∫ p : Ω × Ω, Jfun t (Zvec ξ N p.2)
      (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N p.1))) (Tmap w (Zvec ξ N p.2)))
        ∂(P.prod P) =
      ∑ i : Fin N, ∫ ω, t i (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N ω))) (w i)) ∂P := by
  rw [integral_prod _ (integrable_prod1 hξ hΦ w t)]
  have inner : ∀ x : Ω, ∫ y, Jfun t (Zvec ξ N y)
      (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N x))) (Tmap w (Zvec ξ N y))) ∂P =
      ∑ i : Fin N, t i (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N x))) (w i)) := by
    intro x
    set M := iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N x)) with hM
    have e : ∀ y, Jfun t (Zvec ξ N y) (lastSlot M (Tmap w (Zvec ξ N y))) =
        ∑ i : Fin N, ∑ k : Fin N, ξ i y * ξ k y * t i (lastSlot M (w k)) := by
      intro y
      rw [Jfun_apply, Tmap_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lastSlot_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, smul_eq_mul, Zvec_apply, Zvec_apply]
      ring
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun k _ =>
      integrable_xx hξ i k _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => integrable_xx hξ i k _)]
    simp_rw [integral_mul_const, E_xi_xi hξ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · simp
  simp_rw [inner]
  rw [integral_finsetSum _ (fun i _ => integrable_fin1C hξ hΦ w (t i) (w i))]

lemma fin1_identity (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {N : ℕ}
    (w : Fin N → B) (t : Fin N → TensorDual B 2) :
    ∫ ω, Jfun t (Zvec ξ N ω) (iteratedFDeriv ℝ 2 Φ (Tmap w (Zvec ξ N ω))) ∂P =
      ∫ p : Ω × Ω, Jfun t (Zvec ξ N p.2)
        (lastSlot (iteratedFDeriv ℝ 3 Φ (Tmap w (Zvec ξ N p.1))) (Tmap w (Zvec ξ N p.2)))
          ∂(P.prod P) := by
  rw [fin1_A hξ hΦ w t, fin1_B hξ hΦ w t]

end Stage1

end Aux_s8

section Aux_s12
open ProbabilityTheory

section PointwiseFirst
set_option maxSynthPendingDepth 3
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma lastSlot_sub_right (M : B [×3]→L[ℝ] ℝ) (g g' : B) :
    lastSlot M (g - g') = lastSlot M g - lastSlot M g' := by
  ext m
  have hm : m = ![m 0, m 1] := by ext k; fin_cases k <;> rfl
  rw [hm]
  simp only [lastSlot_apply, sub_apply]
  exact tri_sub3 M _ _ _ _

lemma lastSlot_sub_left (M M' : B [×3]→L[ℝ] ℝ) (g : B) :
    lastSlot (M - M') g = lastSlot M g - lastSlot M' g := by
  ext m
  have hm : m = ![m 0, m 1] := by ext k; fin_cases k <;> rfl
  rw [hm]
  simp only [lastSlot_apply, sub_apply]

lemma abs_J_lastSlot_diff_le (J J' : TensorDual B 2) (M M' : B [×3]→L[ℝ] ℝ) (g g' : B) :
    |J (lastSlot M g) - J' (lastSlot M' g')| ≤
      ‖J - J'‖ * (‖M‖ * ‖g‖) + ‖J'‖ * (‖M‖ * ‖g - g'‖) + ‖J'‖ * (‖M - M'‖ * ‖g'‖) := by
  have e : J (lastSlot M g) - J' (lastSlot M' g') =
      (J - J') (lastSlot M g) + (J' (lastSlot M (g - g')) + J' (lastSlot (M - M') g')) := by
    rw [lastSlot_sub_right, lastSlot_sub_left]
    simp only [sub_apply, map_sub]
    ring
  rw [e]
  have hJ : ∀ (K : TensorDual B 2) (m : B [×2]→L[ℝ] ℝ), |K m| ≤ ‖K‖ * ‖m‖ := fun K m => by
    have := K.le_opNorm m
    rwa [Real.norm_eq_abs] at this
  have h1 := (hJ (J - J') (lastSlot M g)).trans
    (mul_le_mul_of_nonneg_left (norm_lastSlot_le M g) (norm_nonneg _))
  have h2 := (hJ J' (lastSlot M (g - g'))).trans
    (mul_le_mul_of_nonneg_left (norm_lastSlot_le M (g - g')) (norm_nonneg _))
  have h3 := (hJ J' (lastSlot (M - M') g')).trans
    (mul_le_mul_of_nonneg_left (norm_lastSlot_le (M - M') g') (norm_nonneg _))
  have a1 := abs_add_le ((J - J') (lastSlot M g)) (J' (lastSlot M (g - g')) + J' (lastSlot (M - M') g'))
  have a2 := abs_add_le (J' (lastSlot M (g - g'))) (J' (lastSlot (M - M') g'))
  nlinarith

lemma enorm_J_lastSlot_diff_le (J J' : TensorDual B 2) (M M' : B [×3]→L[ℝ] ℝ) (g g' : B) :
    ‖J (lastSlot M g) - J' (lastSlot M' g')‖ₑ ≤
      ‖J - J'‖ₑ * (‖M‖ₑ * ‖g‖ₑ) + ‖J'‖ₑ * (‖M‖ₑ * ‖g - g'‖ₑ) + ‖J'‖ₑ * (‖M - M'‖ₑ * ‖g'‖ₑ) := by
  have h := abs_J_lastSlot_diff_le J J' M M' g g'
  calc ‖J (lastSlot M g) - J' (lastSlot M' g')‖ₑ
      = ENNReal.ofReal |J (lastSlot M g) - J' (lastSlot M' g')| := by
        rw [← Real.norm_eq_abs, ofReal_norm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h
    _ = _ := by
        simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul, ofReal_norm]

lemma abs_J_iter2_diff_le {Φ : B → ℝ} (hΦ : ContDiff ℝ 3 Φ) {K2 K3 : ℝ}
    (hK2 : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ K2) (hK3 : ∀ y, ‖iteratedFDeriv ℝ 3 Φ y‖ ≤ K3)
    (J J' : TensorDual B 2) (y y' : B) :
    |J (iteratedFDeriv ℝ 2 Φ y) - J' (iteratedFDeriv ℝ 2 Φ y')| ≤
      K2 * ‖J - J'‖ + K3 * (‖J'‖ * ‖y - y'‖) := by
  have hJ : ∀ (K : TensorDual B 2) (m : B [×2]→L[ℝ] ℝ), |K m| ≤ ‖K‖ * ‖m‖ := fun K m => by
    have := K.le_opNorm m
    rwa [Real.norm_eq_abs] at this
  have e : J (iteratedFDeriv ℝ 2 Φ y) - J' (iteratedFDeriv ℝ 2 Φ y') =
      (J - J') (iteratedFDeriv ℝ 2 Φ y) +
        J' (iteratedFDeriv ℝ 2 Φ y - iteratedFDeriv ℝ 2 Φ y') := by
    simp only [sub_apply, map_sub]; ring
  rw [e]
  have hl : ‖iteratedFDeriv ℝ 2 Φ y - iteratedFDeriv ℝ 2 Φ y'‖ ≤ K3 * ‖y - y'‖ :=
    lip_iter (k := 2) hΦ (fun z => hK3 z) y y'
  have h1 := (hJ (J - J') (iteratedFDeriv ℝ 2 Φ y)).trans
    (mul_le_mul_of_nonneg_left (hK2 y) (norm_nonneg _))
  have h2 := (hJ J' _).trans (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
  have a1 := abs_add_le ((J - J') (iteratedFDeriv ℝ 2 Φ y))
    (J' (iteratedFDeriv ℝ 2 Φ y - iteratedFDeriv ℝ 2 Φ y'))
  nlinarith

lemma enorm_J_iter2_diff_le {Φ : B → ℝ} (hΦ : ContDiff ℝ 3 Φ) {K2 K3 : ℝ} (hK20 : 0 ≤ K2)
    (hK30 : 0 ≤ K3)
    (hK2 : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ K2) (hK3 : ∀ y, ‖iteratedFDeriv ℝ 3 Φ y‖ ≤ K3)
    (J J' : TensorDual B 2) (y y' : B) :
    ‖J (iteratedFDeriv ℝ 2 Φ y) - J' (iteratedFDeriv ℝ 2 Φ y')‖ₑ ≤
      ENNReal.ofReal K2 * ‖J - J'‖ₑ + ENNReal.ofReal K3 * (‖J'‖ₑ * ‖y - y'‖ₑ) := by
  have h := abs_J_iter2_diff_le hΦ hK2 hK3 J J' y y'
  calc ‖J (iteratedFDeriv ℝ 2 Φ y) - J' (iteratedFDeriv ℝ 2 Φ y')‖ₑ
      = ENNReal.ofReal |J (iteratedFDeriv ℝ 2 Φ y) - J' (iteratedFDeriv ℝ 2 Φ y')| := by
        rw [← Real.norm_eq_abs, ofReal_norm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h
    _ = _ := by
        simp (disch := positivity) only [ENNReal.ofReal_add, ENNReal.ofReal_mul, ofReal_norm]

end PointwiseFirst

end Aux_s12

section Aux_s15
open ProbabilityTheory

section Abstract3
set_option maxSynthPendingDepth 3
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma continuous_evalJ :
    Continuous (fun x : TensorDual B 2 × (B [×2]→L[ℝ] ℝ) => x.1 x.2) :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := B [×2]→L[ℝ] ℝ) (F := ℝ)).continuous

lemma continuous_evalJ3 :
    Continuous (fun x : TensorDual B 2 × ((B [×3]→L[ℝ] ℝ) × B) => x.1 (lastSlot x.2.1 x.2.2)) :=
  continuous_evalJ.comp (continuous_fst.prodMk
    (continuous_lastSlot2 (f := fun x : TensorDual B 2 × ((B [×3]→L[ℝ] ℝ) × B) => x.2.1)
      (h := fun x => x.2.2) continuous_snd.fst continuous_snd.snd))

lemma first_lhs_tendsto {Φ : B → ℝ} (hΦ : MemCb 3 Φ)
    {G : Ω → B} {Gm : ℕ → Ω → B} {J : Ω → TensorDual B 2} {Jm : ℕ → Ω → TensorDual B 2}
    (hG : AEStronglyMeasurable G P) (hJ : AEStronglyMeasurable J P)
    (hGm : ∀ m, AEStronglyMeasurable (Gm m) P) (hJm : ∀ m, AEStronglyMeasurable (Jm m) P)
    (hG2 : Tendsto (fun m => eLpNorm (fun ω => Gm m ω - G ω) 2 P) atTop (𝓝 0))
    (hJ2 : Tendsto (fun m => eLpNorm (fun ω => Jm m ω - J ω) 2 P) atTop (𝓝 0))
    (hJ2fin : eLpNorm J 2 P < ∞)
    (hint2 : Integrable (fun ω => J ω (iteratedFDeriv ℝ 2 Φ (G ω))) P) :
    Tendsto (fun m => ∫ ω, Jm m ω (iteratedFDeriv ℝ 2 Φ (Gm m ω)) ∂P) atTop
      (𝓝 (∫ ω, J ω (iteratedFDeriv ℝ 2 Φ (G ω)) ∂P)) := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hc2 : Continuous (iteratedFDeriv ℝ 2 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  have hmeas : ∀ m, AEStronglyMeasurable (fun ω => Jm m ω (iteratedFDeriv ℝ 2 Φ (Gm m ω))) P :=
    fun m => continuous_evalJ.comp_aestronglyMeasurable
      ((hJm m).prodMk (hc2.comp_aestronglyMeasurable (hGm m)))
  refine tendsto_integral_of_lintegral hint2 hmeas ?_
  have hK2 : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ K := fun y => hK 2 (by norm_num) y
  have hK3 : ∀ y, ‖iteratedFDeriv ℝ 3 Φ y‖ ≤ K := fun y => hK 3 (by norm_num) y
  have hpt : ∀ m ω, ‖Jm m ω (iteratedFDeriv ℝ 2 Φ (Gm m ω)) - J ω (iteratedFDeriv ℝ 2 Φ (G ω))‖ₑ ≤
      ENNReal.ofReal K * ‖Jm m ω - J ω‖ₑ + ENNReal.ofReal K * (‖J ω‖ₑ * ‖Gm m ω - G ω‖ₑ) :=
    fun m ω => enorm_J_iter2_diff_le hΦ3 hK0 hK0 hK2 hK3 _ _ _ _
  have hbound : ∀ m, ∫⁻ ω, ‖Jm m ω (iteratedFDeriv ℝ 2 Φ (Gm m ω)) -
      J ω (iteratedFDeriv ℝ 2 Φ (G ω))‖ₑ ∂P ≤
      ENNReal.ofReal K * eLpNorm (fun ω => Jm m ω - J ω) 2 P +
        ENNReal.ofReal K * (eLpNorm J 2 P * eLpNorm (fun ω => Gm m ω - G ω) 2 P) := by
    intro m
    have hJ' : AEStronglyMeasurable (fun ω => Jm m ω - J ω) P := (hJm m).sub hJ
    have hG' : AEStronglyMeasurable (fun ω => Gm m ω - G ω) P := (hGm m).sub hG
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal K * ‖Jm m ω - J ω‖ₑ +
            ENNReal.ofReal K * (‖J ω‖ₑ * ‖Gm m ω - G ω‖ₑ)) ∂P := lintegral_mono (hpt m)
      _ = ENNReal.ofReal K * ∫⁻ ω, ‖Jm m ω - J ω‖ₑ ∂P +
            ENNReal.ofReal K * ∫⁻ ω, ‖J ω‖ₑ * ‖Gm m ω - G ω‖ₑ ∂P := by
          rw [lintegral_add_left' (hJ'.enorm.const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          · rw [← eLpNorm_one_eq_lintegral_enorm hJ']
            exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
          · exact lintegral_mul2_le hJ hG'
  refine tendsto_zero_of_le ?_ hbound
  have h1 : Tendsto (fun m => ENNReal.ofReal K * eLpNorm (fun ω => Jm m ω - J ω) 2 P) atTop
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hJ2 (Or.inr ENNReal.ofReal_ne_top)
  have h2 : Tendsto (fun m => ENNReal.ofReal K *
      (eLpNorm J 2 P * eLpNorm (fun ω => Gm m ω - G ω) 2 P)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := eLpNorm J 2 P) hG2 (Or.inr hJ2fin.ne)
    simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) this (Or.inr ENNReal.ofReal_ne_top)
  simpa using h1.add h2

lemma first_rhs_tendsto {Φ : B → ℝ} (hΦ : MemCb 3 Φ)
    {G : Ω → B} {Gm : ℕ → Ω → B} {J : Ω → TensorDual B 2} {Jm : ℕ → Ω → TensorDual B 2}
    (hG : AEStronglyMeasurable G P) (hJ : AEStronglyMeasurable J P)
    (hGm : ∀ m, AEStronglyMeasurable (Gm m) P) (hJm : ∀ m, AEStronglyMeasurable (Jm m) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun m => Gm m ω) atTop (𝓝 (G ω)))
    (hG2 : Tendsto (fun m => eLpNorm (fun ω => Gm m ω - G ω) 2 P) atTop (𝓝 0))
    (hJ2 : Tendsto (fun m => eLpNorm (fun ω => Jm m ω - J ω) 2 P) atTop (𝓝 0))
    (hG2fin : eLpNorm G 2 P < ∞) (hJ2fin : eLpNorm J 2 P < ∞)
    (hint3 : Integrable (fun p : Ω × Ω =>
      J p.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2))) (P.prod P)) :
    Tendsto (fun m => ∫ p : Ω × Ω,
      Jm m p.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (Gm m p.1)) (Gm m p.2)) ∂(P.prod P)) atTop
      (𝓝 (∫ p : Ω × Ω, J p.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2)) ∂(P.prod P))) := by
  obtain ⟨K, hK0, hK⟩ := memCb_bound hΦ
  have hΦ3 : ContDiff ℝ 3 Φ := hΦ.1
  have hK3 : ∀ y, ‖iteratedFDeriv ℝ 3 Φ y‖ ≤ K := fun y => hK 3 le_rfl y
  have hc : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ3.continuous_iteratedFDeriv (by norm_num)
  have hmeasT : ∀ (Gx : Ω → B) (Jx : Ω → TensorDual B 2), AEStronglyMeasurable Gx P →
      AEStronglyMeasurable Jx P → ∀ (Hx : Ω → B), AEStronglyMeasurable Hx P →
      AEStronglyMeasurable (fun p : Ω × Ω =>
        Jx p.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (Gx p.1)) (Hx p.2))) (P.prod P) :=
    fun Gx Jx hGx hJx Hx hHx => continuous_evalJ3.comp_aestronglyMeasurable
      (hJx.comp_snd.prodMk ((hc.comp_aestronglyMeasurable hGx.comp_fst).prodMk hHx.comp_snd))
  refine tendsto_integral_of_lintegral hint3 (fun m => hmeasT (Gm m) (Jm m) (hGm m) (hJm m) (Gm m) (hGm m)) ?_
  set a : ℕ → Ω → ℝ≥0∞ :=
    fun m ω => ‖iteratedFDeriv ℝ 3 Φ (Gm m ω) - iteratedFDeriv ℝ 3 Φ (G ω)‖ₑ with ha_def
  set h0 : Ω → ℝ≥0∞ := fun ω => ‖J ω‖ₑ * ‖G ω‖ₑ with hh0_def
  set h1 : ℕ → Ω → ℝ≥0∞ := fun m ω => ‖Jm m ω - J ω‖ₑ * ‖Gm m ω‖ₑ + ‖J ω‖ₑ * ‖Gm m ω - G ω‖ₑ
    with hh1_def
  have ha_meas : ∀ m, AEMeasurable (a m) P := fun m =>
    ((hc.comp_aestronglyMeasurable (hGm m)).sub (hc.comp_aestronglyMeasurable hG)).enorm
  have hh0_meas : AEMeasurable h0 P := hJ.enorm.mul hG.enorm
  have hh1_meas : ∀ m, AEMeasurable (h1 m) P := fun m =>
    (((hJm m).sub hJ).enorm.mul (hGm m).enorm).add (hJ.enorm.mul ((hGm m).sub hG).enorm)
  have hpt : ∀ m (p : Ω × Ω),
      ‖Jm m p.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (Gm m p.1)) (Gm m p.2)) -
        J p.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2))‖ₑ ≤
        a m p.1 * h0 p.2 + ENNReal.ofReal K * h1 m p.2 := by
    intro m p
    refine (enorm_J_lastSlot_diff_le _ _ _ _ _ _).trans ?_
    have hKe : ‖iteratedFDeriv ℝ 3 Φ (Gm m p.1)‖ₑ ≤ ENNReal.ofReal K := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hK3 _)
    calc _ ≤ ‖Jm m p.2 - J p.2‖ₑ * (ENNReal.ofReal K * ‖Gm m p.2‖ₑ) +
          ‖J p.2‖ₑ * (ENNReal.ofReal K * ‖Gm m p.2 - G p.2‖ₑ) +
          ‖J p.2‖ₑ * (‖iteratedFDeriv ℝ 3 Φ (Gm m p.1) - iteratedFDeriv ℝ 3 Φ (G p.1)‖ₑ *
            ‖G p.2‖ₑ) := by gcongr
      _ = _ := by simp only [ha_def, hh0_def, hh1_def]; ring
  have hint : ∀ m, ∫⁻ p : Ω × Ω, ‖Jm m p.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (Gm m p.1)) (Gm m p.2)) -
        J p.2 (lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2))‖ₑ ∂(P.prod P) ≤
      (∫⁻ ω, a m ω ∂P) * (∫⁻ ω, h0 ω ∂P) + ENNReal.ofReal K * ∫⁻ ω, h1 m ω ∂P := by
    intro m
    calc _ ≤ ∫⁻ p : Ω × Ω, (a m p.1 * h0 p.2 + ENNReal.ofReal K * h1 m p.2) ∂(P.prod P) :=
          lintegral_mono (hpt m)
      _ = _ := by
          have hAE : AEMeasurable (fun p : Ω × Ω => a m p.1 * h0 p.2) (P.prod P) :=
            (ha_meas m).comp_fst.mul hh0_meas.comp_snd
          rw [lintegral_add_left' hAE,
            lintegral_prod_mul (ha_meas m) hh0_meas,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod_snd' (hh1_meas m)]
  have hh0_fin : ∫⁻ ω, h0 ω ∂P ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_lt_top hJ2fin hG2fin).ne (lintegral_mul2_le hJ hG)
  have ha_lim : Tendsto (fun m => ∫⁻ ω, a m ω ∂P) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := P) (F := a)
      (f := fun _ => (0 : ℝ≥0∞)) (fun _ => 2 * ENNReal.ofReal K) ha_meas ?_ ?_ ?_
    · simpa using this
    · intro m
      refine Eventually.of_forall fun ω => ?_
      have h1 : ‖iteratedFDeriv ℝ 3 Φ (Gm m ω)‖ₑ ≤ ENNReal.ofReal K := by
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hK3 _)
      have h2 : ‖iteratedFDeriv ℝ 3 Φ (G ω)‖ₑ ≤ ENNReal.ofReal K := by
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hK3 _)
      calc a m ω ≤ ‖iteratedFDeriv ℝ 3 Φ (Gm m ω)‖ₑ + ‖iteratedFDeriv ℝ 3 Φ (G ω)‖ₑ :=
            enorm_sub_le
        _ ≤ ENNReal.ofReal K + ENNReal.ofReal K := add_le_add h1 h2
        _ = 2 * ENNReal.ofReal K := by rw [two_mul]
    · simp [ENNReal.mul_eq_top]
    · filter_upwards [hae] with ω hω
      exact tendsto_iff_enorm_sub_tendsto_zero.1 ((hc.tendsto (G ω)).comp hω)
  have hev : ∀ᶠ m in atTop, eLpNorm (Gm m) 2 P ≤ eLpNorm G 2 P + 1 := by
    filter_upwards [hG2.eventually (gt_mem_nhds zero_lt_one)] with m hm
    have : Gm m = (fun ω => Gm m ω - G ω) + G := by ext ω; simp
    calc eLpNorm (Gm m) 2 P = eLpNorm ((fun ω => Gm m ω - G ω) + G) 2 P := by rw [← this]
      _ ≤ eLpNorm (fun ω => Gm m ω - G ω) 2 P + eLpNorm G 2 P := eLpNorm_add_le (by norm_num)
      _ ≤ 1 + eLpNorm G 2 P := by gcongr
      _ = _ := add_comm _ _
  set S : ℝ≥0∞ := eLpNorm G 2 P + 1 with hS
  have hSfin : S ≠ ∞ := (ENNReal.add_lt_top.2 ⟨hG2fin, ENNReal.one_lt_top⟩).ne
  set x : ℕ → ℝ≥0∞ := fun m => eLpNorm (fun ω => Jm m ω - J ω) 2 P with hx
  set y : ℕ → ℝ≥0∞ := fun m => eLpNorm (fun ω => Gm m ω - G ω) 2 P with hy
  have hh1_le : ∀ᶠ m in atTop, ∫⁻ ω, h1 m ω ∂P ≤ x m * S + eLpNorm J 2 P * y m := by
    filter_upwards [hev] with m hm
    have hJ' : AEStronglyMeasurable (fun ω => Jm m ω - J ω) P := (hJm m).sub hJ
    have hG' : AEStronglyMeasurable (fun ω => Gm m ω - G ω) P := (hGm m).sub hG
    have m1 := lintegral_mul2_le hJ' (hGm m)
    have m2 := lintegral_mul2_le hJ hG'
    have e1 : AEMeasurable (fun ω => ‖Jm m ω - J ω‖ₑ * ‖Gm m ω‖ₑ) P :=
      hJ'.enorm.mul (hGm m).enorm
    calc ∫⁻ ω, h1 m ω ∂P
        = ∫⁻ ω, ‖Jm m ω - J ω‖ₑ * ‖Gm m ω‖ₑ ∂P + ∫⁻ ω, ‖J ω‖ₑ * ‖Gm m ω - G ω‖ₑ ∂P := by
          simp only [hh1_def]
          rw [lintegral_add_left' e1]
      _ ≤ x m * eLpNorm (Gm m) 2 P + eLpNorm J 2 P * y m := add_le_add m1 m2
      _ ≤ x m * S + eLpNorm J 2 P * y m := by gcongr
  have hlim : Tendsto (fun m => (∫⁻ ω, a m ω ∂P) * (∫⁻ ω, h0 ω ∂P) +
      ENNReal.ofReal K * (x m * S + eLpNorm J 2 P * y m)) atTop (𝓝 0) := by
    have t1 : Tendsto (fun m => (∫⁻ ω, a m ω ∂P) * (∫⁻ ω, h0 ω ∂P)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const ha_lim (Or.inr hh0_fin)
    have t2 : Tendsto (fun m => x m * S) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hJ2 (Or.inr hSfin)
    have t3 : Tendsto (fun m => eLpNorm J 2 P * y m) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hG2 (Or.inr hJ2fin.ne)
    have t4 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) (t2.add t3)
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using t1.add t4
  refine tendsto_zero_of_eventually_le hlim ?_
  filter_upwards [hh1_le] with m hm
  exact (hint m).trans (by gcongr)

end Abstract3

end Aux_s15

section Aux_s19b
open ProbabilityTheory

section Glue
set_option maxSynthPendingDepth 3
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

lemma first_finite (hξ : IsStdGaussianSeq P ξ) {Φ : B → ℝ} (hΦ : MemCb 3 Φ) (n n' : ℕ)
    (f : ℕ → B) (t : ℕ → TensorDual B 2) :
    ∫ ω, linP ξ n' t ω (iteratedFDeriv ℝ 2 Φ (linP ξ n f ω)) ∂P =
      ∫ p : Ω × Ω, linP ξ n' t p.2
        (lastSlot (iteratedFDeriv ℝ 3 Φ (linP ξ n f p.1)) (linP ξ n f p.2)) ∂(P.prod P) := by
  set N := n + n' with hN
  set w : Fin N → B := fun i => padv n f i with hw
  set s : Fin N → TensorDual B 2 := fun i => padv n' t i with hs
  have e1 : ∀ ω, linP ξ n f ω = Tmap w (Zvec ξ N ω) := fun ω => by
    rw [linP_pad ξ (Nat.le_add_right n n') f ω, linP_eq_Tmap]
  have e2 : ∀ ω, linP ξ n' t ω = Jfun s (Zvec ξ N ω) := fun ω => by
    rw [linP_pad ξ (Nat.le_add_left n' n) t ω, linP_eq_Tmap, Tmap_apply]
    rfl
  simp_rw [e1, e2]
  exact fin1_identity hξ hΦ w s

end Glue

end Aux_s19b

end Contr

set_option maxSynthPendingDepth 3 in
/-- Lemma 7.3 `M:F:lem:contractions`, display `F:eq:firstcontract` (M L7805-7819): for `G`
centered Gaussian in the Gaussian space of `ξ` and `J ∈ B ⊗̂π B` in its first chaos (an `L^q`
limit of linear polynomials `∑ ξ_i • T_i` with `T_i ∈ B ⊗̂π B`, M L7816-7818, for a finite `q`;
`q ≥ 2` suffices for the Hölder step of the proof), with the displayed moments finite
(`hint2`, `hint3`; M L7808-7809),
`E[⟨D²Φ(G), J⟩] = E[⟨D³Φ(G), E[J ⊗ G]⟩]`.

Representation: `B ⊗̂π B` is `projTensor B 2 ⊆ TensorDual B 2` (see the section comment), so
`⟨D²Φ(G), J⟩ = J (D²Φ(G))`. The right side `E_ω[⟨D³Φ(G ω), E_{ω'}[J ω' ⊗ G ω']⟩]` is written, as
for `thirdMomentPairing` and `gaussian_second_contraction`, by an independent copy `(J', G')` of
`(J, G)` on `Ω × Ω`: the bounded functional `⟨D³Φ(G ω), ·⟩` passes through the Bochner integral
`E[J ⊗ G]` (which exists in `B^{⊗̂π 3}` since `‖J ⊗ G‖_π ≤ ‖J‖ ‖G‖ ∈ L¹`, M L7829-7830), and
`⟨M, J ω' ⊗ G ω'⟩ = J ω' (lastSlot M (G ω'))`. Nothing is lost: both sides are the source's
expectations, and the integrability hypotheses are exactly "assume the moments in the following
expressions are finite". -/
theorem gaussian_first_contraction (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ)
    (G : Ω → B) (hG : IsCenteredGaussian (law P G)) (hGmeas : InFirstChaos P ξ 2 G)
    (J : Ω → projTensor B 2) (q : ℝ) (hq : 2 ≤ q) (hJ : InFirstChaos P ξ q J)
    (Φ : B → ℝ) (hΦ : MemCb 3 Φ)
    (hint2 : Integrable (fun ω => (J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (G ω))) P)
    (hint3 : Integrable (fun p : Ω × Ω =>
      (J p.2 : TensorDual B 2) (lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2))) (P.prod P)) :
    ∫ ω, (J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (G ω)) ∂P =
      ∫ p : Ω × Ω, (J p.2 : TensorDual B 2) (lastSlot (iteratedFDeriv ℝ 3 Φ (G p.1)) (G p.2))
        ∂(P.prod P) := by
  obtain ⟨hGas, n, c, hGlim⟩ := hGmeas
  obtain ⟨hJas, n', T, hJlim⟩ := hJ
  set J' : Ω → TensorDual B 2 := fun ω => (J ω : TensorDual B 2) with hJ'
  set t : ℕ → ℕ → TensorDual B 2 := fun m i => (T m i : TensorDual B 2) with ht
  have hJ'as : AEStronglyMeasurable J' P := continuous_subtype_val.comp_aestronglyMeasurable hJas
  have hGm : ∀ m, AEStronglyMeasurable (linP ξ (n m) (c m)) P := fun m => aesm_linP hξ _ _
  have hJm : ∀ m, AEStronglyMeasurable (linP ξ (n' m) (t m)) P := fun m => aesm_linP hξ _ _
  have hpt : ∀ m ω, ‖(∑ i ∈ Finset.range (n' m), ξ i ω • T m i) - J ω‖ₑ =
      ‖linP ξ (n' m) (t m) ω - J' ω‖ₑ := by
    intro m ω
    have : (((∑ i ∈ Finset.range (n' m), ξ i ω • T m i) - J ω : projTensor B 2) :
        TensorDual B 2) = linP ξ (n' m) (t m) ω - J' ω := by
      simp [linP, ht, hJ']
    rw [← this]
    rfl
  have hJlim' : Tendsto (fun m => ∫⁻ ω, ‖linP ξ (n' m) (t m) ω - J' ω‖ₑ ^ q ∂P) atTop (𝓝 0) := by
    simpa only [hpt] using hJlim
  have hG2 : Tendsto (fun m => eLpNorm (fun ω => linP ξ (n m) (c m) ω - G ω) 2 P) atTop (𝓝 0) := by
    have := eLpNorm_tendsto_of_lintegral (q := 2) (by norm_num) hGm hGas hGlim
    simpa using this
  have hJ2 : Tendsto (fun m => eLpNorm (fun ω => linP ξ (n' m) (t m) ω - J' ω) 2 P) atTop
      (𝓝 0) := by
    have := eLpNorm_tendsto_of_lintegral (q := q) (by linarith) hJm hJ'as hJlim'
    refine tendsto_zero_of_le this fun m => eLpNorm_le_eLpNorm_of_exponent_le ?_
    calc (2 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by norm_num
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (f := fun m => linP ξ (n m) (c m))
    (g := G) (p := 2) (by norm_num) hG2).exists_seq_tendsto_ae
  have hG2φ := hG2.comp hφ.tendsto_atTop
  have hJ2φ := hJ2.comp hφ.tendsto_atTop
  have hG2fin : eLpNorm G 2 P < ∞ :=
    eLpNorm_lt_top_of_approx (F := fun k => linP ξ (n (φ k)) (c (φ k))) (by norm_num)
      (fun k => eLpNorm_linP_lt_top hξ _ _) hG2φ
  have hJ2fin : eLpNorm J' 2 P < ∞ :=
    eLpNorm_lt_top_of_approx (F := fun k => linP ξ (n' (φ k)) (t (φ k))) (by norm_num)
      (fun k => eLpNorm_linP_lt_top hξ _ _) hJ2φ
  have hL := first_lhs_tendsto hΦ hGas hJ'as (fun k => hGm (φ k)) (fun k => hJm (φ k)) hG2φ hJ2φ
    hJ2fin hint2
  have hR := first_rhs_tendsto hΦ hGas hJ'as (fun k => hGm (φ k)) (fun k => hJm (φ k)) hae hG2φ
    hJ2φ hG2fin hJ2fin hint3
  have hL' : Tendsto (fun k => ∫ p : Ω × Ω, linP ξ (n' (φ k)) (t (φ k)) p.2
      (lastSlot (iteratedFDeriv ℝ 3 Φ (linP ξ (n (φ k)) (c (φ k)) p.1))
        (linP ξ (n (φ k)) (c (φ k)) p.2)) ∂(P.prod P)) atTop
      (𝓝 (∫ ω, J' ω (iteratedFDeriv ℝ 2 Φ (G ω)) ∂P)) :=
    hL.congr fun k => first_finite hξ hΦ _ _ _ _
  exact tendsto_nhds_unique hL' hR

end Contractions

end HRS
