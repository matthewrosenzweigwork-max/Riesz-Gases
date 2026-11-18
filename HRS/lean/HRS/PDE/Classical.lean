import HRS.PDE.ForwardEq
import HRS.PDE.KernelInputsD1
import HRS.PDE.TorusCalculus
import HRS.PDE.HsAnalysis

/-!
# Torus PDE layer: classical adjoint solutions as forward solutions (helpers)

Auxiliary results for `classical_toCoeff_isForwardSolution` and `classical_adjoint_unique`
(`HRS/PDE/WellPosed.lean`):

* Step A (`coeffOf_backwardGenerator`): for a `C²` function `u` and a `C¹` density `ρ`
  the Fourier coefficients of `backwardGenerator D ρ u` are `forwardGen D ρ (coeffOf u)`
  (given the kernel facts of `Convention.lean` and `V ∈ C¹`);
* Step B: differentiation of the coefficients of a classical solution in time;
* Step C: `H²` bounds and continuity of the coefficient path from the joint continuity of the
  derivatives up to order two.

Everything lives in the namespace `HRS.PDE.ClassicalAux`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ClassicalAux

variable {d : ℕ}

/-! ### Elementary facts on coefficients of continuous functions -/

lemma coeffOf_apply (g : Torus d → ℝ) (k : Lattice d) :
    coeffOf g k = ∫ x, Torus.mode (-k) x * (g x : ℂ) := funFourierCoeff_eq_int _ _

lemma integrable_mode_mul_ofReal {g : Torus d → ℝ} (hg : Integrable g) (k : Lattice d) :
    Integrable (fun x => Torus.mode (-k) x * (g x : ℂ)) :=
  (hg.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (Torus.continuous_mode (-k)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simp [Torus.norm_mode])

lemma integrable_of_continuous {g : Torus d → ℝ} (hg : Continuous g) : Integrable g :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma memLp_two_of_continuous {g : Torus d → ℝ} (hg : Continuous g) : MemLp g 2 volume :=
  hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma coeffOf_add {g h : Torus d → ℝ} (hg : Integrable g) (hh : Integrable h) :
    coeffOf (fun x => g x + h x) = fun k => coeffOf g k + coeffOf h k := by
  funext k
  simp only [coeffOf_apply, Complex.ofReal_add, mul_add]
  exact integral_add (integrable_mode_mul_ofReal hg k) (integrable_mode_mul_ofReal hh k)

lemma coeffOf_sub {g h : Torus d → ℝ} (hg : Integrable g) (hh : Integrable h) :
    coeffOf (fun x => g x - h x) = fun k => coeffOf g k - coeffOf h k := by
  funext k
  simp only [coeffOf_apply, Complex.ofReal_sub, mul_sub]
  exact integral_sub (integrable_mode_mul_ofReal hg k) (integrable_mode_mul_ofReal hh k)

lemma coeffOf_const_mul (c : ℝ) (g : Torus d → ℝ) :
    coeffOf (fun x => c * g x) = fun k => (c : ℂ) * coeffOf g k := by
  funext k
  simp only [coeffOf_apply, Complex.ofReal_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

lemma coeffOf_sum {ι : Type*} (s : Finset ι) (g : ι → Torus d → ℝ)
    (hg : ∀ i ∈ s, Integrable (g i)) :
    coeffOf (fun x => ∑ i ∈ s, g i x) = fun k => ∑ i ∈ s, coeffOf (g i) k := by
  funext k
  simp only [coeffOf_apply, Complex.ofReal_sum, Finset.mul_sum]
  exact integral_finsetSum _ fun i hi => integrable_mode_mul_ofReal (hg i hi) k

/-! ### Smoothness bookkeeping -/

lemma isCk_sum {n : WithTop ℕ∞} {ι : Type*} (s : Finset ι) {g : ι → Torus d → ℝ}
    (hg : ∀ i ∈ s, Torus.IsCk n (g i)) : Torus.IsCk n (fun x => ∑ i ∈ s, g i x) := by
  unfold Torus.IsCk at *
  have : Torus.lift (fun x => ∑ i ∈ s, g i x) = fun y => ∑ i ∈ s, Torus.lift (g i) y := rfl
  rw [this]
  exact ContDiff.sum hg

lemma isCk_const_mul {n : WithTop ℕ∞} (c : ℝ) {g : Torus d → ℝ} (hg : Torus.IsCk n g) :
    Torus.IsCk n (fun x => c * g x) := by
  unfold Torus.IsCk at *
  exact contDiff_const.mul hg

lemma isCk_mul {n : WithTop ℕ∞} {g h : Torus d → ℝ} (hg : Torus.IsCk n g) (hh : Torus.IsCk n h) :
    Torus.IsCk n (fun x => g x * h x) := by
  unfold Torus.IsCk at *
  exact hg.mul hh

lemma isCk_of_le {n m : WithTop ℕ∞} (h : m ≤ n) {g : Torus d → ℝ} (hg : Torus.IsCk n g) :
    Torus.IsCk m g := ContDiff.of_le hg h

private lemma isOpenQuotientMap_mk_aux : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 := h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h2

lemma continuous_of_lift_aux {E : Type*} [TopologicalSpace E] {f : Torus d → E}
    (h : Continuous (Torus.lift f)) : Continuous f :=
  isOpenQuotientMap_mk_aux.isQuotientMap.continuous_iff.2 h

lemma continuous_of_isCk {g : Torus d → ℝ} (hg : Torus.IsCk 1 g) : Continuous g :=
  continuous_of_lift_aux hg.continuous

/-! ### Components -/

lemma grad_apply (φ : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    Torus.grad φ x j = Torus.partialDeriv j φ x := by
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d)
    (x := EuclideanSpace.single j (1 : ℝ)) (y := fderiv ℝ (Torus.lift φ) (Torus.rep x))
  simp only [Torus.grad, Torus.partialDeriv, gradient]
  rw [← this, EuclideanSpace.inner_single_right]
  simp

lemma matVec_apply (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) (j : Fin d) :
    Torus.matVec M v j = ∑ i, M j i * v i := by
  simp [Torus.matVec, Matrix.mulVec, dotProduct]

lemma inner_euc (a b : Euc d) : inner ℝ a b = ∑ i, a i * b i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

lemma continuous_laplacian {u : Torus d → ℝ} (hu : Torus.IsCk 2 u) :
    Continuous (Torus.laplacian u) := by
  have : Torus.laplacian u = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j u) x :=
    funext (laplacian_eq_sum u hu)
  rw [this]
  exact continuous_finsetSum _ fun j _ =>
    continuous_partialDeriv j _ (isCk_one_partialDeriv j u hu)

/-! ### Step A: the coefficients of the backward generator -/

/-- The kernel facts of `Convention.lean` for the cancellation convention at exponent `s`. -/
structure ConvKernelFacts (d : ℕ) (s : ℝ) : Prop where
  cont : ∀ h : Torus d → ℝ, Torus.IsCk 1 h → Continuous (convGradConv (periodicRieszGrad d s) h)
  coeff : ∀ h : Torus d → ℝ, Torus.IsCk 1 h → ∀ i : Fin d,
    coeffOf (fun x => convGradConv (periodicRieszGrad d s) h x i) =
      gradRieszCoeff d s i (coeffOf h)

lemma convKernelFacts_of_two_le (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ConvKernelFacts d s :=
  ⟨fun h hh => convGradConv_continuous hd hs0 hsd h hh,
    fun h hh i => convGradConv_coeff hd hs0 hsd h hh i⟩

/-- The `j`-th component of the drift `b = M∇g*ρ - ∇V`. -/
def bfun (D : DynData d) (ρ : Torus d → ℝ) (j : Fin d) : Torus d → ℝ := fun x =>
  ∑ i, D.M j i * convGradConv (periodicRieszGrad d D.s) ρ x i - Torus.partialDeriv j D.V x

/-- The `j`-th density-weighted component `ρ (Mᵀ∇u)_j` of the nonlocal term. -/
def wfun (D : DynData d) (ρ u : Torus d → ℝ) (j : Fin d) : Torus d → ℝ := fun y =>
  ∑ l, D.M l j * (ρ y * Torus.partialDeriv l u y)

lemma continuous_bfun {D : DynData d} (hK : ConvKernelFacts d D.s) (hV : Torus.IsCk 1 D.V)
    {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (j : Fin d) : Continuous (bfun D ρ j) := by
  have h1 : Continuous (convGradConv (periodicRieszGrad d D.s) ρ) := hK.cont ρ hρ
  unfold bfun
  refine Continuous.sub (continuous_finsetSum _ fun i _ => ?_) (continuous_partialDeriv j _ hV)
  exact continuous_const.mul ((continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp h1))

lemma isCk_wfun (D : DynData d) {ρ u : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (hu : Torus.IsCk 2 u)
    (j : Fin d) : Torus.IsCk 1 (wfun D ρ u j) :=
  isCk_sum _ fun l _ => isCk_const_mul _ (isCk_mul hρ (isCk_one_partialDeriv l u hu))

lemma coeffOf_bfun {D : DynData d} (hK : ConvKernelFacts d D.s) (hV : Torus.IsCk 1 D.V)
    {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) (j : Fin d) :
    coeffOf (bfun D ρ j) = driftCoeff D ρ j := by
  have hcomp : ∀ i, Continuous (fun x => convGradConv (periodicRieszGrad d D.s) ρ x i) := fun i =>
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp (hK.cont ρ hρ))
  have e1 : coeffOf (fun x => ∑ i, D.M j i * convGradConv (periodicRieszGrad d D.s) ρ x i) =
      fun k => ∑ i, ((D.M j i : ℝ) : ℂ) * gradRieszCoeff d D.s i (coeffOf ρ) k := by
    refine (coeffOf_sum Finset.univ
      (fun i x => D.M j i * convGradConv (periodicRieszGrad d D.s) ρ x i)
      fun i _ => integrable_of_continuous (continuous_const.mul (hcomp i))).trans ?_
    funext k
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeffOf_const_mul, hK.coeff ρ hρ i]
  have e2 : coeffOf (Torus.partialDeriv j D.V) = derivCoeff j (coeffOf D.V) :=
    coeffOf_partialDeriv j D.V hV
  have hc1 : Continuous (fun x => ∑ i, D.M j i * convGradConv (periodicRieszGrad d D.s) ρ x i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcomp i)
  have e3 := coeffOf_sub (g := fun x => ∑ i, D.M j i * convGradConv (periodicRieszGrad d D.s) ρ x i)
    (h := Torus.partialDeriv j D.V) (integrable_of_continuous hc1)
    (integrable_of_continuous (continuous_partialDeriv j _ hV))
  funext k
  exact (congrFun e3 k).trans (by rw [congrFun e1 k, congrFun e2 k]; rfl)

lemma backwardGenerator_eq_fun (D : DynData d) (ρ u : Torus d → ℝ) :
    backwardGenerator D ρ u = fun x => D.invβ * Torus.laplacian u x +
      ∑ j, bfun D ρ j x * Torus.partialDeriv j u x -
        ∑ j, convGradConv (periodicRieszGrad d D.s) (wfun D ρ u j) x j := by
  funext x
  have hdrift : ∀ j, (meanFieldDrift D ρ x) j = bfun D ρ j x := by
    intro j
    simp only [meanFieldDrift, bfun, PiLp.sub_apply, matVec_apply, grad_apply]
  have hw : ∀ j, (fun y => ρ y * (Torus.matVec D.M.transpose (Torus.grad u y)) j) =
      wfun D ρ u j := by
    intro j
    funext y
    simp only [wfun, matVec_apply, grad_apply, Matrix.transpose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  unfold backwardGenerator
  simp only [hw, inner_euc, hdrift, grad_apply]

/-- **Step A.**  The Fourier coefficients of the backward generator applied to a `C²` function are
the forward generator applied to its coefficients. -/
theorem coeffOf_backwardGenerator (D : DynData d) (hK : ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 1 ρ) {u : Torus d → ℝ}
    (hu : Torus.IsCk 2 u) :
    coeffOf (backwardGenerator D ρ u) = forwardGen D ρ (coeffOf u) := by
  have hdu : ∀ j, Continuous (Torus.partialDeriv j u) := fun j =>
    continuous_partialDeriv j u (isCk_of_le (by norm_num) hu)
  have hb := fun j => continuous_bfun hK hV hρ j
  have hlap := continuous_laplacian hu
  have hnl : ∀ j, Continuous (fun x => convGradConv (periodicRieszGrad d D.s) (wfun D ρ u j) x j) :=
    fun j => (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp
      (hK.cont _ (isCk_wfun D hρ hu j)))
  have hA : Continuous (fun x => D.invβ * Torus.laplacian u x) := continuous_const.mul hlap
  have hB : Continuous (fun x => ∑ j, bfun D ρ j x * Torus.partialDeriv j u x) :=
    continuous_finsetSum _ fun j _ => (hb j).mul (hdu j)
  have hC : Continuous (fun x => ∑ j, convGradConv (periodicRieszGrad d D.s) (wfun D ρ u j) x j) :=
    continuous_finsetSum _ fun j _ => hnl j
  have hL : coeffOf (fun x => D.invβ * Torus.laplacian u x) =
      fun k => (D.invβ : ℂ) * laplaceCoeff (coeffOf u) k := by
    rw [coeffOf_const_mul, coeffOf_laplacian u hu]
  have hT : coeffOf (fun x => ∑ j, bfun D ρ j x * Torus.partialDeriv j u x) =
      transportCoeff D ρ (coeffOf u) := by
    refine (coeffOf_sum Finset.univ (fun j x => bfun D ρ j x * Torus.partialDeriv j u x)
      fun j _ => integrable_of_continuous ((hb j).mul (hdu j))).trans ?_
    funext k
    simp only [transportCoeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeffOf_mul _ _ (memLp_two_of_continuous (hb j)) (memLp_two_of_continuous (hdu j)),
      coeffOf_bfun hK hV hρ j, coeffOf_partialDeriv j u (isCk_of_le (by norm_num) hu)]
  have hW : ∀ j, coeffOf (wfun D ρ u j) = fun k => ∑ l,
      (D.M l j : ℂ) * mulCoeff (coeffOf ρ) (derivCoeff l (coeffOf u)) k := by
    intro j
    refine (coeffOf_sum Finset.univ (fun l y => D.M l j * (ρ y * Torus.partialDeriv l u y))
      fun l _ => integrable_of_continuous (continuous_const.mul ?_)).trans ?_
    · exact (continuous_of_isCk hρ).mul (hdu l)
    funext k
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [coeffOf_const_mul, coeffOf_mul _ _
      (memLp_two_of_continuous (continuous_of_isCk hρ))
      (memLp_two_of_continuous (hdu l)), coeffOf_partialDeriv l u (isCk_of_le (by norm_num) hu)]
  have hN : coeffOf (fun x => ∑ j, convGradConv (periodicRieszGrad d D.s) (wfun D ρ u j) x j) =
      nonlocalCoeff D ρ (coeffOf u) := by
    refine (coeffOf_sum Finset.univ
      (fun j x => convGradConv (periodicRieszGrad d D.s) (wfun D ρ u j) x j)
      fun j _ => integrable_of_continuous (hnl j)).trans ?_
    funext k
    simp only [nonlocalCoeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hK.coeff _ (isCk_wfun D hρ hu i) i, hW i]
    simp only [gradRieszCoeff, derivCoeff, rieszMult, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [backwardGenerator_eq_fun]
  refine (coeffOf_sub (g := fun x => D.invβ * Torus.laplacian u x +
      ∑ j, bfun D ρ j x * Torus.partialDeriv j u x) (integrable_of_continuous (hA.add hB))
    (integrable_of_continuous hC)).trans ?_
  funext k
  have hAB := congrFun (coeffOf_add (integrable_of_continuous hA) (integrable_of_continuous hB)) k
  simp only [forwardGen]
  rw [hAB, congrFun hL k, congrFun hT k, congrFun hN k]


/-! ### Step C: the `H²` structure of the coefficient path -/

lemma laplacian_mk (u : Torus d → ℝ) (hu : Torus.IsCk 2 u) (y : Euc d) :
    Torus.laplacian u (Torus.mk y) = ∑ j : Fin d, iteratedFDeriv ℝ 2 (Torus.lift u) y
      ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)] := by
  have h1 : Torus.IsCk 1 u := hu.of_le (by norm_num)
  rw [laplacian_eq_sum u hu]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ (Torus.lift u)) y :=
    ((hu.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ (Torus.lift u)))).differentiable
      one_ne_zero _
  rw [partialDeriv_mk j (Torus.partialDeriv j u) (isCk_one_partialDeriv j u hu) y,
    lift_partialDeriv j u h1, fderiv_clm_apply hd (differentiableAt_const _),
    iteratedFDeriv_two_apply]
  simp

lemma continuous_prod_of_lift {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    (G : X → Torus d → E) (hG : Continuous fun p : X × Euc d => G p.1 (Torus.mk p.2)) :
    Continuous fun p : X × Torus d => G p.1 p.2 :=
  ((IsOpenQuotientMap.id (X := X)).prodMap isOpenQuotientMap_mk_aux).isQuotientMap.continuous_iff.2 hG

lemma continuous_iteratedFDeriv_eval {X : Type*} [TopologicalSpace X] {G : X → Euc d → ℝ}
    (j : ℕ) (h : Continuous fun p : X × Euc d => iteratedFDeriv ℝ j (G p.1) p.2)
    (m : Fin j → Euc d) : Continuous fun p : X × Euc d => iteratedFDeriv ℝ j (G p.1) p.2 m :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ m).continuous.comp h

/-- `u - Δu` along the path `r ↦ f r`. -/
def Wfun (f : ℝ → Torus d → ℝ) (r : ℝ) (x : Torus d) : ℝ := f r x - Torus.laplacian (f r) x

/-- Parseval for continuous real functions: `∑_k |ĥ(k)|² = ∫ h²`. -/
lemma hasSum_sq_coeffOf {h : Torus d → ℝ} (hh : Continuous h) :
    HasSum (fun k => ‖coeffOf h k‖ ^ 2) (∫ x, h x ^ 2) := by
  have hm : MemLp (fun x => (h x : ℂ)) 2 volume := (memLp_two_of_continuous hh).ofReal
  have hP := hasSum_parseval (fun x => (h x : ℂ)) (fun x => (h x : ℂ)) hm hm
  rw [← Complex.hasSum_ofReal]
  have e1 : ∀ k, (conj (Torus.funFourierCoeff (fun x => (h x : ℂ)) k) *
      Torus.funFourierCoeff (fun x => (h x : ℂ)) k) = ((‖coeffOf h k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have : Torus.funFourierCoeff (fun x => (h x : ℂ)) k = coeffOf h k := rfl
    rw [this, Complex.conj_mul']
    push_cast
    rfl
  have e2 : (∫ t, conj ((h t : ℂ)) * (h t : ℂ)) = ((∫ x, h x ^ 2 : ℝ) : ℂ) := by
    have h1 : (∫ t, conj ((h t : ℂ)) * (h t : ℂ)) = ∫ t, (((h t ^ 2 : ℝ)) : ℂ) := by
      congr 1
      funext x
      simp [Complex.conj_ofReal, sq]
    rw [h1]
    exact integral_ofReal (𝕜 := ℂ)
  simpa only [e1, e2] using hP

lemma sobWeight_two (k : Lattice d) :
    sobWeight (2 : ℝ) k = (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 := by
  unfold sobWeight
  exact Real.rpow_two _

/-- If `W` is continuous with `Ŵ(k) = (1+4π²|k|²) c(k)` then `c ∈ H²` with `‖c‖²_{H²} = ∫ W²`. -/
lemma hs2_of_W {c : Coeff d} {W : Torus d → ℝ} (hW : Continuous W)
    (hc : ∀ k, coeffOf W k = ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) * c k) :
    MemHs 2 c ∧ hsNormSq 2 c = ∫ x, W x ^ 2 := by
  have hP := hasSum_sq_coeffOf hW
  have e : ∀ k, sobWeight (2 : ℝ) k * ‖c k‖ ^ 2 = ‖coeffOf W k‖ ^ 2 := by
    intro k
    rw [hc k, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2),
      sobWeight_two]
    ring
  refine ⟨?_, ?_⟩
  · exact hP.summable.congr fun k => (e k).symm
  · unfold hsNormSq
    simp_rw [e]
    exact hP.tsum_eq

section Classical

variable {D : DynData d} {μ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ} {f : ℝ → Torus d → ℝ}

lemma continuous_Wfun (hf : IsClassicalAdjointSolution D μ t φ f) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => Wfun f p.1 p.2 := by
  refine continuous_prod_of_lift (X := Set.Icc (0 : ℝ) t) (fun r (x : Torus d) => Wfun f r x) ?_
  have h0 := continuous_iteratedFDeriv_eval (G := fun r : Set.Icc (0 : ℝ) t => Torus.lift (f r))
    0 (hf.cont_c2 0 (by norm_num)) ![]
  have h2 := fun j : Fin d => continuous_iteratedFDeriv_eval
    (G := fun r : Set.Icc (0 : ℝ) t => Torus.lift (f r)) 2 (hf.cont_c2 2 le_rfl)
    ![EuclideanSpace.single j (1 : ℝ), EuclideanSpace.single j (1 : ℝ)]
  simp only [iteratedFDeriv_zero_apply] at h0
  have := h0.sub (continuous_finsetSum Finset.univ fun j _ => h2 j)
  refine this.congr fun p => ?_
  simp only [Wfun]
  rw [laplacian_mk _ (hf.c2 p.1 p.1.2)]
  rfl

lemma continuous_f_apply (hf : IsClassicalAdjointSolution D μ t φ f) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) : Continuous (f r) :=
  continuous_of_isCk (isCk_of_le (by norm_num) (hf.c2 r hr))

lemma continuous_Wfun_apply (hf : IsClassicalAdjointSolution D μ t φ f) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) : Continuous (Wfun f r) :=
  (continuous_f_apply hf hr).sub (continuous_laplacian (hf.c2 r hr))

lemma coeffOf_Wfun (hf : IsClassicalAdjointSolution D μ t φ f) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) (k : Lattice d) :
    coeffOf (Wfun f r) k =
      ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) * coeffOf (f r) k := by
  have h := congrFun (coeffOf_sub (integrable_of_continuous (continuous_f_apply hf hr))
    (integrable_of_continuous (continuous_laplacian (hf.c2 r hr)))) k
  have e : coeffOf (Wfun f r) = coeffOf (fun x => f r x - Torus.laplacian (f r) x) := rfl
  rw [e, h, coeffOf_laplacian _ (hf.c2 r hr)]
  simp only [laplaceCoeff]
  push_cast
  ring

lemma hs2_f (hf : IsClassicalAdjointSolution D μ t φ f) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    MemHs 2 (coeffOf (f r)) ∧ hsNormSq 2 (coeffOf (f r)) = ∫ x, Wfun f r x ^ 2 :=
  hs2_of_W (continuous_Wfun_apply hf hr) (coeffOf_Wfun hf hr)

lemma integral_sq_le {g : Torus d → ℝ} {ε : ℝ} (h : ∀ x, |g x| ≤ ε) : ∫ x, g x ^ 2 ≤ ε ^ 2 := by
  have h1 : ‖∫ x, g x ^ 2‖ ≤ ε ^ 2 * ((volume : Measure (Torus d)) Set.univ).toReal :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs (g x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (h x) 2)
  simp only [measure_univ, ENNReal.toReal_one, mul_one] at h1
  exact (le_abs_self _).trans h1

lemma hsNormSq_le_of_W {c : Coeff d} {W : Torus d → ℝ} (hW : Continuous W)
    (hc : ∀ k, coeffOf W k = ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) * c k)
    {ε : ℝ} (h : ∀ x, |W x| ≤ ε) : MemHs 2 c ∧ hsNormSq 2 c ≤ ε ^ 2 := by
  obtain ⟨h1, h2⟩ := hs2_of_W hW hc
  exact ⟨h1, h2 ▸ integral_sq_le h⟩

lemma norm_coord_le_hsNorm {c : Coeff d} (hc : MemHs 2 c) (k : Lattice d) :
    ‖c k‖ ≤ hsNorm 2 c := by
  have h1 : sobWeight (2 : ℝ) k * ‖c k‖ ^ 2 ≤ hsNormSq 2 c := sobWeight_mul_sq_le_hsNormSq hc k
  have h2 : (1 : ℝ) ≤ sobWeight (2 : ℝ) k := by
    rw [sobWeight_two]
    have := one_le_sobBase (d := d) k
    nlinarith
  have h3 : ‖c k‖ ^ 2 ≤ hsNormSq 2 c := by nlinarith [sq_nonneg ‖c k‖]
  exact Real.le_sqrt_of_sq_le h3

lemma exists_bound_Wfun (hf : IsClassicalAdjointSolution D μ t φ f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, |Wfun f r x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_Wfun hf).continuousOn
  refine ⟨|B|, abs_nonneg _, fun r hr x => ?_⟩
  have := hB (⟨r, hr⟩, x) (Set.mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_abs_self _)

/-- Uniform convergence of `r ↦ u_r - Δu_r` on the torus (from joint continuity on the compact
set `[0,t] × 𝕋^d`). -/
lemma eventually_uniform_Wfun (hf : IsClassicalAdjointSolution D μ t φ f) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Icc (0 : ℝ) t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[Set.Icc (0 : ℝ) t] r₀, r ∈ Set.Icc (0 : ℝ) t ∧
      ∀ x, |Wfun f r x - Wfun f r₀ x| < ε := by
  have h := Continuous.tendstoUniformly (fun (r : Set.Icc (0 : ℝ) t) (x : Torus d) => Wfun f r x)
    (continuous_Wfun hf) (⟨r₀, hr₀⟩ : Set.Icc (0 : ℝ) t)
  have h2 := Metric.tendstoUniformly_iff.1 h ε hε
  rw [nhdsWithin_eq_map_subtype_coe hr₀, Filter.eventually_map]
  filter_upwards [h2] with r hr
  refine ⟨r.2, fun x => ?_⟩
  have := hr x
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this

lemma tendsto_hsNorm_diff (hf : IsClassicalAdjointSolution D μ t φ f) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Set.Icc (0 : ℝ) t) :
    Tendsto (fun r => hsNorm 2 (coeffOf (f r) - coeffOf (f r₀))) (𝓝[Set.Icc (0 : ℝ) t] r₀)
      (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_uniform_Wfun hf hr₀ (half_pos hε)] with r ⟨hr, hW⟩
  have hc : ∀ k, coeffOf (fun x => Wfun f r x - Wfun f r₀ x) k =
      ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) *
        (coeffOf (f r) - coeffOf (f r₀)) k := by
    intro k
    rw [congrFun (coeffOf_sub (integrable_of_continuous (continuous_Wfun_apply hf hr))
      (integrable_of_continuous (continuous_Wfun_apply hf hr₀))) k, coeffOf_Wfun hf hr,
      coeffOf_Wfun hf hr₀]
    simp only [Pi.sub_apply]
    ring
  have key := hsNormSq_le_of_W ((continuous_Wfun_apply hf hr).sub (continuous_Wfun_apply hf hr₀))
    hc (fun x => (hW x).le)
  have hnn : 0 ≤ hsNorm 2 (coeffOf (f r) - coeffOf (f r₀)) := Real.sqrt_nonneg _
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn]
  have : hsNorm 2 (coeffOf (f r) - coeffOf (f r₀)) ≤ ε / 2 :=
    Real.sqrt_le_iff.2 ⟨(half_pos hε).le, by simpa using key.2⟩
  linarith

lemma memHs_diff (hf : IsClassicalAdjointSolution D μ t φ f) {r r₀ : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) (hr₀ : r₀ ∈ Set.Icc (0 : ℝ) t) :
    MemHs 2 (coeffOf (f r) - coeffOf (f r₀)) := by
  have hc : ∀ k, coeffOf (fun x => Wfun f r x - Wfun f r₀ x) k =
      ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) *
        (coeffOf (f r) - coeffOf (f r₀)) k := by
    intro k
    rw [congrFun (coeffOf_sub (integrable_of_continuous (continuous_Wfun_apply hf hr))
      (integrable_of_continuous (continuous_Wfun_apply hf hr₀))) k, coeffOf_Wfun hf hr,
      coeffOf_Wfun hf hr₀]
    simp only [Pi.sub_apply]
    ring
  exact (hs2_of_W ((continuous_Wfun_apply hf hr).sub (continuous_Wfun_apply hf hr₀)) hc).1

lemma continuousOn_coeff (hf : IsClassicalAdjointSolution D μ t φ f) (k : Lattice d) :
    ContinuousOn (fun r => coeffOf (f r) k) (Set.Icc (0 : ℝ) t) := by
  intro r₀ hr₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ (tendsto_hsNorm_diff hf hr₀)
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [norm_norm]
  exact norm_coord_le_hsNorm (memHs_diff hf hr hr₀) k

lemma bounded_hsNormSq (hf : IsClassicalAdjointSolution D μ t φ f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, hsNormSq 2 (coeffOf (f r)) ≤ B ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_Wfun hf
  refine ⟨B, hB0, fun r hr => ?_⟩
  exact (hsNormSq_le_of_W (continuous_Wfun_apply hf hr) (coeffOf_Wfun hf hr) (hB r hr)).2

/-! ### Step B: time differentiation of the coefficients -/

lemma exists_bound_bg (hf : IsClassicalAdjointSolution D μ t φ f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, |backwardGenerator D (μ r) (f r) x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.cont_time_deriv.continuousOn
  refine ⟨|B|, abs_nonneg _, fun r hr x => ?_⟩
  have := hB (⟨r, hr⟩, x) (Set.mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_abs_self _)

lemma continuous_bg_apply (hf : IsClassicalAdjointSolution D μ t φ f) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) : Continuous (backwardGenerator D (μ r) (f r)) :=
  by
  have h2 : Continuous fun x : Torus d => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) t), x) :=
    Continuous.prodMk_right _
  have h3 := hf.cont_time_deriv.comp h2
  simp only [Function.comp_def] at h3
  exact h3

lemma continuousOn_coeff_bg (hf : IsClassicalAdjointSolution D μ t φ f) (k : Lattice d) :
    ContinuousOn (fun r => coeffOf (backwardGenerator D (μ r) (f r)) k) (Set.Icc (0 : ℝ) t) := by
  have h : Continuous fun r : Set.Icc (0 : ℝ) t =>
      ∫ x in (Set.univ : Set (Torus d)), Torus.mode (-k) x * ((backwardGenerator D (μ r) (f r) x : ℝ) : ℂ) := by
    refine continuous_parametric_integral_of_continuous (X := Set.Icc (0 : ℝ) t)
      (f := fun r x => Torus.mode (-k) x * ((backwardGenerator D (μ r) (f r) x : ℝ) : ℂ)) ?_
      isCompact_univ
    exact ((Torus.continuous_mode (-k)).comp continuous_snd).mul
      (Complex.continuous_ofReal.comp hf.cont_time_deriv)
  rw [continuousOn_iff_continuous_domRestrict]
  simpa only [setIntegral_univ] using h.congr fun r => by
    simp only [Set.domRestrict_apply, coeffOf_apply, setIntegral_univ]

lemma hasDerivAt_coeff (hf : IsClassicalAdjointSolution D μ t φ f) (k : Lattice d) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) t) :
    HasDerivAt (fun r' => coeffOf (f r') k) (-(coeffOf (backwardGenerator D (μ r) (f r)) k)) r := by
  have hr' : r ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hr
  obtain ⟨B, hB0, hB⟩ := exists_bound_bg hf
  have hs : Set.Ioo (0 : ℝ) t ∈ 𝓝 r := Ioo_mem_nhds hr.1 hr.2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Torus d))) (F := fun r' x => Torus.mode (-k) x * (f r' x : ℂ))
    (F' := fun r' x => Torus.mode (-k) x * ((-(backwardGenerator D (μ r') (f r') x) : ℝ) : ℂ))
    (x₀ := r) (bound := fun _ => B) hs ?_ ?_ ?_ ?_ (integrable_const B) ?_
  · have e1 : (fun r' => ∫ x, Torus.mode (-k) x * (f r' x : ℂ)) = fun r' => coeffOf (f r') k := by
      funext r'; rw [coeffOf_apply]
    have e2 : ∫ x, Torus.mode (-k) x * ((-(backwardGenerator D (μ r) (f r) x) : ℝ) : ℂ) =
        -(coeffOf (backwardGenerator D (μ r) (f r)) k) := by
      rw [coeffOf_apply, ← integral_neg]
      congr 1
      funext x
      push_cast
      ring
    rw [e1, e2] at key
    exact key.2
  · have : Set.Icc (0 : ℝ) t ∈ 𝓝 r := Icc_mem_nhds hr.1 hr.2
    filter_upwards [this] with r' hr'
    exact ((Torus.continuous_mode (-k)).mul
      (Complex.continuous_ofReal.comp (continuous_f_apply hf hr'))).aestronglyMeasurable
  · exact integrable_mode_mul_ofReal (integrable_of_continuous (continuous_f_apply hf hr')) k
  · exact ((Torus.continuous_mode (-k)).mul (Complex.continuous_ofReal.comp
      (continuous_bg_apply hf hr').neg)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x r' hr'' => ?_
    have hmem := Set.Ioo_subset_Icc_self hr''
    rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    exact hB r' hmem x
  · refine Filter.Eventually.of_forall fun x r' hr'' => ?_
    exact ((hf.time_deriv x r' hr'').ofReal_comp).const_mul (Torus.mode (-k) x)

lemma mem_Icc_sub (t : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t) : t - τ ∈ Set.Icc (0 : ℝ) t :=
  ⟨by linarith [hτ.2], by linarith [hτ.1]⟩

lemma continuousInHs_two (hf : IsClassicalAdjointSolution D μ t φ f) :
    ContinuousInHs 2 (fun τ => coeffOf (f (t - τ))) t := by
  refine ⟨fun τ hτ => (hs2_f hf (mem_Icc_sub t hτ)).1, fun τ₀ hτ₀ => ?_⟩
  have hmap : Tendsto (fun τ : ℝ => t - τ) (𝓝[Set.Icc (0 : ℝ) t] τ₀)
      (𝓝[Set.Icc (0 : ℝ) t] (t - τ₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun τ hτ =>
      mem_Icc_sub t hτ⟩
    exact ((continuous_const.sub continuous_id).tendsto τ₀).mono_left nhdsWithin_le_nhds
  exact (tendsto_hsNorm_diff hf (mem_Icc_sub t hτ₀)).comp hmap

/-- **Classical solutions are forward solutions** (given the kernel facts, `V ∈ C¹`, `μ ∈ C¹`). -/
theorem classicalToCoeff_aux (D : DynData d) (hK : ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) (μ : ℝ → Torus d → ℝ) (t : ℝ)
    (hμ : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 1 (μ r))
    (φ : Torus d → ℝ) (f : ℝ → Torus d → ℝ) (hf : IsClassicalAdjointSolution D μ t φ f) :
    IsForwardSolution D μ t (coeffOf φ) (fun τ => coeffOf (f (t - τ))) ∧
      ContinuousInHs 2 (fun τ => coeffOf (f (t - τ))) t := by
  have hgen : ∀ r ∈ Set.Icc (0 : ℝ) t,
      coeffOf (backwardGenerator D (μ r) (f r)) = forwardGen D (μ r) (coeffOf (f r)) :=
    fun r hr => coeffOf_backwardGenerator D hK hV (hμ r hr) (hf.c2 r hr)
  have hint : ∀ k, IntegrableOn
      (fun σ => forwardGen D (μ (t - σ)) (coeffOf (f (t - σ))) k) (Set.Icc 0 t) := by
    intro k
    have hc : ContinuousOn (fun σ => coeffOf (backwardGenerator D (μ (t - σ)) (f (t - σ))) k)
        (Set.Icc (0 : ℝ) t) :=
      (continuousOn_coeff_bg hf k).comp (continuous_const.sub continuous_id).continuousOn
        fun σ hσ => mem_Icc_sub t hσ
    refine hc.integrableOn_Icc.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    simp only
    rw [hgen _ (mem_Icc_sub t hσ)]
  refine ⟨⟨fun τ hτ => (hs2_f hf (mem_Icc_sub t hτ)).1.mono (by norm_num), hint, ?_⟩,
    continuousInHs_two hf⟩
  intro k τ hτ
  have hderiv : ∀ σ ∈ Set.Ioo (0 : ℝ) τ,
      HasDerivAt (fun σ => coeffOf (f (t - σ)) k)
        (forwardGen D (μ (t - σ)) (coeffOf (f (t - σ))) k) σ := by
    intro σ hσ
    have hr : t - σ ∈ Set.Ioo (0 : ℝ) t := ⟨by linarith [hσ.2, hτ.2], by linarith [hσ.1]⟩
    have h1 := hasDerivAt_coeff hf k hr
    have h2 : HasDerivAt (fun σ : ℝ => t - σ) (-1) σ := (hasDerivAt_id σ).const_sub t
    have h3 := h1.scomp σ h2
    refine h3.congr_deriv ?_
    rw [← hgen _ (Set.Ioo_subset_Icc_self hr)]
    simp
  have hcont : ContinuousOn (fun σ => coeffOf (f (t - σ)) k) (Set.Icc (0 : ℝ) τ) :=
    ((continuousOn_coeff hf k).comp (continuous_const.sub continuous_id).continuousOn
      fun σ hσ => mem_Icc_sub t ⟨hσ.1, hσ.2.trans hτ.2⟩)
  have hii : IntervalIntegrable (fun σ => forwardGen D (μ (t - σ)) (coeffOf (f (t - σ))) k)
      volume 0 τ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1).2
      ((hint k).mono_set (Set.Icc_subset_Icc_right hτ.2))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1 hcont hderiv hii
  rw [hftc]
  have h0 : coeffOf (f (t - 0)) k = coeffOf φ k := by rw [sub_zero, hf.terminal]
  simp only [h0]
  ring

lemma weakContinuousInHs_two (hf : IsClassicalAdjointSolution D μ t φ f) :
    WeakContinuousInHs 2 (fun τ => coeffOf (f (t - τ))) t := by
  obtain ⟨B, hB0, hB⟩ := bounded_hsNormSq hf
  refine weakContinuous_of_bdd (fun τ hτ => (hs2_f hf (mem_Icc_sub t hτ)).1) B hB0
    (fun τ hτ => hB _ (mem_Icc_sub t hτ)) fun k => ?_
  exact (continuousOn_coeff hf k).comp (continuous_const.sub continuous_id).continuousOn
    fun σ hσ => mem_Icc_sub t hσ

end Classical

/-- Continuous functions with the same Fourier coefficients coincide. -/
lemma eq_of_coeffOf_eq {g h : Torus d → ℝ} (hg : Continuous g) (hh : Continuous h)
    (e : coeffOf g = coeffOf h) : g = h := by
  have hw : Continuous fun x => g x - h x := hg.sub hh
  have hc : ∀ k, coeffOf (fun x => g x - h x) k = 0 := by
    intro k
    rw [congrFun (coeffOf_sub (integrable_of_continuous hg) (integrable_of_continuous hh)) k,
      e, sub_self]
  have hP := hasSum_sq_coeffOf hw
  have h1 : HasSum (fun k : Lattice d => ‖coeffOf (fun x => g x - h x) k‖ ^ 2) 0 := by
    simp [hc]
  have h0 : ∫ x, (g x - h x) ^ 2 = 0 := hP.unique h1
  have hint : Integrable fun x => (g x - h x) ^ 2 := integrable_of_continuous (hw.pow 2)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint).1 h0
  have hae2 : (fun x => g x - h x) =ᵐ[volume] (fun _ => (0 : ℝ)) := by
    filter_upwards [hae] with x hx
    simpa using hx
  have := (Continuous.ae_eq_iff_eq (volume : Measure (Torus d)) hw continuous_const).1 hae2
  funext x
  exact sub_eq_zero.1 (congrFun this x)

/-- The kernel facts for `d = 1`, from the `d = 1` kernel facts of `HRS/Kernel/GradD1.lean`. -/
lemma convKernelFacts_one (hd : d = 1) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ConvKernelFacts d s :=
  ⟨fun h hh => convGradConv_continuous_of_one_le (by omega) hs0 hsd h hh,
    fun h hh i => convGradConv_coeff_of_one_le (by omega) hs0 hsd h hh i⟩

lemma convKernelFacts (hd : 1 ≤ d) (D : DynData d) : ConvKernelFacts d D.s := by
  rcases Nat.lt_or_ge d 2 with h | h
  · exact convKernelFacts_one (by omega) D.hs0 D.hsd
  · exact convKernelFacts_of_two_le h D.hs0 D.hsd

end HRS.PDE.ClassicalAux
