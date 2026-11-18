import HRS.PDE.ForwardEq
import HRS.PDE.KernelInputsD1
import HRS.Analysis.Category
import HRS.PDE.Toolbox.Quadratic
import HRS.PDE.Toolbox.CoeffBounds
import HRS.PDE.Toolbox.Product
import HRS.PDE.Toolbox.Friedrichs
import HRS.PDE.Toolbox.Symbol
import HRS.PDE.Toolbox.SameFunction
import HRS.PDE.Toolbox.Weighted
import HRS.PDE.Toolbox.Levy

/-!
# Torus PDE layer IV: Appendix C auxiliary lemmas (torus versions) and the kernel inputs of the
regime-R2 estimates

Sources (HRS periodic main paper, Appendix C `B:app:aux`, lines 12221–12325):
* Lemma C.1 `B:lem:coefficient-bounds` (12224–12226);
* Lemma C.3 `B:lem:quadratic-toolbox` (12253–12268), items (i)–(v);
* Lemma C.4 `lem:periodic-same-function` (12276–12284);
* Lemma C.5 `B:lem:product-toolbox` (12298–12305), items (i)–(iii);
* Lemma C.6 `B:lem:sqrt-lipschitz` (12311–12313) is `HRS.sqrt_lipschitz` (ANAL-01);
* Lemma C.7 `B:lem:friedrichs` (12319–12321);
* Lemma C.2 `B:lem:mollified-kernels` (12235–12237) is package KERN-01, not stated here.

## Scope and representation (SPEC_NOTES §1, §4)

* C.3 is stated in the source "on `𝕋^d` or `ℝ^d`"; **only the torus versions are specified here**;
  the `ℝ^d` versions belong to the whole-space packages and are recorded as not covered.
* A Fourier multiplier `K` with symbol `𝔪` acts on functions through `coeffOf`; its quadratic form
  is `symbolForm 𝔪 u v = Re ∑_k 𝔪(k) û(k) \overline{v̂(k)}` (meaningful under the stated summability,
  which is part of every conclusion).  `multiplierForm` of `HRS/Kernel/Riesz.lean` (real basis) is
  the same form (`symbolForm_eq_multiplierForm`).
* C.4 defines `⟨κ*(aw), w⟩` for a non-integrable odd kernel by symmetric truncation; the statement
  is given in that form (symmetrized double integral + convergence of the truncations).  The
  identification of this real-space pairing with the Fourier-side pairing for `κ = v·∇g` is the
  **required kernel fact** `rieszGrad_pairing_symmetrized` (extends KERN-01).
* All real suprema (`cbNorm`, `supNorm`, `holderSeminorm`) are applied only under hypotheses
  (`IsCk`, `IsLipschitz`) that make them honest; on the compact torus a `C^k` function has bounded
  derivatives.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Function-level forms and function classes -/

/-- `B(u,v) = ⟨Ku, v⟩_{L²} = Re ∑_k 𝔪(k) û(k) \overline{v̂(k)}` for a real multiplier. -/
def symbolForm (𝔪 : Lattice d → ℝ) (u v : Torus d → ℝ) : ℝ :=
  (bilinForm 𝔪 (coeffOf u) (coeffOf v)).re

/-- The quadratic form `∑_k 𝔪(k)|û(k)|²` is finite. -/
def SymbolFormFinite (𝔪 : Lattice d → ℝ) (u : Torus d → ℝ) : Prop :=
  Summable fun k => 𝔪 k * ‖coeffOf u k‖ ^ 2

/-- `‖w‖²_{L²(𝕋^d)}`. -/
def l2NormSq (w : Torus d → ℝ) : ℝ := ∫ x, w x ^ 2

/-- `u ∈ C^{1,1}_b(𝕋^d)` with Lipschitz constant `L` of the gradient. -/
def IsC11 (L : ℝ) (u : Torus d → ℝ) : Prop :=
  Torus.IsCk 1 u ∧ LipschitzWith (Real.toNNReal L) (fun x => fderiv ℝ (Torus.lift u) x)

/-- `C^k` functions of two torus variables, through the lift to `ℝ^d × ℝ^d`. -/
def lift2 (R : Torus d → Torus d → ℝ) : Euc d × Euc d → ℝ := fun p => R (Torus.mk p.1) (Torus.mk p.2)

/-- `R ∈ C^k(𝕋^d × 𝕋^d)`. -/
def IsCk2 (k : ℕ) (R : Torus d → Torus d → ℝ) : Prop := ContDiff ℝ k (lift2 R)

/-- The `C^k` norm (sum over orders) of a function of two torus variables. -/
def cbNorm2 (k : ℕ) (R : Torus d → Torus d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ⨆ p : Euc d × Euc d, ‖iteratedFDeriv ℝ j (lift2 R) p‖

/-- The symbol class of Lemma C.3: `𝔪` is the restriction to `ℤ^d` of a real, even, nonnegative
function on `ℝ^d`, smooth away from `0` and homogeneous of degree `θ` there, with `𝔪(0) = 0`
(lines 12254–12255). -/
structure IsHomogSymbol (θ : ℝ) (𝔪 : Lattice d → ℝ) : Prop where
  exists_ext : ∃ m₀ : Euc d → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀ {ξ | ξ ≠ 0} ∧ (∀ ξ, m₀ (-ξ) = m₀ ξ) ∧ (∀ ξ, 0 ≤ m₀ ξ) ∧
      (∀ c : ℝ, 0 < c → ∀ ξ, m₀ (c • ξ) = c ^ θ * m₀ ξ) ∧ (∀ k : Lattice d, k ≠ 0 → 𝔪 k = m₀ (Lattice.toEuc k))
  zero : 𝔪 0 = 0

/-- The Lévy-kernel representation of Lemma C.3(ii) (lines 12257–12261): an even kernel `𝔨`,
smooth away from `0`, with `|𝔨(z)| ≤ C(|z|^{-d-θ} + 1)`, such that
`∫ 𝔨(z)(1 - cos 2πk·z) dz = 𝔪(k)` (absolutely convergent), the principal-value formula
`Ku(x) = lim_{ε→0} ∫_{|z|>ε} 𝔨(z)(u(x) - u(x-z)) dz` for `u ∈ C^{1,1}_b` (pointwise, where `Ku`
is the function with coefficients `𝔪 û`), and the bilinear identity
`B(u,v) = ½ ∬ 𝔨(z) δ_z u(x) δ_z v(x) dz dx` (absolutely convergent) for Lipschitz `u, v`. -/
structure IsLevyKernel (θ : ℝ) (𝔪 : Lattice d → ℝ) (𝔨 : Torus d → ℝ) : Prop where
  even : ∀ z, 𝔨 (-z) = 𝔨 z
  smooth : Torus.IsSmoothOffZero 𝔨
  bound : ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 → |𝔨 z| ≤ C * (Torus.tdist z 0 ^ (-(d : ℝ) - θ) + 1)
  symbol : ∀ k : Lattice d, Integrable (fun z => 𝔨 z * (1 - Torus.cosMode k z)) ∧
    ∫ z, 𝔨 z * (1 - Torus.cosMode k z) = 𝔪 k
  pv : ∀ (L : ℝ) (u : Torus d → ℝ), IsC11 L u → ∃ Ku : Torus d → ℝ,
    MemLp Ku 2 volume ∧ coeffOf Ku = (fun k => ((𝔪 k : ℝ) : ℂ) * coeffOf u k) ∧
    ∀ x, Tendsto (fun ε : ℝ => ∫ z in {z | ε < Torus.tdist z 0}, 𝔨 z * (u x - u (x - z)))
      (𝓝[>] 0) (𝓝 (Ku x))
  bilinear : ∀ (Lu Lv : ℝ) (u v : Torus d → ℝ), Torus.IsLipschitz Lu u → Torus.IsLipschitz Lv v →
    Integrable (fun p : Torus d × Torus d => 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))) ∧
    symbolForm 𝔪 u v =
      (1 / 2) * ∫ p : Torus d × Torus d, 𝔨 p.2 * (u p.1 - u (p.1 - p.2)) * (v p.1 - v (p.1 - p.2))

/-! ### Lemma C.1 -/

/-- Lemma C.1 `B:lem:coefficient-bounds` (lines 12224–12226), first assertion: for `μ ∈ 𝒫(𝕋^d)` with
`‖μ‖_{C^{m+3}} ≤ Λ` and `V ∈ C^{m+3}` with `‖V‖_{C^{m+3}} ≤ VB`, the drift `b = M∇g*μ - ∇V`
(cancellation convention) obeys `B:eq:coeff-bounds` (line 1862):
`‖b‖_{C^{m+1}} + sup_{|q|=1} ‖D_q μ‖_{C^{m+1}} + ‖μ‖_{C^{m+3}} ≤ C = C(d,s,m,|M|,Λ,‖V‖_{C^{m+3}})`. -/
theorem coefficient_bounds (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) :
    ∃ C : ℝ, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (_ : MatBound MB M) (V : Torus d → ℝ)
      (_ : VHyp m VB V) (μ : Torus d → ℝ) (_ : IsProbDensity μ) (_ : Torus.IsCk (m + 3) μ)
      (_ : Torus.cbNorm (m + 3) μ ≤ Λ),
      Torus.IsCk (m + 1) (fun x => Torus.matVec M (convGradConv (periodicRieszGrad d s) μ x) - Torus.grad V x) ∧
      Torus.cbNorm (m + 1) (fun x => Torus.matVec M (convGradConv (periodicRieszGrad d s) μ x) - Torus.grad V x) +
        (⨆ q : {q : Euc d // ‖q‖ = 1}, Torus.cbNorm (m + 1) (fun x => inner ℝ q.1 (Torus.grad μ x))) +
        Torus.cbNorm (m + 3) μ ≤ C := by
  exact coefficient_bounds_aux hd s hs0 hsd m MB Λ VB

/-- Lemma C.1, second assertion: for two such densities,
`‖∇g*(μ₁-μ₂)‖_{C^{m+1}_b} ≤ C ‖μ₁-μ₂‖_{C^{m+2}}`. -/
theorem coefficient_bounds_diff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ : ℝ) :
    ∃ C : ℝ, ∀ (μ₁ μ₂ : Torus d → ℝ) (_ : IsProbDensity μ₁) (_ : IsProbDensity μ₂)
      (_ : Torus.IsCk (m + 3) μ₁) (_ : Torus.IsCk (m + 3) μ₂)
      (_ : Torus.cbNorm (m + 3) μ₁ ≤ Λ) (_ : Torus.cbNorm (m + 3) μ₂ ≤ Λ),
      Torus.IsCk (m + 1) (convGradConv (periodicRieszGrad d s) (μ₁ - μ₂)) ∧
      Torus.cbNorm (m + 1) (convGradConv (periodicRieszGrad d s) (μ₁ - μ₂)) ≤ C * Torus.cbNorm (m + 2) (μ₁ - μ₂) := by
  exact coefficient_bounds_diff_aux hd s hs0 hsd m Λ

/-! ### Lemma C.3 (torus version) -/

/-- The symbols `𝔪_l` of `B:eq:Kl-def` (lines 1831–1834) belong to the symbol class of Lemma C.3
with `θ = s + 2 - d ∈ (0,2)` (for `d - 2 < s < d` and the standing assumption `0 ≤ s`, which is
implied by `d - 2 < s` when `d ≥ 2`; for `d = 1` and `s < 0` the constant `c_{1,s}` is negative). -/
theorem symbolK_isHomogSymbol (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d)
    (q : Euc d) : IsHomogSymbol (thetaOrder d s) (symbolK d s q) := by
  refine ⟨⟨SymAux.symExt d s q, SymAux.symExt_contDiffOn d s q, SymAux.symExt_neg d s q,
    SymAux.symExt_nonneg hd hs0 hsd q, fun c hc ξ => SymAux.symExt_smul d s q c hc ξ,
    fun k hk => SymAux.symExt_eq d s q k hk⟩, SymAux.symbolK_zero d s q⟩

/-- The complex coefficient form agrees with the real-basis `multiplierForm` of
`HRS/Kernel/Riesz.lean` for `L²` functions with finite form. -/
theorem symbolForm_eq_multiplierForm (𝔪 : Lattice d → ℝ) (h0 : 𝔪 0 = 0)
    (heven : ∀ k, 𝔪 (-k) = 𝔪 k) (u v : Torus d → ℝ) (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hfu : SymbolFormFinite 𝔪 u) (hfv : SymbolFormFinite 𝔪 v) :
    symbolForm 𝔪 u v = multiplierForm 𝔪 u v := by
  unfold symbolForm bilinForm multiplierForm SymbolFormFinite at *
  simp only [coeffOf_eq_fcoefC] at *
  exact SymAux.form_eq_multiplier 𝔪 h0 heven (hu.integrable one_le_two) (hv.integrable one_le_two)
    hfu hfv

/-- Lemma C.3(i) (line 12256): for a symbol of the class with `θ ∈ (0,2)`, `B` is symmetric,
positive semidefinite, and `B(u,u) ≤ C ‖u‖²_{H^{θ/2}}` (all forms finite for `u, v ∈ H^{θ/2}`). -/
theorem quadratic_toolbox_basic (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) (𝔪 : Lattice d → ℝ)
    (h𝔪 : IsHomogSymbol θ 𝔪) :
    ∃ C : ℝ, ∀ u v : Torus d → ℝ, MemSobolev (θ / 2) u → MemSobolev (θ / 2) v →
      SymbolFormFinite 𝔪 u ∧ SymbolFormFinite 𝔪 v ∧
      Summable (fun k => ((𝔪 k : ℝ) : ℂ) * (coeffOf u k * conj (coeffOf v k))) ∧
      symbolForm 𝔪 u v = symbolForm 𝔪 v u ∧ 0 ≤ symbolForm 𝔪 u u ∧
      symbolForm 𝔪 u u ≤ C * sobolevNorm (θ / 2) u ^ 2 := by
  obtain ⟨m₀, hsm, -, hnn, hhom, hext⟩ := h𝔪.exists_ext
  obtain ⟨A, hA⟩ := symbol_bound θ hθ0 𝔪 m₀ hsm hnn hhom hext h𝔪.zero
  refine ⟨A, fun u v hu hv => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := quad_core θ 𝔪 A hA u v hu hv
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Lemma C.3(ii) (lines 12257–12261), torus version: the Lévy kernel `𝔨` exists
(`IsLevyKernel`: even, smooth off `0`, bound `C(|z|^{-d-θ}+1)`, `∫𝔨(1-cos 2πk·z) = 𝔪(k)`,
principal-value formula for `C^{1,1}_b` functions, bilinear identity for Lipschitz functions). -/
theorem quadratic_toolbox_kernel (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (𝔪 : Lattice d → ℝ) (h𝔪 : IsHomogSymbol θ 𝔪) :
    ∃ 𝔨 : Torus d → ℝ, IsLevyKernel θ 𝔪 𝔨 := by
  obtain ⟨m₀, hsm, he, -, hhom, hext⟩ := h𝔪.exists_ext
  have hd0 : 0 < d := by omega
  have hm := LevyAux.measurable_levyK (θ := θ) hd0 hθ0 hsm
  have hev := LevyAux.levyK_even (θ := θ) he
  have hI := LevyAux.levyK_integrable_sq hd0 hθ0 hθ2 hsm
  have hsy := LevyAux.levyK_symbol 𝔪 hd0 hθ0 hθ2 hsm he hhom hext h𝔪.zero
  refine ⟨LevyAux.levyK θ m₀, ?_⟩
  exact
    { even := hev
      smooth := LevyAux.levyK_smooth hd0 θ hsm
      bound := LevyAux.levyK_bound hd0 hθ0 hsm
      symbol := hsy
      pv := fun L u hu => LevyAux.levy_pv hm hev hI 𝔪 (fun k => (hsy k).2) hu.1 hu.2
      bilinear := fun Lu Lv u v hu hv =>
        LevyAux.levy_bilinear hm hI 𝔪 (fun k => (hsy k).2) hu hv }

/-- Lemma C.3(iii) (lines 12262–12264), weighted symmetrization: for `0 ≤ a ∈ C^{1,1}_b` with
`m = √a` (Lipschitz by C.6) and Lipschitz `w`,
`B(aw,w) = B(mw,mw) + E`, `E = -½ ∬ 𝔨(z) w(x) w(x-z) (δ_z m(x))² dz dx`, and
`|E| ≤ C (‖∇m‖²_∞ + ‖m‖²_∞) ‖w‖²_{L²}` with `C` depending on the kernel only. -/
theorem quadratic_toolbox_weighted (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (𝔪 : Lattice d → ℝ) (h𝔪 : IsHomogSymbol θ 𝔪) (𝔨 : Torus d → ℝ) (h𝔨 : IsLevyKernel θ 𝔪 𝔨) :
    ∃ C : ℝ, ∀ (L La Lm Lw : ℝ) (a w : Torus d → ℝ), (∀ x, 0 ≤ a x) → IsC11 L a →
      Torus.IsLipschitz La a → Torus.IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      Torus.IsLipschitz Lw w →
      let m := fun x => Real.sqrt (a x)
      let E := symbolForm 𝔪 (fun x => a x * w x) w - symbolForm 𝔪 (fun x => m x * w x) (fun x => m x * w x)
      Integrable (fun p : Torus d × Torus d => 𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2) ∧
      E = -(1 / 2) * ∫ p : Torus d × Torus d, 𝔨 p.2 * w p.1 * w (p.1 - p.2) * (m p.1 - m (p.1 - p.2)) ^ 2 ∧
      |E| ≤ C * (Lm ^ 2 + Torus.supNorm m ^ 2) * l2NormSq w := by
  obtain ⟨C, -, hC⟩ := WeightAux.weighted_core (by omega : 1 ≤ d) hθ2
    (LocInt.measurable_of_smoothOffZero h𝔨.smooth) h𝔨.bound
  refine ⟨C, ?_⟩
  intro L La Lm Lw a w ha0 _ _ hLm hLw m E
  exact hC (symbolForm 𝔪) (fun Lu Lv u v hu hv => h𝔨.bilinear Lu Lv u v hu hv) Lm Lw
    (fun x => Real.sqrt (a x)) w a hLm hLw (fun x => (Real.sq_sqrt (ha0 x)).symm)

/-- For a symbol of the class, the quadratic form is nonnegative on the diagonal
(`𝔪 ≥ 0`, so `symbolForm 𝔪 u u = ∑_k 𝔪(k)|û(k)|² ≥ 0`, the series being `0` if not summable). -/
theorem symbolForm_self_nonneg {θ : ℝ} (𝔪 : Lattice d → ℝ) (h𝔪 : IsHomogSymbol θ 𝔪)
    (u : Torus d → ℝ) : 0 ≤ symbolForm 𝔪 u u := by
  obtain ⟨m₀, -, -, hnn, -, hext⟩ := h𝔪.exists_ext
  have h0 : ∀ k, 0 ≤ 𝔪 k := fun k => by
    by_cases hk : k = 0
    · rw [hk, h𝔪.zero]
    · rw [hext k hk]; exact hnn _
  unfold symbolForm bilinForm
  have : ∀ k, ((𝔪 k : ℝ) : ℂ) * (coeffOf u k * conj (coeffOf u k)) =
      ((𝔪 k * ‖coeffOf u k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  simp_rw [this]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg fun k => mul_nonneg (h0 k) (sq_nonneg _)

/-- Lemma C.3(iv) (line 12265), weighted comparison: if moreover `a ≥ λ₀ > 0`, then
`B(w,w) ≤ λ₀⁻¹ B(mw,mw) + C(1+λ₀⁻¹)(‖√a‖²_{C^{0,1}} + ‖√(a/λ₀-1)‖²_{C^{0,1}} + 1) ‖w‖²_{L²}`. -/
theorem quadratic_toolbox_compare (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2)
    (𝔪 : Lattice d → ℝ) (h𝔪 : IsHomogSymbol θ 𝔪) :
    ∃ C : ℝ, ∀ (L lam0 Lm Lm' Lw : ℝ) (a w : Torus d → ℝ), 0 < lam0 → (∀ x, lam0 ≤ a x) → IsC11 L a →
      Torus.IsLipschitz Lm (fun x => Real.sqrt (a x)) →
      Torus.IsLipschitz Lm' (fun x => Real.sqrt (a x / lam0 - 1)) → Torus.IsLipschitz Lw w →
      let m := fun x => Real.sqrt (a x)
      symbolForm 𝔪 w w ≤ lam0⁻¹ * symbolForm 𝔪 (fun x => m x * w x) (fun x => m x * w x) +
        C * (1 + lam0⁻¹) * (Torus.c01Norm m ^ 2 +
          Torus.c01Norm (fun x => Real.sqrt (a x / lam0 - 1)) ^ 2 + 1) * l2NormSq w := by
  obtain ⟨𝔨, h𝔨⟩ := quadratic_toolbox_kernel hd θ hθ0 hθ2 𝔪 h𝔪
  obtain ⟨C, -, hC⟩ := WeightAux.compare_core (by omega : 1 ≤ d) hθ2
    (LocInt.measurable_of_smoothOffZero h𝔨.smooth) h𝔨.bound
  refine ⟨C, ?_⟩
  intro L lam0 Lm Lm' Lw a w hl hla _ hLm hLm' hLw m
  exact hC (symbolForm 𝔪) (fun Lu Lv u v hu hv => h𝔨.bilinear Lu Lv u v hu hv)
    (symbolForm_self_nonneg 𝔪 h𝔪) lam0 Lm Lm' Lw a w hl hla hLm hLm' hLw

/-- Lemma C.3(v) (line 12266), Cauchy–Schwarz for the form. -/
theorem quadratic_toolbox_cauchySchwarz (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) (𝔪 : Lattice d → ℝ)
    (h𝔪 : IsHomogSymbol θ 𝔪) (u v : Torus d → ℝ) (hu : MemSobolev (θ / 2) u)
    (hv : MemSobolev (θ / 2) v) :
    |symbolForm 𝔪 u v| ≤ Real.sqrt (symbolForm 𝔪 u u) * Real.sqrt (symbolForm 𝔪 v v) := by
  obtain ⟨m₀, hsm, -, hnn, hhom, hext⟩ := h𝔪.exists_ext
  obtain ⟨A, hA⟩ := symbol_bound θ hθ0 𝔪 m₀ hsm hnn hhom hext h𝔪.zero
  exact (quad_core θ 𝔪 A hA u v hu hv).2.2.2.2.2.2

/-! ### Lemma C.4 (same-function symmetrization on the torus) -/

/-- Lemma C.4 `lem:periodic-same-function` (lines 12276–12284): for `κ` odd, smooth away from zero,
with `|κ(z)| ≤ K₀(1 + |z|^{-s-1})`, `s < d`, `a ∈ C^{0,1}(𝕋^d)` and `w ∈ L²(𝕋^d)`, the symmetrized
pairing `⟨κ*(aw), w⟩ := ½ ∬ κ(x-y) w(x) w(y)(a(y) - a(x)) dx dy` is absolutely convergent, is the
limit of the symmetric truncations `∬_{|x-y|>ε} κ(x-y) a(y) w(y) w(x)` (which define the pairing
when the force is not integrable, lines 12290–12292), and
`|⟨κ*(aw), w⟩| ≤ C K₀ ‖a‖_{C^{0,1}} ‖w‖²_{L²}` with `C = C(d,s)`. -/
theorem periodic_same_function (hd : 1 ≤ d) (s : ℝ) (hsd : s < d) :
    ∃ C : ℝ, ∀ (κ : Torus d → ℝ) (K₀ : ℝ), (∀ z, κ (-z) = -κ z) → Torus.IsSmoothOffZero κ →
      (∀ z : Torus d, z ≠ 0 → |κ z| ≤ K₀ * (1 + Torus.tdist z 0 ^ (-s - 1))) →
      ∀ (La : ℝ) (a w : Torus d → ℝ), Torus.IsLipschitz La a → MemLp w 2 volume →
      Integrable (fun p : Torus d × Torus d => κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1)) ∧
      (∀ ε : ℝ, 0 < ε →
        Integrable (fun p : Torus d × Torus d =>
          if ε < Torus.tdist p.1 p.2 then κ (p.1 - p.2) * a p.2 * w p.2 * w p.1 else 0)) ∧
      Tendsto (fun ε : ℝ => ∫ p : Torus d × Torus d,
          if ε < Torus.tdist p.1 p.2 then κ (p.1 - p.2) * a p.2 * w p.2 * w p.1 else 0)
        (𝓝[>] 0)
        (𝓝 ((1 / 2) * ∫ p : Torus d × Torus d, κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1))) ∧
      |(1 / 2) * ∫ p : Torus d × Torus d, κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1)| ≤
        C * K₀ * Torus.c01Norm a * l2NormSq w := by
  exact SameFn.main hd s hsd

/-- **Required kernel fact** (serves the regime-R2 estimates (iii), (v) of Prop 3.13 and Prop 3.14,
lines 1919–1926, 1951).  For the odd kernel `κ = v·∇g` (`v ∈ ℝ^d`; `κ = D_l g` for `v = q_l`,
`κ_j = ∑_i A_{ij}∂_i g` for `v = A_{·j}`), Lipschitz `a` and a real trigonometric polynomial `w`,
the Fourier-side pairing `Re ∑_k (2πi v·k) ĝ(k) (aw)^(k) \overline{ŵ(k)}` equals the symmetrized
real-space pairing of Lemma C.4.  Extends KERN-01 (`periodicRiesz_fourierCoeff`,
`periodicRiesz_grad_bound`). -/
theorem rieszGrad_pairing_symmetrized (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    (La : ℝ) (a : Torus d → ℝ) (ha : Torus.IsLipschitz La a) (n : ℕ) (w : Torus d → ℝ)
    (hw : Torus.IsCk 1 w) (hwtrig : IsTrigPoly n (coeffOf w)) :
    (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
        (coeffOf (fun x => a x * w x) k * conj (coeffOf w k))).re =
      (1 / 2) * ∫ p : Torus d × Torus d,
        inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) * w p.1 * w p.2 * (a p.2 - a p.1) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · exact KernelGradD1.rieszGrad_pairing_symmetrized (by omega) s hs0 hsd v La a ha n w hw hwtrig
  · exact KernelGrad.rieszGrad_pairing_symmetrized h s hs0 hsd v La a ha n w hw hwtrig

/-! ### Lemma C.5 (product bounds on `𝕋^d`) -/

/-- Lemma C.5(i) (line 12301): `‖au‖_{H^{-1}} ≤ C ‖a‖_{C¹_b} ‖u‖_{H^{-1}}`, at the level of coefficient
sequences (`u ∈ H^{-1}` a distribution; the product is the absolutely convergent coefficient
convolution). -/
theorem product_toolbox_dual (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ (a : Torus d → ℝ), Torus.IsCk 1 a → ∀ u : Coeff d, MemHs (-1) u →
      (∀ k, Summable fun j => coeffOf a (k - j) * u j) ∧
      MemHs (-1) (mulCoeff (coeffOf a) u) ∧
      hsNorm (-1) (mulCoeff (coeffOf a) u) ≤ C * Torus.cbNorm 1 a * hsNorm (-1) u := by
  refine ⟨prodConstH1 d, fun a ha u hu => ⟨summable_mulCoeff_dual ha hu, ?_⟩⟩
  exact product_dual_aux ha hu

/-- Lemma C.5(ii) (line 12302): for `σ ∈ [0,1]`, `‖au‖_{H^σ} ≤ C ‖a‖_{C^{0,1}_b} ‖u‖_{H^σ}`. -/
theorem product_toolbox_frac (hd : 1 ≤ d) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ C : ℝ, ∀ (La : ℝ) (a : Torus d → ℝ), Torus.IsLipschitz La a →
      ∀ u : Torus d → ℝ, MemSobolev σ u →
        MemSobolev σ (fun x => a x * u x) ∧
        sobolevNorm σ (fun x => a x * u x) ≤ C * Torus.c01Norm a * sobolevNorm σ u := by
  obtain ⟨C, -, hC⟩ := ProdAux.real_product_bound hd σ hσ0 hσ1
  refine ⟨C, fun La a ha u hu => ?_⟩
  exact hC a _ _ (ProdAux.prodHyp_of_lipschitz ha) u hu

/-- Lemma C.5(iii) (line 12303): for `σ ≥ 0`, `‖au‖_{H^σ} ≤ C_σ ‖a‖_{C^{⌈σ⌉}_b} ‖u‖_{H^σ}`. -/
theorem product_toolbox_frac_high (hd : 1 ≤ d) (σ : ℝ) (hσ0 : 0 ≤ σ) :
    ∃ C : ℝ, ∀ (a : Torus d → ℝ), Torus.IsCk ⌈σ⌉₊ a →
      ∀ u : Torus d → ℝ, MemSobolev σ u →
        MemSobolev σ (fun x => a x * u x) ∧
        sobolevNorm σ (fun x => a x * u x) ≤ C * Torus.cbNorm ⌈σ⌉₊ a * sobolevNorm σ u := by
  obtain ⟨C, -, hC⟩ := ProdAux.real_product_bound_high hd σ hσ0
  exact ⟨C, fun a ha u hu => hC a ha u hu⟩

/-! ### Lemma C.7 (Friedrichs commutators) -/

/-- A Friedrichs cutoff `χ₁ ∈ C_c^∞(ℝ^d;[0,1])`, radial, `≡ 1` on `B(0,1)`, supported in `B(0,2)`
(Step 1 of the proof of Prop 3.9, line 1957). -/
structure IsFriedrichsCutoff (χ : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  range : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1
  radial : ∀ ξ η : Euc d, ‖ξ‖ = ‖η‖ → χ ξ = χ η
  one : ∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 1
  support : ∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 0

/-- The mollifier `J_ε = χ₁(εD)²` (Fourier multiplier `χ₁(εk)²`), on coefficient sequences. -/
def mollify (χ : Euc d → ℝ) (ε : ℝ) (c : Coeff d) : Coeff d :=
  fun k => ((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) * c k

/-- The commutator `[J_ε, a]u = J_ε(au) - a J_ε u` (coefficients). -/
def mollifyCommutator (χ : Euc d → ℝ) (ε : ℝ) (a : Torus d → ℝ) (u : Coeff d) : Coeff d :=
  mollify χ ε (mulCoeff (coeffOf a) u) - mulCoeff (coeffOf a) (mollify χ ε u)

/-- The transport commutator `[J_ε, b·∇]u = J_ε(b·∇u) - b·∇(J_ε u)` (coefficients; `b·∇u` is the
distribution `∑_j b_j ∂_j u` for `u ∈ L²`). -/
def mollifyTransportCommutator (χ : Euc d → ℝ) (ε : ℝ) (b : Fin d → Torus d → ℝ) (u : Coeff d) :
    Coeff d :=
  mollify χ ε (fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j u) k) -
    fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j (mollify χ ε u)) k

/-- Lemma C.7 `B:lem:friedrichs` (lines 12319–12321), torus version with `J_ε = χ₁(εD)²`:
for `a ∈ C¹_b`, `u ∈ L²`, `ε ∈ (0,1]`:
`‖[J_ε,a]u‖_{L²} ≤ C ε ‖∇a‖_∞ ‖u‖_{L²}` and `‖[J_ε,a]u‖_{H^σ} ≤ C ε^{1-σ} ‖a‖_{C¹} ‖u‖_{L²}` for
`σ ∈ [0,1]`. -/
theorem friedrichs_commutator (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsFriedrichsCutoff χ) :
    ∃ C : ℝ, ∀ (a : Torus d → ℝ), Torus.IsCk 1 a → ∀ (u : Coeff d), MemHs 0 u →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        MemHs 1 (mollifyCommutator χ ε a u) ∧
        hsNorm 0 (mollifyCommutator χ ε a u) ≤
          C * ε * (⨆ x : Euc d, ‖fderiv ℝ (Torus.lift a) x‖) * hsNorm 0 u ∧
        ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
          hsNorm σ (mollifyCommutator χ ε a u) ≤ C * ε ^ (1 - σ) * Torus.cbNorm 1 a * hsNorm 0 u := by
  obtain ⟨C, -, hC⟩ := Fried.friedrichs_main (d := d)
    (χ := χ) ⟨hχ.smooth, hχ.range, hχ.one, hχ.support⟩
  exact ⟨C, hC⟩

/-- Lemma C.7, transport commutator: for `b ∈ C¹_b` vector-valued and `u ∈ L²`,
`‖[J_ε, b·∇]u‖_{L²} ≤ C ‖∇b‖_∞ ‖u‖_{L²}` uniformly in `ε ∈ (0,1]`, and
`[J_ε, b·∇]u → 0` in `L²` as `ε → 0` for each fixed `u`. -/
theorem friedrichs_transport_commutator (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsFriedrichsCutoff χ) :
    ∃ C : ℝ, ∀ (b : Fin d → Torus d → ℝ), (∀ j, Torus.IsCk 1 (b j)) → ∀ (u : Coeff d), MemHs 0 u →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        MemHs 0 (mollifyTransportCommutator χ ε b u) ∧
        hsNorm 0 (mollifyTransportCommutator χ ε b u) ≤
          C * (∑ j, ⨆ x : Euc d, ‖fderiv ℝ (Torus.lift (b j)) x‖) * hsNorm 0 u) ∧
      Tendsto (fun ε => hsNorm 0 (mollifyTransportCommutator χ ε b u)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := Fried.friedrichs_transport_main (d := d)
    (χ := χ) ⟨hχ.smooth, hχ.range, hχ.one, hχ.support⟩
  exact ⟨C, hC⟩

end HRS.PDE
