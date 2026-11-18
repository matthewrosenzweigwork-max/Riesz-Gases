import HRS.Energy.Pressure
import HRS.External.WuResampling
import HRS.External.WeakSpec
import HRS.Kernel.D1
import HRS.Energy.Coercivity

/-!
# HRS.Energy.WeakReference — Lemmas 5.6 and 5.7 (weak nonnegative interaction)

Main paper, Section 5.2 "A weak nonnegative interaction" (source lines 6144-6172 and 6271-6278):
`q(x,y) = q(y,x) ≥ 0`, `q(x,y) ≤ A w(x-y)` with `w = g + c_*`, and `a := sup_x ∫ q(x,y) dμ(y) < a₀`
(`N:eq:q-small`); `ℝ_{N,τ} = Q^q_{N,τβ}(μ)` for `0 ≤ τ ≤ 1`.

Representation decisions (recorded in `docs/ISSUES.md` §H):
* `ℝ_{N,τ} = (μ^{⊗N}).withDensity (W/K)` with `W(X) = exp(-τβN F_N^q(X, μ))` and `K = ∫⁻ W dμ^{⊗N}`; its
  one-coordinate conditional laws are `HRS.External.siteKernel μ W i x` (the kernel does not depend on the
  normalisation of `W`), the same objects Wu's inequality (`HRS.External.wu_resampling`) consumes.
* `a < a₀` is a hypothesis on a number `a` bounding `∫⁻ q(x,·) dμ` for every `x` (no real `iSup`).
* "a₀ chosen small depending on the fixed upper temperature and the density bounds; A finite and fixed":
  `a₀` and the constants are chosen after `A`, the temperature interval and the density bounds, before `ρ`, `q`.
* Lemma 5.6 is stated without the clause "these bounds also hold after one pin and for the cavity law"; that
  clause is a separate statement (still to be written), and the coverage row stays partial until then.
* `|log K^q_{N,β}(μ)| ≤ C N δ_N` (Lemma 5.7) is stated as two-sided `lintegral` bounds.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS

variable {d : ℕ}

/-- Unnormalised Gibbs weight `exp(-β N F_N^q(X, μ))` of a pair kernel `q`. -/
def pairWeight (q : Torus d → Torus d → ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Torus d))
    (X : Config d N) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * N * modulatedEnergy q X μ))

/-- `K^q_{N,β}(μ) = ∫ exp(-β N F_N^q) dμ^{⊗N}`. -/
def pairPartition (q : Torus d → Torus d → ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Torus d)) : ℝ≥0∞ :=
  ∫⁻ X, pairWeight q N β μ X ∂(Measure.pi fun _ => μ)

/-- `Q^q_{N,β}(μ)`, the normalised Gibbs law of the pair kernel `q`. -/
def pairGibbsLaw (q : Torus d → Torus d → ℝ) (N : ℕ) (β : ℝ) (μ : Measure (Torus d)) :
    Measure (Config d N) :=
  (Measure.pi fun _ => μ).withDensity fun X => pairWeight q N β μ X / pairPartition q N β μ

/-! ### Route for Lemmas 5.6/5.7 (worker MAIN-02)

Done here (Dobrushin layer, source lines 6175-6190): the conditional weight of `ℝ_{N,τ}` in coordinate `i`
factors as `c(x) · v(z)` with `v(z) = exp(-(τβ/N) ∑_{l≠i} q(z,x_l) + τβ (q*μ)(z))`
(`weight_update`, `siteKernel_eq`); `e^{-τβ a} ≤ ∫ v dμ`, `v ≤ e^{τβ a}` (Jensen via the tangent line) give the
density bound `≤ e^{2τβ a} μ` (`siteKernel_le`); a change of one coordinate `j` changes `v` in `L¹(μ)` by at
most `e^{τβ a}(τβ/N) 2a` (`1 - e^{-u} ≤ u`), hence `siteKernel_coeff` (`4 e^{2τβ a} τβ a / N`); Wu's
inequality with constant `2` (`wu_clause`, via `wu_resampling_half` for `W/K`); and `K ≥ 1`
(`one_le_partition`, Jensen with `E[N F^q] = -½ ∬q ≤ 0`).

Done (worker `weakm`):

* `weak_marginal_aux` (source 6206-6268), via `weak_marginal_strong` (sections WM_A-WM_J): cavity formula for the
  marginal density, Laplace residual through the variance of the truncated sum, convolution `L²` estimate
  (Riesz envelope, polar coordinates, level-set integrals), Schur contraction with explicit constants.
* `weak_pressure_upper_aux` (source 6281-6340), sections WM_K-WM_Z.  Route: `Z(t) = ∫ e^{-t G} dμ^{⊗N}` with
  `G = N F_N^q`, `K^q_{N,t}(μ) = Z(t)` and `log Z(t)' = -E_t[G]`, `(log Z)'' = Var_{ℝ_t}(G)`.  The variance bound
  (`variance_G_le`, Wu's inequality applied twice with pinned marginals, `evariance_G_le`, `second_moment_gi`)
  is `Var ≤ C (ψ₂(2NP/t) + ψ₂(N))` (`variance_at`; `ψ₂` = order of `∫ min(w,L)²`, regime wise `1`, `log(eL)`,
  `L^{2-d/s}`) using the marginal `L²` bound for the field difference (`theta_abstract`) and the level-set
  bounds `row_bounds_real`.  The ODE comparison lemma `ode_bound`/`logZ_upper` with the explicit antiderivatives
  `exists_W` (integrable singularity `J_N(t)`) gives `log K ≤ β(½∬q + W(β)) ≤ C N δ_N`. -/

namespace WeakRef

variable {N : ℕ}

/-- row integral `H x = ∫ q(x,y) dμ(y)` -/
def rowInt (q : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (x : Torus d) : ℝ :=
  ∫ y, q x y ∂μ

/-- Hypotheses on the weak kernel. -/
structure WeakKernel (μ : Measure (Torus d)) (a : ℝ) (q : Torus d → Torus d → ℝ) : Prop where
  meas : Measurable (Function.uncurry q)
  symm : ∀ x y, q x y = q y x
  nonneg : ∀ x y, 0 ≤ q x y
  row : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ ≤ ENNReal.ofReal a

section WK

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

lemma WeakKernel.measurable_left (h : WeakKernel μ a q) (x : Torus d) : Measurable (q x) :=
  h.meas.comp (measurable_const.prodMk measurable_id)

lemma WeakKernel.measurable_right (h : WeakKernel μ a q) (y : Torus d) :
    Measurable (fun x => q x y) :=
  h.meas.comp (measurable_id.prodMk measurable_const)

lemma WeakKernel.integrable_row (h : WeakKernel μ a q) (x : Torus d) : Integrable (q x) μ := by
  refine ⟨(h.measurable_left x).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ y, ‖q x y‖ₑ = ENNReal.ofReal (q x y) := fun y => by
    rw [Real.enorm_eq_ofReal (h.nonneg x y)]
  simp_rw [this]
  exact lt_of_le_of_lt (h.row x) ENNReal.ofReal_lt_top

lemma WeakKernel.integrable_col (h : WeakKernel μ a q) (y : Torus d) :
    Integrable (fun x => q x y) μ := by
  simpa [h.symm] using h.integrable_row y

lemma WeakKernel.rowInt_nonneg (h : WeakKernel μ a q) (x : Torus d) : 0 ≤ rowInt q μ x :=
  integral_nonneg fun y => h.nonneg x y

lemma WeakKernel.rowInt_le (h : WeakKernel μ a q) (ha : 0 ≤ a) (x : Torus d) :
    rowInt q μ x ≤ a := by
  have h1 : ENNReal.ofReal (rowInt q μ x) = ∫⁻ y, ENNReal.ofReal (q x y) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (h.integrable_row x)
      (Filter.Eventually.of_forall fun y => h.nonneg x y)
  have := (h.row x)
  rw [← h1] at this
  exact (ENNReal.ofReal_le_ofReal_iff ha).1 this

lemma WeakKernel.integral_col (h : WeakKernel μ a q) (y : Torus d) :
    ∫ x, q x y ∂μ = rowInt q μ y := by
  unfold rowInt; simp_rw [h.symm _ y]

lemma WeakKernel.measurable_rowInt (h : WeakKernel μ a q) : Measurable (rowInt q μ) := by
  have : StronglyMeasurable (Function.uncurry q) := h.meas.stronglyMeasurable
  exact (this.integral_prod_right' (ν := μ)).measurable

end WK

lemma abs_exp_neg_sub_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-s) - Real.exp (-t)| ≤ |s - t| := by
  have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t → Real.exp (-s) - Real.exp (-t) ≤ t - s := by
    intro s t hs hst
    have h1 : Real.exp (-s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h2 : -(t - s) + 1 ≤ Real.exp (-(t - s)) := Real.add_one_le_exp _
    have h3 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h4 : 0 ≤ Real.exp (-s) := (Real.exp_pos _).le
    have : Real.exp (-s) - Real.exp (-t) = Real.exp (-s) * (1 - Real.exp (-(t - s))) := by
      rw [h3]; ring
    rw [this]
    nlinarith
  rcases le_total s t with h | h
  · have := key s t hs h
    have h5 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have := key t s ht h
    have h5 : Real.exp (-s) ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith




/-- pair sum -/
def pairSum (q : Torus d → Torus d → ℝ) (X : Config d N) : ℝ :=
  ∑ k, ∑ l ∈ Finset.univ.erase k, q (X k) (X l)

/-- part of the pair sum not involving coordinate `i` -/
def pairRest (q : Torus d → Torus d → ℝ) (i : Fin N) (x : Config d N) : ℝ :=
  ∑ k ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase k).erase i, q (x k) (x l)

lemma pairSum_update (q : Torus d → Torus d → ℝ) (hq : ∀ x y, q x y = q y x) (i : Fin N)
    (x : Config d N) (z : Torus d) :
    pairSum q (Function.update x i z)
      = 2 * ∑ l ∈ Finset.univ.erase i, q z (x l) + pairRest q i x := by
  unfold pairSum pairRest
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : ∑ l ∈ Finset.univ.erase i, q (Function.update x i z i) (Function.update x i z l)
      = ∑ l ∈ Finset.univ.erase i, q z (x l) := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Function.update_self, Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h2 : ∀ k ∈ Finset.univ.erase i,
      ∑ l ∈ Finset.univ.erase k, q (Function.update x i z k) (Function.update x i z l)
        = q (x k) z + ∑ l ∈ (Finset.univ.erase k).erase i, q (x k) (x l) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hi : i ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨hki.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase _ _ hi]
    rw [Function.update_of_ne hki, Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  have h3 : ∑ k ∈ Finset.univ.erase i, q (x k) z = ∑ l ∈ Finset.univ.erase i, q z (x l) :=
    Finset.sum_congr rfl fun k _ => hq _ _
  rw [h3]; ring


/-- one-site factor -/
def vfun (q : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (N : ℕ) (β' : ℝ) (i : Fin N)
    (x : Config d N) (z : Torus d) : ℝ :=
  Real.exp (-(β' / N) * ∑ l ∈ Finset.univ.erase i, q z (x l) + β' * rowInt q μ z)

/-- the rest in the exponent -/
def restExp (q : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (N : ℕ) (β' : ℝ) (i : Fin N)
    (x : Config d N) : ℝ :=
  -(β' / (2 * N)) * pairRest q i x + β' * ∑ k ∈ Finset.univ.erase i, rowInt q μ (x k)
    - β' * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2

lemma exponent_eq (q : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (β' : ℝ) (X : Config d N)
    (hN : 0 < N) :
    -β' * N * modulatedEnergy q X μ
      = -(β' / (2 * N)) * pairSum q X + β' * ∑ k, rowInt q μ (X k)
          - β' * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2 := by
  unfold modulatedEnergy pairSum rowInt
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma weight_update (q : Torus d → Torus d → ℝ) (hq : ∀ x y, q x y = q y x)
    (μ : Measure (Torus d)) (β' : ℝ) (i : Fin N) (x : Config d N) (z : Torus d) (hN : 0 < N) :
    pairWeight q N β' μ (Function.update x i z)
      = ENNReal.ofReal (Real.exp (restExp q μ N β' i x)) * ENNReal.ofReal (vfun q μ N β' i x z) := by
  unfold pairWeight vfun
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [exponent_eq q μ β' _ hN, pairSum_update q hq]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : (N : ℝ) ≠ 0 := by positivity
  simp only [restExp, Function.update_self]
  have h : ∑ k ∈ Finset.univ.erase i, rowInt q μ (Function.update x i z k)
      = ∑ k ∈ Finset.univ.erase i, rowInt q μ (x k) :=
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [h]
  field_simp
  ring




section TVpart

lemma integrable_of_bdd' {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {f : E → ℝ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ z, |f z| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hb z)

lemma real_withDensity_ofReal {E : Type*} [MeasurableSpace E] (μ : Measure E) {f : E → ℝ}
    (h0 : ∀ z, 0 ≤ f z)
    (hint : Integrable f μ) {S : Set E} (hS : MeasurableSet S) :
    ((μ.withDensity (fun z => ENNReal.ofReal (f z))) S).toReal = ∫ z in S, f z ∂μ := by
  rw [withDensity_apply _ hS, ← ofReal_integral_eq_lintegral_ofReal hint.restrict
    (Filter.Eventually.of_forall h0)]
  exact ENNReal.toReal_ofReal (integral_nonneg h0)

lemma tv_normalized {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {u u' : E → ℝ} (hu : Measurable u)
    (hu' : Measurable u') (h0 : ∀ z, 0 ≤ u z) (h0' : ∀ z, 0 ≤ u' z) {M m : ℝ}
    (hM : ∀ z, u z ≤ M) (hM' : ∀ z, u' z ≤ M) (hm : 0 < m) (hZ : m ≤ ∫ z, u z ∂μ)
    (hZ' : m ≤ ∫ z, u' z ∂μ) (S : Set E) :
    |(∫ z in S, u z / ∫ z, u z ∂μ ∂μ) - ∫ z in S, u' z / ∫ z, u' z ∂μ ∂μ|
      ≤ 2 / m * ∫ z, |u z - u' z| ∂μ := by
  set Z := ∫ z, u z ∂μ with hZdef
  set Z' := ∫ z, u' z ∂μ with hZ'def
  have hZp : 0 < Z := lt_of_lt_of_le hm hZ
  have hZ'p : 0 < Z' := lt_of_lt_of_le hm hZ'
  have iu : Integrable u μ := integrable_of_bdd' μ hu (M := M) fun z => by
    rw [abs_of_nonneg (h0 z)]; exact hM z
  have iu' : Integrable u' μ := integrable_of_bdd' μ hu' (M := M) fun z => by
    rw [abs_of_nonneg (h0' z)]; exact hM' z
  have idiff : Integrable (fun z => |u z - u' z|) μ := (iu.sub iu').abs
  set D := ∫ z, |u z - u' z| ∂μ with hD
  have hD0 : 0 ≤ D := integral_nonneg fun z => abs_nonneg _
  have hZZ' : |Z' - Z| ≤ D := by
    have : Z' - Z = ∫ z, (u' z - u z) ∂μ := (integral_sub iu' iu).symm
    rw [this]
    calc |∫ z, (u' z - u z) ∂μ| ≤ ∫ z, |u' z - u z| ∂μ := abs_integral_le_integral_abs
      _ = D := by simp_rw [abs_sub_comm]; rfl
  have hpt : ∀ z, |u z / Z - u' z / Z'| ≤ |u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z')) := by
    intro z
    have : u z / Z - u' z / Z' = (u z - u' z) / Z + u' z * ((Z' - Z) / (Z * Z')) := by
      field_simp; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos hZp, abs_mul, abs_of_nonneg (h0' z), abs_div, abs_of_pos (mul_pos hZp hZ'p)]
  have ig : Integrable (fun z => |u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z'))) μ :=
    (idiff.div_const Z).add (iu'.mul_const _)
  have hint : ∫ z, (|u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z'))) ∂μ = D / Z + |Z' - Z| / Z := by
    rw [integral_add (idiff.div_const Z) (iu'.mul_const _), integral_div, integral_mul_const]
    congr 1
    rw [← hZ'def]; field_simp
  have e1 : (∫ z in S, u z / Z ∂μ) - ∫ z in S, u' z / Z' ∂μ = ∫ z in S, (u z / Z - u' z / Z') ∂μ :=
    (integral_sub (iu.div_const Z).restrict (iu'.div_const Z').restrict).symm
  rw [e1]
  have step : |∫ z in S, (u z / Z - u' z / Z') ∂μ| ≤ ∫ z, (|u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z'))) ∂μ := by
    calc |∫ z in S, (u z / Z - u' z / Z') ∂μ| ≤ ∫ z in S, |u z / Z - u' z / Z'| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z in S, (|u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z'))) ∂μ :=
          integral_mono ((iu.div_const Z).sub (iu'.div_const Z')).abs.restrict ig.restrict hpt
      _ ≤ _ := setIntegral_le_integral ig (Filter.Eventually.of_forall fun z =>
            add_nonneg (div_nonneg (abs_nonneg _) hZp.le)
              (mul_nonneg (h0' z) (div_nonneg (abs_nonneg _) (mul_pos hZp hZ'p).le)))
  refine step.trans ?_
  rw [hint]
  have h1 : D / Z ≤ D / m := div_le_div_of_nonneg_left hD0 hm hZ
  have h2 : |Z' - Z| / Z ≤ D / m := by
    calc |Z' - Z| / Z ≤ D / Z := div_le_div_of_nonneg_right hZZ' hZp.le
      _ ≤ D / m := h1
  calc D / Z + |Z' - Z| / Z ≤ D / m + D / m := add_le_add h1 h2
    _ = 2 / m * D := by ring

end TVpart

section Site

set_option linter.unusedSectionVars false

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

lemma WeakKernel.measurable_vfun (h : WeakKernel μ a q) (N : ℕ) (β' : ℝ) (i : Fin N)
    (x : Config d N) : Measurable (vfun q μ N β' i x) := by
  unfold vfun
  refine Real.measurable_exp.comp ?_
  refine Measurable.add ?_ (h.measurable_rowInt.const_mul _)
  exact (Finset.measurable_sum _ fun l _ => h.measurable_right (x l)).const_mul _

lemma vfun_pos (N : ℕ) (β' : ℝ) (i : Fin N) (x : Config d N) (z : Torus d) :
    0 < vfun q μ N β' i x z := Real.exp_pos _

lemma WeakKernel.vfun_le (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β') (N : ℕ)
    (i : Fin N) (x : Config d N) (z : Torus d) :
    vfun q μ N β' i x z ≤ Real.exp (β' * a) := by
  unfold vfun
  refine Real.exp_le_exp.2 ?_
  have h1 : 0 ≤ ∑ l ∈ Finset.univ.erase i, q z (x l) :=
    Finset.sum_nonneg fun l _ => h.nonneg _ _
  have h2 : 0 ≤ β' / N := div_nonneg hβ (Nat.cast_nonneg N)
  have h3 : β' * rowInt q μ z ≤ β' * a := mul_le_mul_of_nonneg_left (h.rowInt_le ha z) hβ
  nlinarith

lemma WeakKernel.integral_vfun_ge (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (i : Fin N) (x : Config d N) :
    Real.exp (-(β' * a)) ≤ ∫ z, vfun q μ N β' i x z ∂μ := by
  set t : Torus d → ℝ := fun z =>
    -(β' / N) * ∑ l ∈ Finset.univ.erase i, q z (x l) + β' * rowInt q μ z with ht
  have hvt : ∀ z, vfun q μ N β' i x z = Real.exp (t z) := fun z => rfl
  set c0 : ℝ := -(β' * a) with hc0
  have ivf : Integrable (vfun q μ N β' i x) μ :=
    integrable_of_bdd' μ (h.measurable_vfun N β' i x) (M := Real.exp (β' * a)) fun z => by
      rw [abs_of_pos (vfun_pos N β' i x z)]; exact h.vfun_le ha hβ N i x z
  have iH : Integrable (rowInt q μ) μ :=
    integrable_of_bdd' μ h.measurable_rowInt (M := a) fun z => by
      rw [abs_of_nonneg (h.rowInt_nonneg z)]; exact h.rowInt_le ha z
  have it : Integrable t μ := by
    refine Integrable.add ?_ (iH.const_mul _)
    exact (integrable_finsetSum _ fun l _ => h.integrable_col (x l)).const_mul _
  have hpt : ∀ z, Real.exp c0 * (1 + (t z - c0)) ≤ vfun q μ N β' i x z := by
    intro z
    have := Real.add_one_le_exp (t z - c0)
    have h2 : Real.exp (t z) = Real.exp c0 * Real.exp (t z - c0) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hvt, h2]
    have := Real.exp_pos c0
    nlinarith
  have hint : ∫ z, Real.exp c0 * (1 + (t z - c0)) ∂μ ≤ ∫ z, vfun q μ N β' i x z ∂μ :=
    integral_mono ((integrable_const _).add (it.sub (integrable_const _)) |>.const_mul _) ivf hpt
  refine le_trans ?_ hint
  have e1 : ∫ z, Real.exp c0 * (1 + (t z - c0)) ∂μ = Real.exp c0 * (1 + (∫ z, t z ∂μ - c0)) := by
    rw [integral_const_mul, integral_add (f := fun _ => (1:ℝ)) (g := fun z => t z - c0)
      (integrable_const _) (it.sub (integrable_const _)),
      integral_sub (f := t) (g := fun _ => c0) it (integrable_const _)]
    simp
  rw [e1]
  have ht0 : c0 ≤ ∫ z, t z ∂μ := by
    have e2 : ∫ z, t z ∂μ = -(β' / N) * ∑ l ∈ Finset.univ.erase i, rowInt q μ (x l)
        + β' * ∫ z, rowInt q μ z ∂μ := by
      rw [ht]
      simp only
      rw [integral_add ((integrable_finsetSum _ fun l _ => h.integrable_col (x l)).const_mul _)
        (iH.const_mul _), integral_const_mul, integral_const_mul, integral_finsetSum _
        fun l _ => h.integrable_col (x l)]
      simp_rw [h.integral_col]
    rw [e2]
    have h1 : ∑ l ∈ Finset.univ.erase i, rowInt q μ (x l) ≤ N * a := by
      calc ∑ l ∈ Finset.univ.erase i, rowInt q μ (x l)
          ≤ ∑ l ∈ Finset.univ.erase i, a := Finset.sum_le_sum fun l _ => h.rowInt_le ha _
        _ = ((Finset.univ.erase i).card : ℝ) * a := by simp
        _ ≤ N * a := by
          refine mul_le_mul_of_nonneg_right ?_ ha
          rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp
    have h2 : 0 ≤ ∫ z, rowInt q μ z ∂μ := integral_nonneg fun z => h.rowInt_nonneg z
    have h3 : 0 ≤ β' / N := div_nonneg hβ (Nat.cast_nonneg N)
    have h4 : -(β' / N) * ∑ l ∈ Finset.univ.erase i, rowInt q μ (x l) ≥ -(β' / N) * (N * a) := by
      nlinarith
    have h5 : -(β' / N) * (N * a) = -(β' * a) := by
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp
    have : 0 ≤ β' * ∫ z, rowInt q μ z ∂μ := mul_nonneg hβ h2
    rw [hc0]; linarith
  have := Real.exp_pos c0
  nlinarith

end Site

section Site2

set_option linter.unusedSectionVars false

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

lemma WeakKernel.measurable_pairWeight (h : WeakKernel μ a q) (N : ℕ) (β' : ℝ) :
    Measurable (pairWeight q N β' μ) := by
  unfold pairWeight
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  unfold modulatedEnergy
  have h1 : Measurable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => by
      have := h.meas.comp (f := fun X : Config d N => (X i, X j))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact this
  have h2 : Measurable (fun X : Config d N => ∑ i, ∫ y, q (X i) y ∂μ) :=
    Finset.measurable_sum _ fun i _ => h.measurable_rowInt.comp (measurable_pi_apply i)
  exact (((h1.const_mul _).sub (h2.const_mul _)).add_const _).const_mul _

lemma WeakKernel.siteKernel_eq (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (i : Fin N) (x : Config d N) :
    External.siteKernel μ (pairWeight q N β' μ) i x
      = μ.withDensity (fun z => ENNReal.ofReal (vfun q μ N β' i x z / ∫ w, vfun q μ N β' i x w ∂μ)) := by
  rw [External.siteKernel_apply (h.measurable_pairWeight N β')]
  set V := ∫ w, vfun q μ N β' i x w ∂μ with hV
  have hVp : 0 < V := lt_of_lt_of_le (Real.exp_pos _) (h.integral_vfun_ge ha hβ hN i x)
  have ivf : Integrable (vfun q μ N β' i x) μ :=
    integrable_of_bdd' μ (h.measurable_vfun N β' i x) (M := Real.exp (β' * a)) fun z => by
      rw [abs_of_pos (vfun_pos N β' i x z)]; exact h.vfun_le ha hβ N i x z
  have hnorm : External.normalizer μ (pairWeight q N β' μ) i x
      = ENNReal.ofReal (Real.exp (restExp q μ N β' i x)) * ENNReal.ofReal V := by
    unfold External.normalizer
    simp_rw [weight_update q h.symm μ β' i x _ hN]
    have hmv : Measurable fun z => ENNReal.ofReal (vfun q μ N β' i x z) :=
      ENNReal.measurable_ofReal.comp (h.measurable_vfun N β' i x)
    rw [lintegral_const_mul _ hmv,
      ← ofReal_integral_eq_lintegral_ofReal ivf (Filter.Eventually.of_forall fun z => (vfun_pos N β' i x z).le)]
  rw [hnorm]
  congr 1
  funext z
  rw [weight_update q h.symm μ β' i x z hN]
  set c := ENNReal.ofReal (Real.exp (restExp q μ N β' i x)) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  rw [ENNReal.ofReal_div_of_pos hVp, div_eq_mul_inv]
  calc c * ENNReal.ofReal (vfun q μ N β' i x z) * (c⁻¹ * (ENNReal.ofReal V)⁻¹)
      = (c * c⁻¹) * (ENNReal.ofReal (vfun q μ N β' i x z) * (ENNReal.ofReal V)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hc0 hct, one_mul]

end Site2

section Site3

set_option linter.unusedSectionVars false

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

lemma WeakKernel.siteKernel_le (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (i : Fin N) (x : Config d N) {C : ℝ} (hC : Real.exp (2 * (β' * a)) ≤ C) :
    External.siteKernel μ (pairWeight q N β' μ) i x ≤ ENNReal.ofReal C • μ := by
  rw [h.siteKernel_eq ha hβ hN i x]
  have hVp := lt_of_lt_of_le (Real.exp_pos _) (h.integral_vfun_ge ha hβ hN i x)
  refine Measure.le_iff.2 fun S hS => ?_
  rw [withDensity_apply _ hS, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  refine lintegral_mono fun z => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) (h.integral_vfun_ge ha hβ hN i x))]
  have h1 := h.vfun_le ha hβ N i x z
  have h2 := h.integral_vfun_ge ha hβ hN i x
  have h3 : Real.exp (2 * (β' * a)) * Real.exp (-(β' * a)) = Real.exp (β' * a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (2 * (β' * a)) * Real.exp (-(β' * a)) ≤ C * ∫ w, vfun q μ N β' i x w ∂μ := by
    calc _ ≤ C * Real.exp (-(β' * a)) :=
          mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 ((Real.exp_pos _).le.trans hC)
  linarith

lemma WeakKernel.abs_vfun_sub_le (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (i j : Fin N) (hij : i ≠ j) (x y : Config d N) (hxy : ∀ k, k ≠ j → x k = y k)
    (z : Torus d) :
    |vfun q μ N β' i x z - vfun q μ N β' i y z|
      ≤ Real.exp (β' * a) * (β' / N * (q z (x j) + q z (y j))) := by
  unfold vfun
  set A : Config d N → ℝ := fun x => β' / N * ∑ l ∈ Finset.univ.erase i, q z (x l) with hA
  have hA0 : ∀ x, 0 ≤ A x := fun x => mul_nonneg (div_nonneg hβ (Nat.cast_nonneg N))
    (Finset.sum_nonneg fun l _ => h.nonneg _ _)
  have hAx : ∀ x : Config d N, -(β' / N) * ∑ l ∈ Finset.univ.erase i, q z (x l)
      + β' * rowInt q μ z = -A x + β' * rowInt q μ z := fun x => by simp only [hA]; ring
  simp_rw [hAx]
  have e : ∀ x : Config d N, Real.exp (-A x + β' * rowInt q μ z)
      = Real.exp (-A x) * Real.exp (β' * rowInt q μ z) := fun x => by rw [← Real.exp_add]
  simp_rw [e]
  rw [← sub_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hle : Real.exp (β' * rowInt q μ z) ≤ Real.exp (β' * a) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h.rowInt_le ha z) hβ)
  have hdiff : |A x - A y| ≤ β' / N * (q z (x j) + q z (y j)) := by
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩
    have hs : ∑ l ∈ Finset.univ.erase i, q z (x l) - ∑ l ∈ Finset.univ.erase i, q z (y l)
        = q z (x j) - q z (y j) := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single j]
      · intro l _ hl; rw [hxy l hl]; ring
      · intro hj'; exact absurd hj hj'
    have : A x - A y = β' / N * (q z (x j) - q z (y j)) := by
      simp only [hA]; rw [← mul_sub, hs]
    rw [this, abs_mul, abs_of_nonneg (div_nonneg hβ (Nat.cast_nonneg N))]
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hβ (Nat.cast_nonneg N))
    have := h.nonneg z (x j); have := h.nonneg z (y j)
    rw [abs_le]; constructor <;> linarith
  calc |Real.exp (-A x) - Real.exp (-A y)| * Real.exp (β' * rowInt q μ z)
      ≤ |A x - A y| * Real.exp (β' * a) :=
        mul_le_mul (abs_exp_neg_sub_le (hA0 x) (hA0 y)) hle (Real.exp_pos _).le (abs_nonneg _)
    _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le

lemma WeakKernel.siteKernel_coeff (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (i j : Fin N) (hij : i ≠ j) (x y : Config d N)
    (hxy : ∀ k, k ≠ j → x k = y k) (S : Set (Torus d)) (hS : MeasurableSet S) :
    |(External.siteKernel μ (pairWeight q N β' μ) i x).real S
        - (External.siteKernel μ (pairWeight q N β' μ) i y).real S|
      ≤ 4 * Real.exp (2 * (β' * a)) * β' * a / N := by
  have hbd : ∀ (x : Config d N) z, |vfun q μ N β' i x z| ≤ Real.exp (β' * a) := fun x z => by
    rw [abs_of_pos (vfun_pos N β' i x z)]; exact h.vfun_le ha hβ N i x z
  have ivf : ∀ x : Config d N, Integrable (vfun q μ N β' i x) μ := fun x =>
    integrable_of_bdd' μ (h.measurable_vfun N β' i x) (hbd x)
  have hVp : ∀ x : Config d N, 0 < ∫ w, vfun q μ N β' i x w ∂μ := fun x =>
    lt_of_lt_of_le (Real.exp_pos _) (h.integral_vfun_ge ha hβ hN i x)
  have hreal : ∀ x : Config d N,
      (External.siteKernel μ (pairWeight q N β' μ) i x).real S
        = ∫ z in S, vfun q μ N β' i x z / ∫ w, vfun q μ N β' i x w ∂μ ∂μ := by
    intro x
    rw [h.siteKernel_eq ha hβ hN i x, Measure.real]
    exact real_withDensity_ofReal μ (fun z => div_nonneg (vfun_pos N β' i x z).le (hVp x).le)
      ((ivf x).div_const _) hS
  rw [hreal x, hreal y]
  have htv := tv_normalized μ (h.measurable_vfun N β' i x) (h.measurable_vfun N β' i y)
    (fun z => (vfun_pos N β' i x z).le) (fun z => (vfun_pos N β' i y z).le)
    (fun z => h.vfun_le ha hβ N i x z) (fun z => h.vfun_le ha hβ N i y z) (Real.exp_pos (-(β' * a)))
    (h.integral_vfun_ge ha hβ hN i x) (h.integral_vfun_ge ha hβ hN i y) S
  refine htv.trans ?_
  -- bound the L¹ distance
  have iq : ∀ x : Config d N, Integrable (fun z => q z (x j)) μ := fun x => h.integrable_col (x j)
  have hI : ∫ z, |vfun q μ N β' i x z - vfun q μ N β' i y z| ∂μ
      ≤ Real.exp (β' * a) * (β' / N * (2 * a)) := by
    calc ∫ z, |vfun q μ N β' i x z - vfun q μ N β' i y z| ∂μ
        ≤ ∫ z, Real.exp (β' * a) * (β' / N * (q z (x j) + q z (y j))) ∂μ :=
          integral_mono ((ivf x).sub (ivf y)).abs
            (((iq x).add (iq y)).const_mul _ |>.const_mul _)
            (fun z => h.abs_vfun_sub_le ha hβ i j hij x y hxy z)
      _ = Real.exp (β' * a) * (β' / N * (rowInt q μ (x j) + rowInt q μ (y j))) := by
          rw [integral_const_mul, integral_const_mul, integral_add (iq x) (iq y),
            h.integral_col, h.integral_col]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hβ (Nat.cast_nonneg N))
          have := h.rowInt_le ha (x j); have := h.rowInt_le ha (y j); linarith
  have hm : 2 / Real.exp (-(β' * a)) = 2 * Real.exp (β' * a) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  rw [hm]
  have h2 : (2 : ℝ) * Real.exp (β' * a) * (Real.exp (β' * a) * (β' / N * (2 * a)))
      = 4 * Real.exp (2 * (β' * a)) * β' * a / N := by
    have : Real.exp (2 * (β' * a)) = Real.exp (β' * a) * Real.exp (β' * a) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [← h2]
  exact mul_le_mul_of_nonneg_left hI (by positivity)

end Site3

section Wu

set_option linter.unusedSectionVars false

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

lemma siteKernel_div_const {E : Type*} [MeasurableSpace E] {n : ℕ} (μ : Measure E)
    [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞) (K : ℝ≥0∞) (hK0 : K ≠ 0) (hKt : K ≠ ⊤)
    (i : Fin n) :
    External.siteKernel μ (fun X => W X / K) i = External.siteKernel μ W i := by
  unfold External.siteKernel
  congr 1
  funext x z
  have hKi0 : K⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hKt
  have hKit : K⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hK0
  have hn : External.normalizer μ (fun X => W X / K) i x = External.normalizer μ W i x * K⁻¹ := by
    unfold External.normalizer
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const' _ _ hKit
  rw [hn]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr hKit) (Or.inr hKi0), inv_inv]
  calc W (Function.update x i z) * K⁻¹ * ((External.normalizer μ W i x)⁻¹ * K)
      = W (Function.update x i z) * (External.normalizer μ W i x)⁻¹ * (K⁻¹ * K) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hK0 hKt, mul_one]

lemma WeakKernel.pairWeight_le (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (X : Config d N) :
    pairWeight q N β' μ X ≤ ENNReal.ofReal (Real.exp (β' * N * a)) := by
  unfold pairWeight
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [exponent_eq q μ β' X hN]
  have h1 : 0 ≤ pairSum q X := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => h.nonneg _ _
  have h2 : ∑ k, rowInt q μ (X k) ≤ N * a := by
    calc ∑ k, rowInt q μ (X k) ≤ ∑ _k : Fin N, a := Finset.sum_le_sum fun k _ => h.rowInt_le ha _
      _ = N * a := by simp
  have h3 : 0 ≤ ∫ x, ∫ y, q x y ∂μ ∂μ := integral_nonneg fun x => h.rowInt_nonneg x
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : 0 ≤ β' / (2 * N) * pairSum q X := mul_nonneg (by positivity) h1
  have h5 : 0 ≤ β' * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2 := by positivity
  have h6 : β' * ∑ k, rowInt q μ (X k) ≤ β' * (N * a) := mul_le_mul_of_nonneg_left h2 hβ
  have e : β' * N * a = β' * (N * a) := by ring
  rw [e]
  have : -(β' / (2 * N)) * pairSum q X = -(β' / (2 * N) * pairSum q X) := by ring
  rw [this]
  linarith

lemma WeakKernel.partition_pos_lt (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) :
    pairPartition q N β' μ ≠ 0 ∧ pairPartition q N β' μ ≠ ⊤ := by
  have hW := h.measurable_pairWeight N β'
  constructor
  · unfold pairPartition
    intro h0
    rw [lintegral_eq_zero_iff hW] at h0
    have hne : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), False := by
      filter_upwards [h0] with X hX
      have : (0 : ℝ≥0∞) < pairWeight q N β' μ X := ENNReal.ofReal_pos.2 (Real.exp_pos _)
      exact this.ne' hX
    have := ae_iff.mp hne
    simp at this
  · unfold pairPartition
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun X => h.pairWeight_le ha hβ hN X) ?_)
    simp

lemma WeakKernel.wu_clause (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2)
    (hcoef : ∀ i j : Fin N, i ≠ j → ∀ x y : Config d N, (∀ k, k ≠ j → x k = y k) →
      ∀ S : Set (Torus d), MeasurableSet S →
        |(External.siteKernel μ (pairWeight q N β' μ) i x).real S
          - (External.siteKernel μ (pairWeight q N β' μ) i y).real S| ≤ κ / N)
    (F : Config d N → ℝ) (hF : Measurable F) :
    ProbabilityTheory.evariance F (pairGibbsLaw q N β' μ) ≤
      2 * ∑ i, ∫⁻ x, ProbabilityTheory.evariance (fun z => F (Function.update x i z))
        (External.siteKernel μ (pairWeight q N β' μ) i x) ∂(pairGibbsLaw q N β' μ : Measure (Config d N)) := by
  obtain ⟨hK0, hKt⟩ := h.partition_pos_lt ha hβ hN
  set K := pairPartition q N β' μ with hK
  set W := pairWeight q N β' μ with hWdef
  have hW : Measurable W := h.measurable_pairWeight N β'
  have hW' : Measurable (fun X => W X / K) := by
    simpa [div_eq_mul_inv] using hW.mul_const K⁻¹
  have hpos : ∀ X, 0 < W X / K := fun X =>
    ENNReal.div_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hKt
  have hbd0 : ENNReal.ofReal (Real.exp (β' * N * a)) / K ≠ ⊤ :=
    (ENNReal.div_lt_top ENNReal.ofReal_ne_top hK0).ne
  have hbd : ∀ X, W X / K ≤ ((ENNReal.ofReal (Real.exp (β' * N * a)) / K).toNNReal : ℝ≥0∞) := by
    intro X
    rw [ENNReal.coe_toNNReal hbd0]
    exact ENNReal.div_le_div_right (h.pairWeight_le ha hβ hN X) K
  have hnorm : ∫⁻ X, W X / K ∂(Measure.pi fun _ : Fin N => μ) = 1 := by
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hK0)]
    exact ENNReal.mul_inv_cancel hK0 hKt
  have := External.wu_resampling_half μ (fun X => W X / K) hW' hpos _ hbd hnorm
    (fun _ _ => κ / N) (fun _ _ => div_nonneg hκ0 (Nat.cast_nonneg N))
    (fun i j hij x y hxy S hS => by
      rw [siteKernel_div_const μ W K hK0 hKt i]
      exact hcoef i j hij x y hxy S hS)
    (fun i => (External.row_sum_le_of_uniform hN le_rfl hκ0 i).trans hκ) F hF
  simp_rw [siteKernel_div_const μ W K hK0 hKt] at this
  exact this

end Wu

section Lower

set_option linter.unusedSectionVars false

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

lemma WeakKernel.integrable_prod (h : WeakKernel μ a q) :
    Integrable (fun p : Torus d × Torus d => q p.1 p.2) (μ.prod μ) := by
  refine ⟨h.meas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ p : Torus d × Torus d, ‖q p.1 p.2‖ₑ = ENNReal.ofReal (q p.1 p.2) := fun p => by
    rw [Real.enorm_eq_ofReal (h.nonneg _ _)]
  simp_rw [this]
  have hm : Measurable fun p : Torus d × Torus d => ENNReal.ofReal (q p.1 p.2) :=
    ENNReal.measurable_ofReal.comp h.meas
  rw [lintegral_prod (fun p : Torus d × Torus d => ENNReal.ofReal (q p.1 p.2)) hm.aemeasurable]
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ ∂μ ≤ ∫⁻ _x, ENNReal.ofReal a ∂μ :=
        lintegral_mono fun x => h.row x
    _ < ⊤ := by simp

lemma WeakKernel.integrable_energy (h : WeakKernel μ a q) (N : ℕ) :
    Integrable (fun X : Config d N => modulatedEnergy q X μ) (Measure.pi fun _ : Fin N => μ) := by
  have hI := h.integrable_prod
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => q (X i) (X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => q p.1 p.2) hI
  have hconv_int : Integrable (fun x => ∫ y, q x y ∂μ) μ := hI.integral_prod_left
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, q (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, q (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  unfold modulatedEnergy
  exact ((hT1.const_mul _).sub (hT2.const_mul _)).add (integrable_const _)

lemma WeakKernel.integral_energy (h : WeakKernel μ a q) {N : ℕ} (hN : 1 ≤ N) :
    ∫ X : Config d N, modulatedEnergy q X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / (2 * N)) * ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) := by
  have hI := h.integrable_prod
  set G := ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) with hG
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => q (X i) (X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => q p.1 p.2) hI
  have hpair' : ∀ i j : Fin N, i ≠ j →
      ∫ X : Config d N, q (X i) (X j) ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i j hij => integral_pair_comp μ hij (H := fun p => q p.1 p.2) hI
  have hconv_int : Integrable (fun x => ∫ y, q x y ∂μ) μ := hI.integral_prod_left
  have hconv_mean : ∫ x, ∫ y, q x y ∂μ ∂μ = G := by
    rw [hG, integral_prod _ hI]
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, q (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have h1' : ∀ i : Fin N, ∫ X : Config d N, ∫ y, q (X i) y ∂μ ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i => by
      have := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int.aestronglyMeasurable
      exact this.trans hconv_mean
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, q (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  have E1 : ∫ X : Config d N, ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)
      ∂(Measure.pi fun _ : Fin N => μ) = (N : ℝ) * ((N : ℝ) - 1) * G := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm]
    have : ∀ i : Fin N, ∫ X : Config d N, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)
        ∂(Measure.pi fun _ : Fin N => μ) = ((N : ℝ) - 1) * G := by
      intro i
      rw [integral_finsetSum _ fun j hj => hpair i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_congr rfl fun j hj => hpair' i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hN]; simp
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have E2 : ∫ X : Config d N, ∑ i, ∫ y, q (X i) y ∂μ ∂(Measure.pi fun _ : Fin N => μ) = N * G := by
    rw [integral_finsetSum _ fun i _ => h1 i]
    simp_rw [h1']
    simp
  unfold modulatedEnergy
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, E1, E2, integral_const]
  · have hμ : (Measure.pi fun _ : Fin N => μ).real Set.univ = 1 := by simp [Measure.real]
    rw [hμ, one_smul]
    have : ∫ x, ∫ y, (fun x y => q x y) x y ∂μ ∂μ = G := hconv_mean
    rw [this]
    field_simp
    ring
  all_goals first
    | exact (hT1.const_mul _)
    | exact (hT2.const_mul _)
    | exact ((hT1.const_mul _).sub (hT2.const_mul _))
    | exact integrable_const _

lemma WeakKernel.one_le_partition (h : WeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) : 1 ≤ pairPartition q N β' μ := by
  set t : Config d N → ℝ := fun X => -β' * N * modulatedEnergy q X μ with ht
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have it : Integrable t (Measure.pi fun _ : Fin N => μ) :=
    (h.integrable_energy N).const_mul _
  have iet : Integrable (fun X => Real.exp (t X)) (Measure.pi fun _ : Fin N => μ) := by
    refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable it.1)
      (Real.exp (β' * N * a)) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have := h.pairWeight_le ha hβ hN X
    unfold pairWeight at this
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 this |> Real.exp_le_exp.1
  have hK : pairPartition q N β' μ = ENNReal.ofReal (∫ X, Real.exp (t X) ∂(Measure.pi fun _ : Fin N => μ)) := by
    unfold pairPartition pairWeight
    rw [ofReal_integral_eq_lintegral_ofReal iet (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)]
  rw [hK]
  refine ENNReal.one_le_ofReal.2 ?_
  have h1 : ∫ X, (1 + t X) ∂(Measure.pi fun _ : Fin N => μ) ≤ ∫ X, Real.exp (t X) ∂(Measure.pi fun _ : Fin N => μ) :=
    integral_mono ((integrable_const _).add it) iet fun X => by
      have := Real.add_one_le_exp (t X); linarith
  refine le_trans ?_ h1
  rw [integral_add (integrable_const _) it]
  have e : ∫ X, t X ∂(Measure.pi fun _ : Fin N => μ)
      = -β' * N * (-(1 / (2 * N)) * ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ)) := by
    rw [ht]; simp only
    rw [integral_const_mul, h.integral_energy hN]
  have hG : 0 ≤ ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) :=
    integral_nonneg fun p => h.nonneg _ _
  have e2 : -β' * N * (-(1 / (2 * N)) * ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ))
      = β' / 2 * ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) := by
    field_simp
  have : 0 ≤ β' / 2 * ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) :=
    mul_nonneg (by positivity) hG
  rw [e, e2]
  simp
  linarith

end Lower

end WeakRef


lemma deltaN_nonneg (s : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ deltaN d s N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold deltaN
  split_ifs with h1 h2
  · positivity
  · have : 0 ≤ Real.log (Real.exp 1 * N) := by
      apply Real.log_nonneg
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith [Real.exp_pos 1]
    positivity
  · positivity

end HRS

section WM_A
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {B : Type*} [Fintype B]

/-- The law of coordinate `i` of the `(n+1)`-particle pinned ensemble has density `pinWeight`. -/
theorem marginal_self_succ (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) :
    (pinnedLaw V lam (n + 1) a).map (fun y => y i) = μ.withDensity (pinWeight V lam a n) := by
  have hψ := isField_pinField V hlam a
  have hψx : ∀ x, IsField μ (pinField V lam (pinsWith a x)) V.M
      (V.M' + lam * Fintype.card (Option B) * V.γ) := fun x => isField_pinField V hlam _
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply _) hA]
  have hS : MeasurableSet ((fun y : Fin (n + 1) → E => y i) ⁻¹' A) :=
    measurable_pi_apply _ hA
  change (fieldLaw V (pinField V lam a) lam (n + 1)) _ = _
  unfold fieldLaw
  rw [withDensity_apply _ hS, ← lintegral_indicator hS, withDensity_apply _ hA]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hsymm : ∀ (x : E) (y : Fin n → E), e.symm (x, y) = insertAt i x y := fun _ _ => rfl
  set h : (Fin (n + 1) → E) → ℝ≥0∞ := fun y =>
    ((fun y : Fin (n + 1) → E => y i) ⁻¹' A).indicator
      (fieldDensity V (pinField V lam a) lam (n + 1)) y with hh
  have hhm : Measurable h :=
    (measurable_fieldDensity hψ.measurable V lam (n + 1)).indicator hS
  have step1 : ∫⁻ y, h y ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫⁻ p, h (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => h (e.symm p))
    rw [← this]
    exact lintegral_congr fun y => by rw [e.symm_apply_apply]
  rw [step1, lintegral_prod (fun p => h (e.symm p)) (hhm.comp e.symm.measurable).aemeasurable,
    ← lintegral_indicator hA]
  refine lintegral_congr fun x => ?_
  simp only [hsymm]
  by_cases hx : x ∈ A
  · have h1 : ∀ y : Fin n → E, h (insertAt i x y)
        = (ENNReal.ofReal (Real.exp (pinField V lam a x))
            * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹)
            * fieldWeight V (pinField V lam (pinsWith a x)) lam y := by
      intro y
      have hm : insertAt i x y ∈ (fun y : Fin (n + 1) → E => y i) ⁻¹' A := by simp [hx]
      simp only [hh]
      rw [Set.indicator_of_mem hm]
      unfold fieldDensity
      rw [fieldWeight_insertAt]; ring
    simp_rw [h1]
    rw [lintegral_const_mul _ (measurable_fieldWeight (hψx x).measurable V lam), Set.indicator_of_mem hx]
    unfold pinWeight fieldNorm
    ring
  · have h1 : ∀ y : Fin n → E, h (insertAt i x y) = 0 := by
      intro y
      have hm : insertAt i x y ∉ (fun y : Fin (n + 1) → E => y i) ⁻¹' A := by simp [hx]
      simp only [hh]
      rw [Set.indicator_of_notMem hm]
    simp_rw [h1]
    simp [Set.indicator_of_notMem hx]


/-- Cavity factor `G(x) = E_{cavity}[exp(-lam ∑_k q(x, y_k))]`. -/
def cavG (V : WeakPotential μ) (lam : ℝ) (a : B → E) (n : ℕ) (x : E) : ℝ :=
  ∫ y, Real.exp (-lam * ∑ k, V.q x (y k)) ∂(pinnedLaw V lam n a)

lemma fieldWeight_pin_eq (V : WeakPotential μ) (lam : ℝ) (a : B → E) (x : E) {n : ℕ}
    (y : Fin n → E) :
    fieldWeight V (pinField V lam (pinsWith a x)) lam y
      = fieldWeight V (pinField V lam a) lam y
          * ENNReal.ofReal (Real.exp (-lam * ∑ k, V.q x (y k))) := by
  unfold fieldWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp_rw [pinField_pinsWith, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h3 : ∑ k, V.q (y k) x = ∑ k, V.q x (y k) :=
    Finset.sum_congr rfl fun k _ => V.q_symm _ _
  rw [h3]; ring

lemma measurable_sumq' (V : WeakPotential μ) {n : ℕ} (x : E) :
    Measurable fun y : Fin n → E => ∑ k, V.q x (y k) := by
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (V.measurable_q.comp (measurable_const.prodMk (measurable_pi_apply k)))

lemma cavG_nonneg (V : WeakPotential μ) (lam : ℝ) (a : B → E) (n : ℕ) (x : E) :
    0 ≤ cavG V lam a n x := integral_nonneg fun _ => (Real.exp_pos _).le

lemma cavG_le_one (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) (x : E) :
    cavG V lam a n x ≤ 1 := by
  have := isProb_pinnedLaw V hlam n a
  unfold cavG
  calc ∫ y, Real.exp (-lam * ∑ k, V.q x (y k)) ∂(pinnedLaw V lam n a)
      ≤ ∫ _y, (1 : ℝ) ∂(pinnedLaw V lam n a) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
          (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
        refine Real.exp_le_one_iff.2 ?_
        have : 0 ≤ lam * ∑ k, V.q x (y k) :=
          mul_nonneg hlam (Finset.sum_nonneg fun k _ => V.q_nonneg _ _)
        linarith
    _ = 1 := by simp

lemma measurable_cavG (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) :
    Measurable (cavG V lam a n) := by
  have := isProb_pinnedLaw V hlam n a
  unfold cavG
  have hm : Measurable fun p : E × (Fin n → E) => Real.exp (-lam * ∑ k, V.q p.1 (p.2 k)) := by
    refine Real.measurable_exp.comp ((measurable_const.mul ?_))
    refine Finset.measurable_sum _ fun k _ => ?_
    exact V.measurable_q.comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

lemma fieldNorm_pin_eq (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (x : E)
    (n : ℕ) :
    fieldNorm V (pinField V lam (pinsWith a x)) lam n
      = fieldNorm V (pinField V lam a) lam n
          * ENNReal.ofReal (cavG V lam a n x) := by
  have hψ := isField_pinField V hlam a
  unfold fieldNorm
  simp_rw [fieldWeight_pin_eq]
  have hmeas : Measurable fun y : Fin n → E => ENNReal.ofReal (Real.exp (-lam * ∑ k, V.q x (y k))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sumq' V x)))
  have h1 : ∫⁻ y, fieldWeight V (pinField V lam a) lam y
        * ENNReal.ofReal (Real.exp (-lam * ∑ k, V.q x (y k))) ∂(Measure.pi fun _ : Fin n => μ)
      = fieldNorm V (pinField V lam a) lam n *
        ∫⁻ y, ENNReal.ofReal (Real.exp (-lam * ∑ k, V.q x (y k))) ∂(pinnedLaw V lam n a) := by
    change _ = _ * ∫⁻ y, _ ∂(fieldLaw V (pinField V lam a) lam n)
    unfold fieldLaw
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_fieldDensity hψ.measurable V lam n) hmeas]
    unfold fieldDensity
    have hW := measurable_fieldWeight hψ.measurable V lam (n := n)
    have e1 : ∀ y : Fin n → E, ((fun y : Fin n → E => fieldWeight V (pinField V lam a) lam y *
          (fieldNorm V (pinField V lam a) lam n)⁻¹) * fun y : Fin n → E =>
            ENNReal.ofReal (Real.exp (-lam * ∑ k, V.q x (y k)))) y
        = (fieldNorm V (pinField V lam a) lam n)⁻¹ *
          (fieldWeight V (pinField V lam a) lam y *
            ENNReal.ofReal (Real.exp (-lam * ∑ k, V.q x (y k)))) := fun y => by
      simp only [Pi.mul_apply]; ring
    rw [lintegral_congr e1]
    have hm2 : Measurable fun y : Fin n → E => fieldWeight V (pinField V lam a) lam y *
        ENNReal.ofReal (Real.exp (-lam * ∑ k, V.q x (y k))) := hW.mul hmeas
    rw [lintegral_const_mul _ hm2, ← mul_assoc,
      ENNReal.mul_inv_cancel (fieldNorm_pos hψ.measurable V lam n).ne'
        (fieldNorm_lt_top hψ hlam n).ne, one_mul]
  rw [h1]
  congr 1
  have := isProb_pinnedLaw V hlam n a
  unfold cavG
  rw [ofReal_integral_eq_lintegral_ofReal]
  · refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun y => ?_)
    · exact (Real.measurable_exp.comp (measurable_const.mul (measurable_sumq' V x))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_one_iff.2 ?_
      have : 0 ≤ lam * ∑ k, V.q x (y k) :=
        mul_nonneg hlam (Finset.sum_nonneg fun k _ => V.q_nonneg _ _)
      linarith
  · exact Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le


/-- Cavity formula: the marginal of coordinate `i` of the `(n+1)`-particle ensemble has `μ`-density
`c · exp(ψ(x)) · G(x)`, with `ψ = pinField a` and `G = cavG` the cavity Laplace functional. -/
theorem marginal_cavity (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) :
    ∃ c : ℝ, 0 < c ∧ (pinnedLaw V lam (n + 1) a).map (fun y => y i)
      = μ.withDensity (fun x => ENNReal.ofReal (c * (Real.exp (pinField V lam a x) * cavG V lam a n x))) := by
  have hψ := isField_pinField V hlam a
  have hn := fieldNorm_pos hψ.measurable V (lam := lam) (ψ := pinField V lam a) n
  have hn1 := fieldNorm_pos hψ.measurable V (lam := lam) (ψ := pinField V lam a) (n + 1)
  have hnt := fieldNorm_lt_top (V := V) hψ hlam n
  have hn1t := fieldNorm_lt_top (V := V) hψ hlam (n + 1)
  set c : ℝ≥0∞ := fieldNorm V (pinField V lam a) lam n * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹
    with hc
  have hc0 : c ≠ 0 := mul_ne_zero hn.ne' (ENNReal.inv_ne_zero.2 hn1t.ne)
  have hct : c ≠ ∞ := ENNReal.mul_ne_top hnt.ne (ENNReal.inv_ne_top.2 hn1.ne')
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, ?_⟩
  rw [marginal_self_succ V hlam a i]
  congr 1
  funext x
  unfold pinWeight
  rw [fieldNorm_pin_eq V hlam a x n, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hct, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [hc]
  ring


/-- Marginal density bound: every one-coordinate marginal of the pinned ensemble is `≤ C μ`,
`C = exp(M + M' + β γ)` (stationarity + `weak_siteKernel_le`). -/
theorem marginal_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) (i : Fin n) :
    (pinnedLaw V (β / N) n a).map (fun y => y i)
      ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) • μ := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam a
  have hP := isProb_pinnedLaw V hlam n a
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.map_apply (measurable_pi_apply _) hA]
  have hS : MeasurableSet ((fun y : Fin n → E => y i) ⁻¹' A) := measurable_pi_apply _ hA
  have hinv := invariant_density (μ := μ) (W := pinnedDensity V (β / N) n a)
    (measurable_fieldDensity hψ.measurable V _ n) (fieldDensity_pos hψ hlam n) (fieldDensity_le hψ hlam n) i
    (φ := ((fun y : Fin n → E => y i) ⁻¹' A).indicator 1) (measurable_one.indicator hS)
  rw [← pinnedLaw_eq] at hinv
  have h1 : ∀ x : Fin n → E, ∫⁻ z, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞)
      (update x i z) ∂(siteKernel μ (pinnedDensity V (β / N) n a) i x)
      = siteKernel μ (pinnedDensity V (β / N) n a) i x A := by
    intro x
    rw [← lintegral_indicator_one hA]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ A
    · simp [Set.indicator_apply, hz]
    · simp [Set.indicator_apply, hz]
  simp_rw [h1] at hinv
  calc (pinnedLaw V (β / N) n a) ((fun y : Fin n → E => y i) ⁻¹' A)
      = ∫⁻ x, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞) x
          ∂(pinnedLaw V (β / N) n a) := by rw [lintegral_indicator_one hS]
    _ = ∫⁻ x, siteKernel μ (pinnedDensity V (β / N) n a) i x A ∂(pinnedLaw V (β / N) n a) := hinv.symm
    _ ≤ ∫⁻ _x, (ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) • μ) A ∂(pinnedLaw V (β / N) n a) :=
        lintegral_mono fun x => weak_siteKernel_le V hβ hN0 hN a i x A
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]


/-- `e^{-x} ≤ e^{-m}(1-(x-m)) + (x-m)²/2` for `x, m ≥ 0`. -/
lemma exp_neg_le_quad {x m : ℝ} (hx : 0 ≤ x) (hm : 0 ≤ m) :
    Real.exp (-x) ≤ Real.exp (-m) * (1 - (x - m)) + (x - m) ^ 2 / 2 := by
  set φ : ℝ → ℝ := fun y => (y - m) ^ 2 / 2 - Real.exp (-y) + Real.exp (-m) * (1 - (y - m)) with hφ
  have hφ' : ∀ y, HasDerivAt φ ((y - m) + Real.exp (-y) - Real.exp (-m)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y - m) ^ 2 / 2) (y - m) y := by
      have := ((hasDerivAt_id y).sub_const m).pow 2
      convert this.div_const 2 using 1
      all_goals (try simp)
      all_goals (try ring)
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
      have := (hasDerivAt_id y).neg.exp
      simpa using this
    have h3 : HasDerivAt (fun y : ℝ => Real.exp (-m) * (1 - (y - m))) (-Real.exp (-m)) y := by
      have := (((hasDerivAt_id y).sub_const m).const_sub 1).const_mul (Real.exp (-m))
      simpa using this
    convert (h1.sub h2).add h3 using 1
    ring
  set ψ : ℝ → ℝ := fun y => (y - m) + Real.exp (-y) - Real.exp (-m) with hψ
  have hψ' : ∀ y, HasDerivAt ψ (1 - Real.exp (-y)) y := by
    intro y
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
      have := (hasDerivAt_id y).neg.exp
      simpa using this
    convert (((hasDerivAt_id y).sub_const m).add h2).sub_const (Real.exp (-m)) using 1
    funext z; simp [hψ]
  have hψm : ψ m = 0 := by simp [hψ]
  have hψmono : MonotoneOn ψ (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _ => (hψ' y).continuousAt.continuousWithinAt)
      (fun y _ => (hψ' y).differentiableAt.differentiableWithinAt) fun y hy => ?_
    rw [(hψ' y).deriv]
    have hy' : 0 < y := by simpa using hy
    have : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hφm : φ m = 0 := by simp [hφ]
  rcases le_total m x with h | h
  · have hmono : MonotoneOn φ (Set.Ici m) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici m) (fun y _ => (hφ' y).continuousAt.continuousWithinAt)
        (fun y _ => (hφ' y).differentiableAt.differentiableWithinAt) fun y hy => ?_
      rw [(hφ' y).deriv]
      have hy' : m < y := by simpa using hy
      have := hψmono (show (0:ℝ) ∈ Set.Ici 0 from le_refl 0 |> fun _ => by simp) (show m ∈ Set.Ici 0 from hm) hm
      have h5 := hψmono (show m ∈ Set.Ici (0:ℝ) from hm) (show y ∈ Set.Ici (0:ℝ) from le_of_lt (lt_of_le_of_lt hm hy')) hy'.le
      simp only [hψm, hψ] at h5
      linarith
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
    have e1 : φ x = (x - m) ^ 2 / 2 - Real.exp (-x) + Real.exp (-m) * (1 - (x - m)) := rfl
    linarith
  · have hanti : AntitoneOn φ (Set.Icc 0 m) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 m) (fun y _ => (hφ' y).continuousAt.continuousWithinAt)
        (fun y _ => (hφ' y).differentiableAt.differentiableWithinAt) fun y hy => ?_
      rw [(hφ' y).deriv]
      have hy' : 0 < y ∧ y < m := by simpa using hy
      have h5 := hψmono (show y ∈ Set.Ici (0:ℝ) from hy'.1.le) (show m ∈ Set.Ici (0:ℝ) from hm) hy'.2.le
      simp only [hψm, hψ] at h5
      linarith
    have := hanti (show x ∈ Set.Icc 0 m from ⟨hx, h⟩) (show m ∈ Set.Icc 0 m from ⟨hm, le_rfl⟩) h
    have e1 : φ x = (x - m) ^ 2 / 2 - Real.exp (-x) + Real.exp (-m) * (1 - (x - m)) := rfl
    linarith

lemma laplace_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) (h0 : ∀ ω, 0 ≤ X ω) {K : ℝ} (hK : ∀ ω, X ω ≤ K) :
    Real.exp (-∫ ω, X ω ∂P) ≤ ∫ ω, Real.exp (-X ω) ∂P ∧
      ∫ ω, Real.exp (-X ω) ∂P ≤ Real.exp (-∫ ω, X ω ∂P) + variance X P / 2 := by
  have hint : Integrable X P :=
    Integrable.of_bound hX.aestronglyMeasurable K (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 ω)]; exact hK ω)
  have hint2 : Integrable (fun ω => Real.exp (-X ω)) P :=
    Integrable.of_bound (Real.measurable_exp.comp hX.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by linarith [h0 ω]))
  set m := ∫ ω, X ω ∂P with hm
  have hm0 : 0 ≤ m := integral_nonneg h0
  have hlin : ∫ ω, Real.exp (-m) * (1 - (X ω - m)) ∂P = Real.exp (-m) := by
    have h1 : Integrable (fun ω => X ω - m) P := hint.sub (integrable_const m)
    rw [integral_const_mul, integral_sub (f := fun _ => (1:ℝ)) (g := fun ω => X ω - m)
      (integrable_const _) h1, integral_sub (f := X) (g := fun _ => m) hint (integrable_const _)]
    simp [hm]
  have hI : Integrable (fun ω => Real.exp (-m) * (1 - (X ω - m))) P :=
    ((integrable_const (1:ℝ)).sub (hint.sub (integrable_const m))).const_mul _
  have hvar : variance X P = ∫ ω, (X ω - m) ^ 2 ∂P := variance_eq_integral hX.aemeasurable
  have hsq : Integrable (fun ω => (X ω - m) ^ 2) P := by
    refine Integrable.of_bound ((hX.sub_const m).pow_const 2).aestronglyMeasurable (K ^ 2 + m ^ 2 + 2 * |K| * m + 1)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := h0 ω; have h2 := hK ω
    have : |X ω - m| ≤ |K| + m := by
      rw [abs_le]; constructor <;> nlinarith [le_abs_self K, neg_abs_le K]
    have h3 : (X ω - m) ^ 2 ≤ (|K| + m) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [sq_abs K, abs_nonneg K]
  constructor
  · calc Real.exp (-m) = ∫ ω, Real.exp (-m) * (1 - (X ω - m)) ∂P := hlin.symm
      _ ≤ ∫ ω, Real.exp (-X ω) ∂P := by
        refine integral_mono hI hint2 fun ω => ?_
        have := Real.add_one_le_exp (-(X ω - m))
        calc Real.exp (-m) * (1 - (X ω - m)) ≤ Real.exp (-m) * Real.exp (-(X ω - m)) :=
              mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
          _ = Real.exp (-X ω) := by rw [← Real.exp_add]; ring_nf
  · calc ∫ ω, Real.exp (-X ω) ∂P
        ≤ ∫ ω, (Real.exp (-m) * (1 - (X ω - m)) + (X ω - m) ^ 2 / 2) ∂P := by
          refine integral_mono hint2 ?_ fun ω => exp_neg_le_quad (h0 ω) hm0
          exact hI.add (hsq.div_const 2)
      _ = Real.exp (-m) + variance X P / 2 := by
          rw [integral_add hI (hsq.div_const 2), hlin, integral_div, hvar]

lemma abs_exp_neg_sub_le' {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-s) - Real.exp (-t)| ≤ |s - t| := by
  have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t → Real.exp (-s) - Real.exp (-t) ≤ t - s := by
    intro s t hs hst
    have h1 : Real.exp (-s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h2 : -(t - s) + 1 ≤ Real.exp (-(t - s)) := Real.add_one_le_exp _
    have h3 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h4 : 0 ≤ Real.exp (-s) := (Real.exp_pos _).le
    have : Real.exp (-s) - Real.exp (-t) = Real.exp (-s) * (1 - Real.exp (-(t - s))) := by
      rw [h3]; ring
    rw [this]
    nlinarith
  rcases le_total s t with h | h
  · have := key s t hs h
    have h5 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have := key t s ht h
    have h5 : Real.exp (-s) ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith

/-- Laplace residual for a sum of nonnegative integrable summands with cut level `L`. -/
lemma laplace_sum {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [Fintype ι] (u : ι → Ω → ℝ) (hm : ∀ k, Measurable (u k)) (h0 : ∀ k ω, 0 ≤ u k ω)
    (hi : ∀ k, Integrable (u k) P) {lam L : ℝ} (hlam : 0 ≤ lam) (hL : 0 ≤ L) :
    |∫ ω, Real.exp (-(lam * ∑ k, u k ω)) ∂P - Real.exp (-(lam * ∑ k, ∫ ω, u k ω ∂P))|
      ≤ 2 * (lam * ∑ k, ∫ ω, max (u k ω - L) 0 ∂P)
        + lam ^ 2 / 2 * variance (fun ω => ∑ k, min (u k ω) L) P := by
  set U : Ω → ℝ := fun ω => lam * ∑ k, u k ω with hU
  set X : Ω → ℝ := fun ω => lam * ∑ k, min (u k ω) L with hX
  set Y : Ω → ℝ := fun ω => lam * ∑ k, max (u k ω - L) 0 with hY
  have hUXY : ∀ ω, U ω = X ω + Y ω := fun ω => by
    simp only [hU, hX, hY, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases le_total (u k ω) L with h | h
    · simp [min_eq_left h, max_eq_right (by linarith : u k ω - L ≤ 0)]
    · simp [min_eq_right h, max_eq_left (by linarith : 0 ≤ u k ω - L)]
  have hmU : Measurable U := measurable_const.mul (Finset.measurable_sum _ fun k _ => hm k)
  have hmX : Measurable X :=
    measurable_const.mul (Finset.measurable_sum _ fun k _ => (hm k).min measurable_const)
  have hmY : Measurable Y :=
    measurable_const.mul (Finset.measurable_sum _ fun k _ => ((hm k).sub_const L).max measurable_const)
  have hU0 : ∀ ω, 0 ≤ U ω := fun ω =>
    mul_nonneg hlam (Finset.sum_nonneg fun k _ => h0 k ω)
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω =>
    mul_nonneg hlam (Finset.sum_nonneg fun k _ => le_min (h0 k ω) hL)
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω =>
    mul_nonneg hlam (Finset.sum_nonneg fun k _ => le_max_right _ _)
  have hXK : ∀ ω, X ω ≤ lam * (Fintype.card ι * L) := fun ω => by
    refine mul_le_mul_of_nonneg_left ?_ hlam
    calc ∑ k, min (u k ω) L ≤ ∑ _k : ι, L := Finset.sum_le_sum fun k _ => min_le_right _ _
      _ = _ := by simp
  have hiU : Integrable U P := by
    simpa [hU] using ((integrable_finset_sum _ fun k _ => hi k).const_mul lam)
  have hiX : Integrable X P :=
    Integrable.of_bound hmX.aestronglyMeasurable _ (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]; exact hXK ω)
  have hiY : Integrable Y P := by
    have : Y = fun ω => U ω - X ω := funext fun ω => by rw [hUXY ω]; ring
    rw [this]; exact hiU.sub hiX
  have hint : ∀ k, ∫ ω, u k ω ∂P = ∫ ω, u k ω ∂P := fun _ => rfl
  have hEU : ∫ ω, U ω ∂P = lam * ∑ k, ∫ ω, u k ω ∂P := by
    simp only [hU]
    rw [integral_const_mul, integral_finset_sum _ fun k _ => hi k]
  have hEUXY : ∫ ω, U ω ∂P = ∫ ω, X ω ∂P + ∫ ω, Y ω ∂P := by
    rw [← integral_add hiX hiY]
    exact integral_congr_ae (Filter.Eventually.of_forall hUXY)
  have hEY : ∫ ω, Y ω ∂P = lam * ∑ k, ∫ ω, max (u k ω - L) 0 ∂P := by
    simp only [hY]
    rw [integral_const_mul, integral_finset_sum]
    intro k _
    exact ((hi k).sub (integrable_const L)).pos_part
  have hEX0 : 0 ≤ ∫ ω, X ω ∂P := integral_nonneg hX0
  have hEY0 : 0 ≤ ∫ ω, Y ω ∂P := integral_nonneg hY0
  -- the three comparisons
  have c1 : |∫ ω, Real.exp (-U ω) ∂P - ∫ ω, Real.exp (-X ω) ∂P| ≤ ∫ ω, Y ω ∂P := by
    rw [← integral_sub]
    · refine (abs_integral_le_integral_abs).trans ?_
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hiY
        (Filter.Eventually.of_forall fun ω => ?_)
      refine (abs_exp_neg_sub_le' (hU0 ω) (hX0 ω)).trans ?_
      rw [hUXY ω, add_sub_cancel_left, abs_of_nonneg (hY0 ω)]
    · exact Integrable.of_bound (Real.measurable_exp.comp hmU.neg).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.2 (by linarith [hU0 ω]))
    · exact Integrable.of_bound (Real.measurable_exp.comp hmX.neg).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.2 (by linarith [hX0 ω]))
  obtain ⟨hl, hu⟩ := laplace_bounds P hmX hX0 hXK
  have c3 : |Real.exp (-∫ ω, X ω ∂P) - Real.exp (-∫ ω, U ω ∂P)| ≤ ∫ ω, Y ω ∂P := by
    refine (abs_exp_neg_sub_le' hEX0 (integral_nonneg hU0)).trans ?_
    rw [hEUXY, sub_add_cancel_left, abs_neg, abs_of_nonneg hEY0]
  have hvarX : variance X P = lam ^ 2 * variance (fun ω => ∑ k, min (u k ω) L) P := by
    simp only [hX]; exact variance_const_mul _ _ _
  rw [← hEU, ← hEY]
  have hvarX' : lam ^ 2 / 2 * variance (fun ω => ∑ k, min (u k ω) L) P = variance X P / 2 := by
    rw [hvarX]; ring
  rw [hvarX']
  have t1 := abs_sub_abs_le_abs_sub (∫ ω, Real.exp (-U ω) ∂P) (∫ ω, Real.exp (-X ω) ∂P)
  have := abs_add_three (∫ ω, Real.exp (-U ω) ∂P - ∫ ω, Real.exp (-X ω) ∂P)
    (∫ ω, Real.exp (-X ω) ∂P - Real.exp (-∫ ω, X ω ∂P))
    (Real.exp (-∫ ω, X ω ∂P) - Real.exp (-∫ ω, U ω ∂P))
  have e : ∫ ω, Real.exp (-U ω) ∂P - Real.exp (-∫ ω, U ω ∂P)
      = (∫ ω, Real.exp (-U ω) ∂P - ∫ ω, Real.exp (-X ω) ∂P)
        + (∫ ω, Real.exp (-X ω) ∂P - Real.exp (-∫ ω, X ω ∂P))
        + (Real.exp (-∫ ω, X ω ∂P) - Real.exp (-∫ ω, U ω ∂P)) := by ring
  rw [e]
  have h2 : |∫ ω, Real.exp (-X ω) ∂P - Real.exp (-∫ ω, X ω ∂P)| ≤ variance X P / 2 := by
    rw [abs_le]; constructor <;> linarith
  linarith


lemma integral_le_of_le_smul {ν : Measure E} {D : ℝ} (hD : 0 ≤ D) (hν : ν ≤ ENNReal.ofReal D • μ)
    {g : E → ℝ} (hg0 : ∀ z, 0 ≤ g z) (hgi : Integrable g μ) :
    Integrable g ν ∧ ∫ z, g z ∂ν ≤ D * ∫ z, g z ∂μ := by
  have h1 : Integrable g (ENNReal.ofReal D • μ) := hgi.smul_measure ENNReal.ofReal_ne_top
  refine ⟨h1.mono_measure hν, ?_⟩
  calc ∫ z, g z ∂ν ≤ ∫ z, g z ∂(ENNReal.ofReal D • μ) :=
        integral_mono_measure hν (Filter.Eventually.of_forall hg0) h1
    _ = D * ∫ z, g z ∂μ := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hD, smul_eq_mul]

lemma marginal_symm (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ} (i j : Fin n) :
    (pinnedLaw V lam n a).map (fun y => y i) = (pinnedLaw V lam n a).map (fun y => y j) := by
  rw [pinnedLaw_eq]
  exact map_eval_eq_of_symm μ _ (measurable_fieldDensity (isField_pinField (V := V) hlam a).measurable V lam n)
    (fun σ y => fieldDensity_comp_perm V _ _ σ y) i j


/-- Laplace residual of the cavity functional at a point `x` (source `N:eq:laplace-residual`):
`|G(x) - exp(-(β/N) n ∫ q(x,·) dν)| ≤ 2 lam n D ∫(q-L)_+ dμ + lam² n D ∫ min(q,L)² dμ`. -/
theorem cavG_residual (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (hn : 0 < n) (a : B → E) (hκ : weakKappa V β ≤ 1 / 2)
    (x : E) {L : ℝ} (hL : 0 ≤ L) :
    |cavG V (β / N) a n x
        - Real.exp (-((β / N) * (n * ∫ z, V.q x z
            ∂((pinnedLaw V (β / N) n a).map (fun y => y ⟨0, hn⟩)))))|
      ≤ 2 * ((β / N) * (n * (Real.exp (V.M + V.M' + β * V.γ) * ∫ z, max (V.q x z - L) 0 ∂μ)))
        + (β / N) ^ 2 / 2 * (2 * n * (Real.exp (V.M + V.M' + β * V.γ)
            * ∫ z, (min (V.q x z) L) ^ 2 ∂μ)) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hP := isProb_pinnedLaw V hlam n a
  set P := pinnedLaw V (β / N) n a with hPdef
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  set ν := P.map (fun y => y i₀) with hν
  set D := Real.exp (V.M + V.M' + β * V.γ) with hD
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  have hνP : ∀ k : Fin n, P.map (fun y => y k) = ν := fun k => marginal_symm V hlam a k i₀
  have hνle : ν ≤ ENNReal.ofReal D • μ := marginal_le V hβ hN0 hN a i₀
  have hq0 : ∀ z, 0 ≤ V.q x z := fun z => V.q_nonneg x z
  have hqm : Measurable (V.q x) := V.measurable_q.comp (measurable_const.prodMk measurable_id)
  have hqi : Integrable (V.q x) μ := V.integrable_q x
  have : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  -- the summands
  have hmeas : ∀ k : Fin n, Measurable (fun y : Fin n → E => V.q x (y k)) :=
    fun k => hqm.comp (measurable_pi_apply k)
  have hint : ∀ k : Fin n, Integrable (fun y : Fin n → E => V.q x (y k)) P := by
    intro k
    have h1 : Integrable (V.q x) ν := (integral_le_of_le_smul hD0 hνle hq0 hqi).1
    rw [← hνP k] at h1
    exact (integrable_map_measure hqm.aestronglyMeasurable (measurable_pi_apply k).aemeasurable).1 h1
  have key := laplace_sum P (fun k y => V.q x (y k)) hmeas (fun k y => hq0 _) hint hlam hL
  have hmap : ∀ (g : E → ℝ), Measurable g → ∀ k : Fin n,
      ∫ y, g (y k) ∂P = ∫ z, g z ∂ν := by
    intro g hg k
    rw [← hνP k, integral_map (measurable_pi_apply k).aemeasurable hg.aestronglyMeasurable]
  -- (i) the functional
  have e1 : cavG V (β / N) a n x = ∫ y, Real.exp (-((β / N) * ∑ k, V.q x (y k))) ∂P := by
    simp [cavG, neg_mul, hPdef]
  -- (ii) mean
  have e2 : ∑ k : Fin n, ∫ y, V.q x (y k) ∂P = n * ∫ z, V.q x z ∂ν := by
    rw [Finset.sum_congr rfl fun k _ => hmap (V.q x) hqm k]
    simp
  -- (iii) tail
  have hg1m : Measurable (fun z => max (V.q x z - L) 0) := (hqm.sub_const L).max measurable_const
  have hg1i : Integrable (fun z => max (V.q x z - L) 0) μ := by
    refine Integrable.mono' hqi hg1m.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (hq0 z)
  have e3 : ∑ k : Fin n, ∫ y, max (V.q x (y k) - L) 0 ∂P
      ≤ n * (D * ∫ z, max (V.q x z - L) 0 ∂μ) := by
    rw [Finset.sum_congr rfl fun k _ => hmap (fun z => max (V.q x z - L) 0) hg1m k]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (integral_le_of_le_smul hD0 hνle (fun z => le_max_right _ _) hg1i).2
      (Nat.cast_nonneg n)
  -- (iv) variance
  have hfm : Measurable (fun z => min (V.q x z) L) := hqm.min measurable_const
  have hfbd : ∀ z, |min (V.q x z) L| ≤ L := fun z => by
    rw [abs_of_nonneg (le_min (hq0 z) hL)]; exact min_le_right _ _
  have hf2 : MemLp (fun z => min (V.q x z) L) 2 ν :=
    MemLp.of_bound hfm.aestronglyMeasurable L (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hfbd z)
  have hvar := weak_linear_variance_real V hβ hN0 hN a hκ ν hνP (fun z => min (V.q x z) L) hfm hf2
  have hvar2 : variance (fun z => min (V.q x z) L) ν ≤ D * ∫ z, (min (V.q x z) L) ^ 2 ∂μ := by
    refine (variance_le_expectation_sq hfm.aestronglyMeasurable).trans ?_
    have hgi : Integrable (fun z => (min (V.q x z) L) ^ 2) μ :=
      Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable (L ^ 2) (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have := hfbd z
        have h0 : 0 ≤ min (V.q x z) L := le_min (hq0 z) hL
        nlinarith [min_le_right (V.q x z) L])
    have := (integral_le_of_le_smul hD0 hνle (fun z => sq_nonneg _) hgi).2
    simpa [Pi.pow_apply] using this
  rw [e1]
  rw [e2] at key
  have hvar' : variance (fun y : Fin n → E => ∑ k, min (V.q x (y k)) L) P
      ≤ 2 * n * (D * ∫ z, (min (V.q x z) L) ^ 2 ∂μ) := by
    refine hvar.trans ?_
    have h2n : (0 : ℝ) ≤ 2 * n := by positivity
    exact mul_le_mul_of_nonneg_left hvar2 h2n
  refine key.trans ?_
  have hl2 : 0 ≤ (β / N) ^ 2 / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hvar' hl2
  have h3 := mul_le_mul_of_nonneg_left e3 hlam
  linarith

end HRS.WeakRef.Abs

end WM_A

section WM_B
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- Cauchy-Schwarz for a nonnegative weight: `(∫ w g)² ≤ (∫ w) (∫ w g²)`. -/
lemma cs_weight {w g : E → ℝ} (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) (hwi : Integrable w μ)
    (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C) (hgb : ∀ z, |g z| ≤ C) :
    (∫ z, w z * g z ∂μ) ^ 2 ≤ (∫ z, w z ∂μ) * ∫ z, w z * g z ^ 2 ∂μ := by
  have i1 : Integrable (fun z => w z * g z) μ := by
    refine Integrable.mono' (hwi.const_mul C) (hw.mul hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 z), mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb z) (hw0 z)
  have i2 : Integrable (fun z => w z * g z ^ 2) μ := by
    refine Integrable.mono' (hwi.const_mul (C ^ 2)) (hw.mul (hg.pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 z), mul_comm, abs_of_nonneg (sq_nonneg _)]
    refine mul_le_mul_of_nonneg_right ?_ (hw0 z)
    calc g z ^ 2 = |g z| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hgb z) 2
  have h : ∀ t : ℝ, 0 ≤ (∫ z, w z ∂μ) * (t * t) + (-2 * ∫ z, w z * g z ∂μ) * t
      + ∫ z, w z * g z ^ 2 ∂μ := by
    intro t
    have : ∫ z, w z * (g z - t) ^ 2 ∂μ
        = (∫ z, w z ∂μ) * (t * t) + (-2 * ∫ z, w z * g z ∂μ) * t + ∫ z, w z * g z ^ 2 ∂μ := by
      have e : ∀ z, w z * (g z - t) ^ 2 = w z * g z ^ 2 + (-2 * t) * (w z * g z) + (t * t) * w z :=
        fun z => by ring
      simp_rw [e]
      have j1 : Integrable (fun z => (-2 * t) * (w z * g z)) μ := i1.const_mul _
      have j2 : Integrable (fun z => (t * t) * w z) μ := hwi.const_mul _
      have j3 : Integrable (fun z => w z * g z ^ 2 + (-2 * t) * (w z * g z)) μ := i2.add j1
      rw [integral_add j3 j2, integral_add i2 j1, integral_const_mul, integral_const_mul]
      ring
    rw [← this]
    exact integral_nonneg fun z => mul_nonneg (hw0 z) (sq_nonneg _)
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith


section Schur

variable {q : E → E → ℝ}

lemma measurable_rowInt' (hqm : Measurable (Function.uncurry q)) {h : E → ℝ} (hh : Measurable h) :
    Measurable fun x => ∫ y, q x y * h y ∂μ := by
  have : Measurable fun p : E × E => q p.1 p.2 * h p.2 :=
    (hqm.comp measurable_id).mul (hh.comp measurable_snd)
  exact (this.stronglyMeasurable.integral_prod_right').measurable

lemma integrable_q_prod (hqm : Measurable (Function.uncurry q)) (hq0 : ∀ x y, 0 ≤ q x y) {a : ℝ}
    (hrow : ∀ x, ∫ y, q x y ∂μ ≤ a) (hqi : ∀ x, Integrable (q x) μ) :
    Integrable (fun p : E × E => q p.1 p.2) (μ.prod μ) := by
  change Integrable (Function.uncurry q) (μ.prod μ)
  rw [integrable_prod_iff (hqm.aestronglyMeasurable)]
  refine ⟨Filter.Eventually.of_forall hqi, ?_⟩
  have h0 : ∀ x, ∫ y, ‖Function.uncurry q (x, y)‖ ∂μ = ∫ y, q x y ∂μ := fun x => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Function.uncurry, abs_of_nonneg (hq0 x y)]
  simp_rw [h0]
  have hm : Measurable fun x => ∫ y, q x y ∂μ := by
    simpa using measurable_rowInt' (μ := μ) hqm (h := fun _ => 1) measurable_const
  refine Integrable.mono' (integrable_const a) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => hq0 x y)]
  exact hrow x

/-- Schur test on `L²(μ)` for a symmetric nonnegative kernel with row sums `≤ a`. -/
lemma schur_sq (hqm : Measurable (Function.uncurry q)) (hq0 : ∀ x y, 0 ≤ q x y)
    (hqs : ∀ x y, q x y = q y x) {a : ℝ} (ha : 0 ≤ a) (hrow : ∀ x, ∫ y, q x y ∂μ ≤ a)
    (hqi : ∀ x, Integrable (q x) μ) {g : E → ℝ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hgb : ∀ z, |g z| ≤ C) :
    ∫ x, (∫ y, q x y * g y ∂μ) ^ 2 ∂μ ≤ a ^ 2 * ∫ y, g y ^ 2 ∂μ := by
  have hqx : ∀ x, Measurable (q x) := fun x => hqm.comp (measurable_const.prodMk measurable_id)
  have hJm : Measurable fun x => ∫ y, q x y * g y ^ 2 ∂μ :=
    measurable_rowInt' hqm (hg.pow_const 2)
  have hIm : Measurable fun x => ∫ y, q x y * g y ∂μ := measurable_rowInt' hqm hg
  have hpt : ∀ x, (∫ y, q x y * g y ∂μ) ^ 2 ≤ a * ∫ y, q x y * g y ^ 2 ∂μ := by
    intro x
    refine (cs_weight (hqx x) (hq0 x) (hqi x) hg hC hgb).trans ?_
    exact mul_le_mul_of_nonneg_right (hrow x) (integral_nonneg fun y => mul_nonneg (hq0 x y) (sq_nonneg _))
  have hprod : Integrable (fun p : E × E => q p.1 p.2 * g p.2 ^ 2) (μ.prod μ) := by
    have hi := integrable_q_prod hqm hq0 hrow hqi
    refine Integrable.mono' (hi.const_mul (C ^ 2))
      ((hqm.comp measurable_id).mul ((hg.comp measurable_snd).pow_const 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, id]
    rw [abs_mul, abs_of_nonneg (hq0 _ _), abs_of_nonneg (sq_nonneg _), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (hq0 _ _)
    calc g p.2 ^ 2 = |g p.2| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hgb _) 2
  have hJi : Integrable (fun x => ∫ y, q x y * g y ^ 2 ∂μ) μ := hprod.integral_prod_left
  have hIi : Integrable (fun x => (∫ y, q x y * g y ∂μ) ^ 2) μ := by
    refine Integrable.mono' (hJi.const_mul a) (hIm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt x
  calc ∫ x, (∫ y, q x y * g y ∂μ) ^ 2 ∂μ ≤ ∫ x, a * ∫ y, q x y * g y ^ 2 ∂μ ∂μ :=
        integral_mono hIi (hJi.const_mul a) hpt
    _ = a * ∫ y, ∫ x, q x y * g y ^ 2 ∂μ ∂μ := by
        rw [integral_const_mul, integral_integral_swap hprod]
    _ ≤ a * ∫ y, a * g y ^ 2 ∂μ := by
        refine mul_le_mul_of_nonneg_left ?_ ha
        have hgi : Integrable (fun y => a * g y ^ 2) μ :=
          Integrable.of_bound ((hg.pow_const 2).const_mul a).aestronglyMeasurable (a * C ^ 2)
            (Filter.Eventually.of_forall fun y => by
              rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha (sq_nonneg _))]
              refine mul_le_mul_of_nonneg_left ?_ ha
              calc g y ^ 2 = |g y| ^ 2 := (sq_abs _).symm
                _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hgb _) 2)
        refine integral_mono hprod.integral_prod_right hgi fun y => ?_
        have : ∫ x, q x y * g y ^ 2 ∂μ = (∫ x, q y x ∂μ) * g y ^ 2 := by
          rw [← integral_mul_const]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hqs x y])
        rw [this]
        calc (∫ x, q y x ∂μ) * g y ^ 2 ≤ a * g y ^ 2 :=
              mul_le_mul_of_nonneg_right (hrow y) (sq_nonneg _)
          _ = a * g y ^ 2 := rfl
    _ = a ^ 2 * ∫ y, g y ^ 2 ∂μ := by rw [integral_const_mul]; ring

end Schur


section Closing

lemma sq_le_two_add (a b c : ℝ) : (a - b) ^ 2 ≤ 2 * (a - c) ^ 2 + 2 * (c - b) ^ 2 := by
  nlinarith [sq_nonneg (a - c - (c - b))]

lemma sq_le_three_add (a b c d : ℝ) :
    (a - d) ^ 2 ≤ 3 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2) := by
  nlinarith [sq_nonneg (a - b - (b - c)), sq_nonneg (a - b - (c - d)), sq_nonneg (b - c - (c - d))]

lemma closing_algebra {x R P A B C εG εc κ a t : ℝ} (hx0 : 0 ≤ x) (hs2 : 214 * (κ * a) ^ 2 ≤ 1)
    (hxs : x ≤ 3 * (A + B + C)) (hA : A ≤ 25 * εG ^ 2) (hB : B ≤ 10 * P)
    (hP : P ≤ 16 / 9 * κ ^ 2 * R) (hR : R ≤ 2 * εc ^ 2 + 2 * (a ^ 2 * x))
    (hC : C ≤ (4 / 3 * t) ^ 2) (hPnn : 0 ≤ κ ^ 2) :
    x ≤ 150 * εG ^ 2 + 214 * κ ^ 2 * εc ^ 2 + 12 * t ^ 2 := by
  have hk : (κ * a) ^ 2 * x ≤ x / 214 := by
    have := mul_le_mul_of_nonneg_right hs2 hx0
    linarith
  have h1 : κ ^ 2 * R ≤ κ ^ 2 * (2 * εc ^ 2 + 2 * (a ^ 2 * x)) := mul_le_mul_of_nonneg_left hR hPnn
  have e1 : κ ^ 2 * (a ^ 2 * x) = (κ * a) ^ 2 * x := by ring
  have e2 : (4 / 3 * t) ^ 2 = 16 / 9 * t ^ 2 := by ring
  have h2 : 0 ≤ κ ^ 2 * εc ^ 2 := by positivity
  nlinarith [hxs, hA, hB, hP, h1, e1, e2, hk, h2]


lemma intg_bdd {g : E → ℝ} (hm : Measurable g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hb x)

lemma sq_integral_le' {g : E → ℝ} (hm : Measurable g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have h2 : MemLp g 2 μ := MemLp.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have h := variance_nonneg g μ
  rw [variance_eq_sub h2] at h
  simp only [Pi.pow_apply] at h
  linarith

lemma intg_sq_bdd {g : E → ℝ} (hm : Measurable g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) :
    Integrable (fun x => g x ^ 2) μ :=
  intg_bdd (hm.pow_const 2) (C := C ^ 2) fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb x) 2

/-- Normalisation is `L²`-Lipschitz on functions with values in `[3/4, 4/3]` and `[1, 4/3]`. -/
lemma ratio_sq {F F₁ : E → ℝ} (hF : Measurable F) (hF₁ : Measurable F₁)
    (hFb : ∀ x, 3 / 4 ≤ F x ∧ F x ≤ 4 / 3) (hF₁b : ∀ x, 1 ≤ F₁ x ∧ F₁ x ≤ 4 / 3) :
    ∫ x, (F x / ∫ y, F y ∂μ - F₁ x / ∫ y, F₁ y ∂μ) ^ 2 ∂μ ≤ 10 * ∫ x, (F x - F₁ x) ^ 2 ∂μ := by
  set Z := ∫ y, F y ∂μ with hZ
  set Z₁ := ∫ y, F₁ y ∂μ with hZ₁
  have hiF : Integrable F μ := intg_bdd hF (C := 4 / 3) fun x => by
    rw [abs_of_nonneg (by linarith [(hFb x).1])]; exact (hFb x).2
  have hiF₁ : Integrable F₁ μ := intg_bdd hF₁ (C := 4 / 3) fun x => by
    rw [abs_of_nonneg (by linarith [(hF₁b x).1])]; exact (hF₁b x).2
  have hZlo : 3 / 4 ≤ Z := by
    have := integral_mono (integrable_const (μ := μ) (3 / 4 : ℝ)) hiF fun x => (hFb x).1
    simpa using this
  have hZhi : Z ≤ 4 / 3 := by
    have := integral_mono hiF (integrable_const (μ := μ) (4 / 3 : ℝ)) fun x => (hFb x).2
    simpa using this
  have hZ₁lo : 1 ≤ Z₁ := by
    have := integral_mono (integrable_const (μ := μ) (1 : ℝ)) hiF₁ fun x => (hF₁b x).1
    simpa using this
  have hZ₁hi : Z₁ ≤ 4 / 3 := by
    have := integral_mono hiF₁ (integrable_const (μ := μ) (4 / 3 : ℝ)) fun x => (hF₁b x).2
    simpa using this
  have hΔ : ∀ x, |F x - F₁ x| ≤ 3 := fun x => by
    rw [abs_le]; constructor <;> linarith [hFb x, hF₁b x]
  have hmΔ : Measurable fun x => F x - F₁ x := hF.sub hF₁
  have hZdiff : (Z - Z₁) ^ 2 ≤ ∫ x, (F x - F₁ x) ^ 2 ∂μ := by
    have := sq_integral_le' (μ := μ) hmΔ hΔ
    rw [integral_sub hiF hiF₁] at this
    exact this
  have hpt : ∀ x, (F x / Z - F₁ x / Z₁) ^ 2 ≤ 32 / 9 * (F x - F₁ x) ^ 2 + 512 / 81 * (Z - Z₁) ^ 2 := by
    intro x
    have hZpos : 0 < Z := by linarith
    have hZ₁pos : 0 < Z₁ := by linarith
    have e : F x / Z - F₁ x / Z₁ = (F x - F₁ x) / Z + F₁ x * (Z₁ - Z) / (Z * Z₁) := by
      field_simp; ring
    rw [e]
    have h1 : |(F x - F₁ x) / Z| ≤ 4 / 3 * |F x - F₁ x| := by
      rw [abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
      nlinarith [abs_nonneg (F x - F₁ x)]
    have h2 : |F₁ x * (Z₁ - Z) / (Z * Z₁)| ≤ 16 / 9 * |Z - Z₁| := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hZpos hZ₁pos), abs_of_pos (by linarith [(hF₁b x).1] : 0 < F₁ x),
        abs_sub_comm Z₁ Z, div_le_iff₀ (mul_pos hZpos hZ₁pos)]
      have h3 : F₁ x ≤ 16 / 9 * (Z * Z₁) := by nlinarith [(hF₁b x).2]
      nlinarith [abs_nonneg (Z - Z₁)]
    set A1 := (F x - F₁ x) / Z with hA1
    set B1 := F₁ x * (Z₁ - Z) / (Z * Z₁) with hB1
    have h4 : (A1 + B1) ^ 2 ≤ 2 * A1 ^ 2 + 2 * B1 ^ 2 := by nlinarith [sq_nonneg (A1 - B1)]
    have h5 : A1 ^ 2 ≤ 16 / 9 * (F x - F₁ x) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow, sq_abs] at this
      linarith
    have h6 : B1 ^ 2 ≤ 256 / 81 * (Z - Z₁) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h2 2
      rw [sq_abs, mul_pow, sq_abs] at this
      linarith
    linarith
  have hbd : ∀ x, |F x / Z - F₁ x / Z₁| ≤ 3 := by
    intro x
    have hZpos : 0 < Z := by linarith
    have hZ₁pos : 0 < Z₁ := by linarith
    have a1 : 0 ≤ F x / Z := div_nonneg (by linarith [(hFb x).1]) hZpos.le
    have a2 : F x / Z ≤ 2 := by rw [div_le_iff₀ hZpos]; nlinarith [(hFb x).2]
    have b1 : 0 ≤ F₁ x / Z₁ := div_nonneg (by linarith [(hF₁b x).1]) hZ₁pos.le
    have b2 : F₁ x / Z₁ ≤ 2 := by rw [div_le_iff₀ hZ₁pos]; nlinarith [(hF₁b x).2]
    rw [abs_le]; constructor <;> linarith
  have hmeas : Measurable fun x => F x / Z - F₁ x / Z₁ := (hF.div_const _).sub (hF₁.div_const _)
  have hI1 := intg_sq_bdd (μ := μ) hmeas hbd
  have hI2 := intg_sq_bdd (μ := μ) hmΔ hΔ
  calc ∫ x, (F x / Z - F₁ x / Z₁) ^ 2 ∂μ
      ≤ ∫ x, (32 / 9 * (F x - F₁ x) ^ 2 + 512 / 81 * (Z - Z₁) ^ 2) ∂μ :=
        integral_mono hI1 ((hI2.const_mul _).add (integrable_const _)) hpt
    _ = 32 / 9 * ∫ x, (F x - F₁ x) ^ 2 ∂μ + 512 / 81 * (Z - Z₁) ^ 2 := by
        rw [integral_add (hI2.const_mul _) (integrable_const _), integral_const_mul]
        simp
    _ ≤ 10 * ∫ x, (F x - F₁ x) ^ 2 ∂μ := by nlinarith



lemma exp_le_four_thirds {t : ℝ} (ht : t ≤ 1 / 4) : Real.exp t ≤ 4 / 3 := by
  have h1 : 3 / 4 ≤ Real.exp (-(1 / 4)) := by
    have := Real.add_one_le_exp (-(1 / 4 : ℝ)); linarith
  have h2 : Real.exp (1 / 4) * Real.exp (-(1 / 4)) = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp (1 / 4) ≤ 4 / 3 := by
    have hp := Real.exp_pos (1 / 4 : ℝ)
    nlinarith
  exact (Real.exp_le_exp.2 ht).trans h3

lemma three_fourths_le_exp {t : ℝ} (ht : -(1 / 4) ≤ t) : 3 / 4 ≤ Real.exp t := by
  have h1 : 3 / 4 ≤ Real.exp (-(1 / 4)) := by
    have := Real.add_one_le_exp (-(1 / 4 : ℝ)); linarith
  exact h1.trans (Real.exp_le_exp.2 ht)

lemma exp_sub_one_le_mul {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4) : Real.exp t - 1 ≤ 4 / 3 * t := by
  have h1 := Real.add_one_le_exp (-t)
  have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h3 := exp_le_four_thirds ht
  have hp := Real.exp_pos t
  have : Real.exp t - 1 ≤ t * Real.exp t := by nlinarith
  nlinarith

/-- `T₁ = F₁/∫F₁` is `η`-close to `1` in `L²` when `1 ≤ F₁ ≤ 1 + η`. -/
lemma ratio_one {F₁ : E → ℝ} (hF₁ : Measurable F₁) {η : ℝ} (hη : 0 ≤ η)
    (hb : ∀ x, 1 ≤ F₁ x ∧ F₁ x ≤ 1 + η) :
    ∫ x, (F₁ x / ∫ y, F₁ y ∂μ - 1) ^ 2 ∂μ ≤ η ^ 2 := by
  set Z₁ := ∫ y, F₁ y ∂μ with hZ₁
  have hiF₁ : Integrable F₁ μ := intg_bdd hF₁ (C := 1 + η) fun x => by
    rw [abs_of_nonneg (by linarith [(hb x).1])]; exact (hb x).2
  have hlo : 1 ≤ Z₁ := by
    have := integral_mono (integrable_const (μ := μ) (1 : ℝ)) hiF₁ fun x => (hb x).1
    simpa using this
  have hhi : Z₁ ≤ 1 + η := by
    have := integral_mono hiF₁ (integrable_const (μ := μ) (1 + η)) fun x => (hb x).2
    simpa using this
  have hbd : ∀ x, |F₁ x / Z₁ - 1| ≤ η := by
    intro x
    have hZpos : 0 < Z₁ := by linarith
    have e : F₁ x / Z₁ - 1 = (F₁ x - Z₁) / Z₁ := by field_simp
    rw [e, abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
    have : |F₁ x - Z₁| ≤ η := by
      rw [abs_le]; constructor <;> linarith [(hb x).1, (hb x).2]
    nlinarith [abs_nonneg (F₁ x - Z₁)]
  have hpt : ∀ x, (F₁ x / Z₁ - 1) ^ 2 ≤ η ^ 2 := by
    intro x
    have := pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2
    rwa [sq_abs] at this
  calc ∫ x, (F₁ x / Z₁ - 1) ^ 2 ∂μ ≤ ∫ _x, η ^ 2 ∂μ :=
        integral_mono (intg_sq_bdd (hF₁.div_const _ |>.sub_const 1) hbd) (integrable_const _) hpt
    _ = η ^ 2 := by simp


set_option maxHeartbeats 1600000 in
/-- **Closing estimate** (source `N:eq:L2-contraction` and the conclusion of Lemma 5.6): the density
`f = c e^{κH} G` with `G` the Laplace functional `≈ e^{-κθ Hν}` is `L²(μ)`-close to `1`, once `κ a`
is small.  Here `Hν = q*ν` is the cavity field and `‖Hν - q*f‖₂ ≤ εc`. -/
theorem closing_L2 {q : E → E → ℝ} (hqm : Measurable (Function.uncurry q)) (hq0 : ∀ x y, 0 ≤ q x y)
    (hqs : ∀ x y, q x y = q y x) {a : ℝ} (ha : 0 ≤ a) (hrow : ∀ x, ∫ y, q x y ∂μ ≤ a)
    (hqi : ∀ x, Integrable (q x) μ)
    {κ θ D : ℝ} (hκ : 0 ≤ κ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hD : 1 ≤ D) (hs : κ * a * D ≤ 1 / 4)
    (hs2 : 214 * (κ * a) ^ 2 ≤ 1)
    {Hν : E → ℝ} (hHνm : Measurable Hν) (hHν0 : ∀ x, 0 ≤ Hν x) (hHνD : ∀ x, Hν x ≤ D * a)
    {G f : E → ℝ} {c : ℝ} (hc : 0 < c) (hGm : Measurable G)
    (hf : ∀ x, f x = c * (Real.exp (κ * ∫ y, q x y ∂μ) * G x))
    (hf1 : ∫ x, f x ∂μ = 1)
    {εG : ℝ} (hG1 : ∀ x, |G x - Real.exp (-(κ * θ * Hν x))| ≤ εG)
    (hG2 : ∀ x, Real.exp (-(κ * θ * Hν x)) ≤ G x)
    {εc : ℝ} (hcnv : ∫ x, (Hν x - ∫ y, q x y * f y ∂μ) ^ 2 ∂μ ≤ εc ^ 2) :
    ∫ x, (f x - 1) ^ 2 ∂μ ≤ 150 * εG ^ 2 + 214 * κ ^ 2 * εc ^ 2 + 12 * (κ * (1 - θ) * a) ^ 2 := by
  have hne : Nonempty E := Measure.nonempty_of_neZero μ
  obtain ⟨x₀⟩ := hne
  have hεG : 0 ≤ εG := (abs_nonneg _).trans (hG1 x₀)
  -- the row field
  set H : E → ℝ := fun x => ∫ y, q x y ∂μ with hH
  have hHm : Measurable H := by
    simpa [hH] using measurable_rowInt' (μ := μ) hqm (h := fun _ => 1) measurable_const
  have hH0 : ∀ x, 0 ≤ H x := fun x => integral_nonneg fun y => hq0 x y
  have hHa : ∀ x, H x ≤ a := hrow
  have hκa : κ * a ≤ 1 / 4 := by
    have : κ * a ≤ κ * a * D := by nlinarith [mul_nonneg hκ ha]
    linarith
  -- the exponential fields
  set F : E → ℝ := fun x => Real.exp (κ * H x) * Real.exp (-(κ * θ * Hν x)) with hFdef
  set F₁ : E → ℝ := fun x => Real.exp (κ * H x) * Real.exp (-(κ * θ * H x)) with hF₁def
  have hFm : Measurable F := (Real.measurable_exp.comp (hHm.const_mul κ)).mul
    (Real.measurable_exp.comp ((hHνm.const_mul (κ * θ)).neg))
  have hF₁m : Measurable F₁ := (Real.measurable_exp.comp (hHm.const_mul κ)).mul
    (Real.measurable_exp.comp ((hHm.const_mul (κ * θ)).neg))
  have hwb : ∀ x, 0 ≤ κ * θ * Hν x ∧ κ * θ * Hν x ≤ 1 / 4 := by
    intro x
    refine ⟨mul_nonneg (mul_nonneg hκ hθ0) (hHν0 x), ?_⟩
    calc κ * θ * Hν x ≤ κ * 1 * (D * a) := by
          have := hHνD x
          have h0 := hHν0 x
          gcongr
      _ = κ * a * D := by ring
      _ ≤ 1 / 4 := hs
  have hub : ∀ x, 0 ≤ κ * H x ∧ κ * H x ≤ 1 / 4 := by
    intro x
    exact ⟨mul_nonneg hκ (hH0 x), (mul_le_mul_of_nonneg_left (hHa x) hκ).trans hκa⟩
  have hFb : ∀ x, 3 / 4 ≤ F x ∧ F x ≤ 4 / 3 := by
    intro x
    have e : F x = Real.exp (κ * H x - κ * θ * Hν x) := by
      simp only [hFdef]; rw [← Real.exp_add]; ring_nf
    rw [e]
    constructor
    · exact three_fourths_le_exp (by linarith [(hub x).1, (hwb x).2])
    · exact exp_le_four_thirds (by linarith [(hub x).2, (hwb x).1])
  have hF₁b : ∀ x, 1 ≤ F₁ x ∧ F₁ x ≤ 1 + 4 / 3 * (κ * (1 - θ) * a) := by
    intro x
    have e : F₁ x = Real.exp (κ * (1 - θ) * H x) := by
      simp only [hF₁def]; rw [← Real.exp_add]; ring_nf
    rw [e]
    have h0 : 0 ≤ κ * (1 - θ) * H x := mul_nonneg (mul_nonneg hκ (by linarith)) (hH0 x)
    have h1 : κ * (1 - θ) * H x ≤ κ * (1 - θ) * a :=
      mul_le_mul_of_nonneg_left (hHa x) (mul_nonneg hκ (by linarith))
    have h2 : κ * (1 - θ) * a ≤ 1 / 4 := by
      have : κ * (1 - θ) * a ≤ κ * 1 * a := by gcongr; linarith
      linarith
    refine ⟨Real.one_le_exp h0, ?_⟩
    have := exp_sub_one_le_mul h0 (h1.trans h2)
    nlinarith [mul_nonneg (mul_nonneg hκ (by linarith : (0:ℝ) ≤ 1 - θ)) ha]
  -- bounds on G and f
  have hGb : ∀ x, 0 ≤ G x ∧ G x ≤ 1 + εG := by
    intro x
    have h1 := hG2 x
    have h2 : Real.exp (-(κ * θ * Hν x)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [(hwb x).1])
    have h3 := (abs_le.1 (hG1 x)).2
    exact ⟨(Real.exp_pos _).le.trans h1, by linarith⟩
  have hEb : ∀ x, 0 ≤ Real.exp (κ * H x) * G x ∧ Real.exp (κ * H x) * G x ≤ 4 / 3 * (1 + εG) := by
    intro x
    refine ⟨mul_nonneg (Real.exp_pos _).le (hGb x).1, ?_⟩
    exact mul_le_mul (exp_le_four_thirds (hub x).2) (hGb x).2 (hGb x).1 (by norm_num)
  have hEm : Measurable fun x => Real.exp (κ * H x) * G x :=
    (Real.measurable_exp.comp (hHm.const_mul κ)).mul hGm
  have hEi : Integrable (fun x => Real.exp (κ * H x) * G x) μ :=
    intg_bdd hEm (C := 4 / 3 * (1 + εG)) fun x => by rw [abs_of_nonneg (hEb x).1]; exact (hEb x).2
  set I := ∫ x, Real.exp (κ * H x) * G x ∂μ with hI
  have hcI : c * I = 1 := by
    rw [← hf1, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hf x).symm)
  have hiF : Integrable F μ := intg_bdd hFm (C := 4 / 3) fun x => by
    rw [abs_of_nonneg (by linarith [(hFb x).1])]; exact (hFb x).2
  set Z := ∫ x, F x ∂μ with hZ
  have hZlo : 3 / 4 ≤ Z := by
    have := integral_mono (integrable_const (μ := μ) (3 / 4 : ℝ)) hiF fun x => (hFb x).1
    simpa using this
  have hZhi : Z ≤ 4 / 3 := by
    have := integral_mono hiF (integrable_const (μ := μ) (4 / 3 : ℝ)) fun x => (hFb x).2
    simpa using this
  have hFle : ∀ x, F x ≤ Real.exp (κ * H x) * G x := fun x =>
    mul_le_mul_of_nonneg_left (hG2 x) (Real.exp_pos _).le
  have hZI : Z ≤ I := integral_mono hiF hEi hFle
  have hc43 : c ≤ 4 / 3 := by nlinarith
  have hIZ : |I - Z| ≤ 4 / 3 * εG := by
    have e : I - Z = ∫ x, Real.exp (κ * H x) * (G x - Real.exp (-(κ * θ * Hν x))) ∂μ := by
      rw [hI, hZ, ← integral_sub hEi hiF]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hFdef]; ring
    rw [e]
    have hb : ∀ x, ‖Real.exp (κ * H x) * (G x - Real.exp (-(κ * θ * Hν x)))‖ ≤ 4 / 3 * εG := by
      intro x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (exp_le_four_thirds (hub x).2) (hG1 x) (abs_nonneg _) (by norm_num)
    have := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
    simpa using this
  have hcZ : |1 - c * Z| ≤ 16 / 9 * εG := by
    have : 1 - c * Z = c * (I - Z) := by rw [mul_sub, hcI]
    rw [this, abs_mul, abs_of_pos hc]
    calc c * |I - Z| ≤ 4 / 3 * (4 / 3 * εG) := mul_le_mul hc43 hIZ (abs_nonneg _) (by norm_num)
      _ = 16 / 9 * εG := by ring
  have hfT : ∀ x, |f x - F x / Z| ≤ 5 * εG := by
    intro x
    have hZpos : 0 < Z := by linarith
    have e : f x - F x / Z = c * Real.exp (κ * H x) * (G x - Real.exp (-(κ * θ * Hν x)))
        + F x * (c * Z - 1) / Z := by
      rw [hf x]; simp only [hFdef]; field_simp; ring
    rw [e]
    have h1 : |c * Real.exp (κ * H x) * (G x - Real.exp (-(κ * θ * Hν x)))| ≤ 16 / 9 * εG := by
      rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_pos (Real.exp_pos _)]
      calc c * Real.exp (κ * H x) * |G x - Real.exp (-(κ * θ * Hν x))|
          ≤ (4 / 3 * (4 / 3)) * εG := by
            refine mul_le_mul (mul_le_mul hc43 (exp_le_four_thirds (hub x).2) (Real.exp_pos _).le (by norm_num))
              (hG1 x) (abs_nonneg _) (by norm_num)
        _ = 16 / 9 * εG := by ring
    have h2 : |F x * (c * Z - 1) / Z| ≤ 256 / 81 * εG := by
      rw [abs_div, abs_mul, abs_of_pos hZpos, abs_of_pos (by linarith [(hFb x).1] : 0 < F x),
        div_le_iff₀ hZpos, abs_sub_comm]
      have h3 : |1 - c * Z| ≤ 16 / 9 * εG := hcZ
      have h4 : F x ≤ 4 / 3 := (hFb x).2
      calc F x * |1 - c * Z| ≤ 4 / 3 * (16 / 9 * εG) :=
            mul_le_mul h4 h3 (abs_nonneg _) (by norm_num)
        _ ≤ 256 / 81 * εG * Z := by nlinarith
    calc |_ + _| ≤ _ := abs_add_le _ _
      _ ≤ 16 / 9 * εG + 256 / 81 * εG := add_le_add h1 h2
      _ ≤ 5 * εG := by nlinarith
  -- measurability and boundedness of f
  have hfm : Measurable f := by
    have : f = fun x => c * (Real.exp (κ * H x) * G x) := funext hf
    rw [this]; exact hEm.const_mul c
  have hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 16 / 9 * (1 + εG) := by
    intro x
    rw [hf x]
    refine ⟨mul_nonneg hc.le (hEb x).1, ?_⟩
    calc c * (Real.exp (κ * H x) * G x) ≤ 4 / 3 * (4 / 3 * (1 + εG)) :=
          mul_le_mul hc43 (hEb x).2 (hEb x).1 (by norm_num)
      _ = 16 / 9 * (1 + εG) := by ring
  have hf1b : ∀ x, |f x - 1| ≤ 16 / 9 * (1 + εG) + 1 := fun x => by
    rw [abs_le]; constructor <;> linarith [(hfb x).1, (hfb x).2, hεG]
  -- the three pieces
  set Z₁ := ∫ x, F₁ x ∂μ with hZ₁
  set T : E → ℝ := fun x => F x / Z with hT
  set T₁ : E → ℝ := fun x => F₁ x / Z₁ with hT₁
  have hTm : Measurable T := hFm.div_const _
  have hT₁m : Measurable T₁ := hF₁m.div_const _
  have hZpos : 0 < Z := by linarith
  have hTb : ∀ x, |T x| ≤ 2 := fun x => by
    simp only [hT]
    rw [abs_of_nonneg (div_nonneg (by linarith [(hFb x).1]) hZpos.le), div_le_iff₀ hZpos]
    nlinarith [(hFb x).2]
  have hZ₁lo : 1 ≤ Z₁ := by
    have hi : Integrable F₁ μ := intg_bdd hF₁m (C := 2) fun x => by
      rw [abs_of_nonneg (by linarith [(hF₁b x).1])]
      have : 0 ≤ κ * (1 - θ) * a := mul_nonneg (mul_nonneg hκ (by linarith)) ha
      linarith [(hF₁b x).2, show 4 / 3 * (κ * (1 - θ) * a) ≤ 1 / 3 by
        have : κ * (1 - θ) * a ≤ κ * 1 * a := by gcongr; linarith
        linarith]
    have := integral_mono (integrable_const (μ := μ) (1 : ℝ)) hi fun x => (hF₁b x).1
    simpa using this
  have hZ₁pos : 0 < Z₁ := by linarith
  have hT₁b : ∀ x, |T₁ x| ≤ 2 := fun x => by
    simp only [hT₁]
    rw [abs_of_nonneg (div_nonneg (by linarith [(hF₁b x).1]) hZ₁pos.le), div_le_iff₀ hZ₁pos]
    have : 0 ≤ κ * (1 - θ) * a := mul_nonneg (mul_nonneg hκ (by linarith)) ha
    have h2 : κ * (1 - θ) * a ≤ 1 / 4 := by
      have : κ * (1 - θ) * a ≤ κ * 1 * a := by gcongr; linarith
      linarith
    nlinarith [(hF₁b x).2]
  -- (i) f vs T
  have Q1 : ∫ x, (f x - T x) ^ 2 ∂μ ≤ 25 * εG ^ 2 := by
    calc ∫ x, (f x - T x) ^ 2 ∂μ ≤ ∫ _x, 25 * εG ^ 2 ∂μ := by
          refine integral_mono (intg_sq_bdd (hfm.sub hTm) (C := 16 / 9 * (1 + εG) + 2) fun x => ?_)
            (integrable_const _) fun x => ?_
          · rw [abs_le]; constructor <;> linarith [(hfb x).1, (hfb x).2, hεG, (abs_le.1 (hTb x)).1,
              (abs_le.1 (hTb x)).2]
          · have h := pow_le_pow_left₀ (abs_nonneg _) (hfT x) 2
            rw [sq_abs, mul_pow] at h
            simp only [hT]; nlinarith
      _ = 25 * εG ^ 2 := by simp
  -- (ii) T vs T₁
  have Q2 : ∫ x, (T x - T₁ x) ^ 2 ∂μ ≤ 10 * ∫ x, (F x - F₁ x) ^ 2 ∂μ := by
    have hF₁b' : ∀ x, 1 ≤ F₁ x ∧ F₁ x ≤ 4 / 3 := by
      intro x
      refine ⟨(hF₁b x).1, ?_⟩
      have : 4 / 3 * (κ * (1 - θ) * a) ≤ 1 / 3 := by
        have : κ * (1 - θ) * a ≤ κ * 1 * a := by gcongr; linarith
        linarith
      linarith [(hF₁b x).2]
    exact ratio_sq hFm hF₁m hFb hF₁b'
  -- (iii) T₁ vs 1
  have Q3 : ∫ x, (T₁ x - 1) ^ 2 ∂μ ≤ (4 / 3 * (κ * (1 - θ) * a)) ^ 2 := by
    have hη : 0 ≤ 4 / 3 * (κ * (1 - θ) * a) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hκ (by linarith)) ha)
    exact ratio_one hF₁m hη hF₁b
  -- (iv) F vs F₁ in terms of Hν - H
  have hFF₁ : ∀ x, (F x - F₁ x) ^ 2 ≤ 16 / 9 * κ ^ 2 * (Hν x - H x) ^ 2 := by
    intro x
    have h1 : |F x - F₁ x| ≤ 4 / 3 * (κ * |Hν x - H x|) := by
      have e : F x - F₁ x = Real.exp (κ * H x) *
          (Real.exp (-(κ * θ * Hν x)) - Real.exp (-(κ * θ * H x))) := by
        simp only [hFdef, hF₁def]; ring
      rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h2 := abs_exp_neg_sub_le' (hwb x).1 (mul_nonneg (mul_nonneg hκ hθ0) (hH0 x))
      have h3 : |κ * θ * Hν x - κ * θ * H x| ≤ κ * |Hν x - H x| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg hκ hθ0)]
        exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
      exact mul_le_mul (exp_le_four_thirds (hub x).2) (h2.trans h3) (abs_nonneg _) (by norm_num)
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, mul_pow, sq_abs] at this
    calc (F x - F₁ x) ^ 2 ≤ _ := this
      _ = 16 / 9 * κ ^ 2 * (Hν x - H x) ^ 2 := by ring
  -- Schur: Hπ - H
  set Hπ : E → ℝ := fun x => ∫ y, q x y * f y ∂μ with hHπ
  have hHπm : Measurable Hπ := measurable_rowInt' hqm hfm
  have hπH : ∀ x, Hπ x - H x = ∫ y, q x y * (f y - 1) ∂μ := by
    intro x
    have h1 : Integrable (fun y => q x y * f y) μ := by
      refine Integrable.mono' ((hqi x).const_mul (16 / 9 * (1 + εG)))
        ((hqm.comp (measurable_const.prodMk measurable_id)).mul hfm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 x y), abs_of_nonneg (hfb y).1, mul_comm]
      exact mul_le_mul_of_nonneg_right (hfb y).2 (hq0 x y)
    simp only [hHπ, hH, mul_sub, mul_one]
    rw [integral_sub h1 (hqi x)]
  have hSchur : ∫ x, (Hπ x - H x) ^ 2 ∂μ ≤ a ^ 2 * ∫ y, (f y - 1) ^ 2 ∂μ := by
    simp_rw [hπH]
    exact schur_sq hqm hq0 hqs ha hrow hqi (hfm.sub_const 1) (C := 16 / 9 * (1 + εG) + 1)
      (by linarith) hf1b
  -- integrability for assembly
  have hiQ : ∀ {g : E → ℝ}, Measurable g → ∀ {C : ℝ}, (∀ x, |g x| ≤ C) → Integrable (fun x => g x ^ 2) μ :=
    fun hg _ hb => intg_sq_bdd hg hb
  have hHπb : ∀ x, 0 ≤ Hπ x ∧ Hπ x ≤ 16 / 9 * (1 + εG) * a := by
    intro x
    have h1 : Integrable (fun y => q x y * f y) μ := by
      refine Integrable.mono' ((hqi x).const_mul (16 / 9 * (1 + εG)))
        ((hqm.comp (measurable_const.prodMk measurable_id)).mul hfm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 x y), abs_of_nonneg (hfb y).1, mul_comm]
      exact mul_le_mul_of_nonneg_right (hfb y).2 (hq0 x y)
    refine ⟨integral_nonneg fun y => mul_nonneg (hq0 x y) (hfb y).1, ?_⟩
    calc Hπ x ≤ ∫ y, 16 / 9 * (1 + εG) * q x y ∂μ :=
          integral_mono h1 ((hqi x).const_mul _) fun y => by
            have := mul_le_mul_of_nonneg_left (hfb y).2 (hq0 x y)
            linarith [mul_comm (q x y) (16 / 9 * (1 + εG))]
      _ = 16 / 9 * (1 + εG) * H x := by rw [integral_const_mul]
      _ ≤ 16 / 9 * (1 + εG) * a := mul_le_mul_of_nonneg_left (hHa x) (by positivity)
  have hbd1 : ∀ x, |Hν x - Hπ x| ≤ D * a + 16 / 9 * (1 + εG) * a := by
    intro x
    rw [abs_le]; constructor <;> linarith [hHν0 x, hHνD x, (hHπb x).1, (hHπb x).2]
  have hbd2 : ∀ x, |Hπ x - H x| ≤ 16 / 9 * (1 + εG) * a + a := by
    intro x
    rw [abs_le]; constructor <;> linarith [hH0 x, hHa x, (hHπb x).1, (hHπb x).2]
  have hbd3 : ∀ x, |Hν x - H x| ≤ D * a + a := by
    intro x
    rw [abs_le]; constructor <;> linarith [hH0 x, hHa x, hHν0 x, hHνD x]
  have hI1 : Integrable (fun x => (Hν x - Hπ x) ^ 2) μ := intg_sq_bdd (hHνm.sub hHπm) hbd1
  have hI2 : Integrable (fun x => (Hπ x - H x) ^ 2) μ := intg_sq_bdd (hHπm.sub hHm) hbd2
  have hI3 : Integrable (fun x => (Hν x - H x) ^ 2) μ := intg_sq_bdd (hHνm.sub hHm) hbd3
  have hHν_H : ∫ x, (Hν x - H x) ^ 2 ∂μ ≤ 2 * εc ^ 2 + 2 * (a ^ 2 * ∫ y, (f y - 1) ^ 2 ∂μ) := by
    calc ∫ x, (Hν x - H x) ^ 2 ∂μ ≤ ∫ x, (2 * (Hν x - Hπ x) ^ 2 + 2 * (Hπ x - H x) ^ 2) ∂μ :=
          integral_mono hI3 ((hI1.const_mul 2).add (hI2.const_mul 2)) fun x =>
            sq_le_two_add (Hν x) (H x) (Hπ x)
      _ = 2 * ∫ x, (Hν x - Hπ x) ^ 2 ∂μ + 2 * ∫ x, (Hπ x - H x) ^ 2 ∂μ := by
          rw [integral_add (hI1.const_mul 2) (hI2.const_mul 2), integral_const_mul, integral_const_mul]
      _ ≤ _ := by linarith
  -- assembly
  have hiA : Integrable (fun x => (f x - T x) ^ 2) μ :=
    intg_sq_bdd (hfm.sub hTm) (C := 16 / 9 * (1 + εG) + 2) fun x => by
      rw [abs_le]; constructor <;> linarith [(hfb x).1, (hfb x).2, hεG, (abs_le.1 (hTb x)).1,
        (abs_le.1 (hTb x)).2]
  have hiB : Integrable (fun x => (T x - T₁ x) ^ 2) μ :=
    intg_sq_bdd (hTm.sub hT₁m) (C := 4) fun x => by
      rw [abs_le]; constructor <;> linarith [(abs_le.1 (hTb x)).1, (abs_le.1 (hTb x)).2,
        (abs_le.1 (hT₁b x)).1, (abs_le.1 (hT₁b x)).2]
  have hiC : Integrable (fun x => (T₁ x - 1) ^ 2) μ :=
    intg_sq_bdd (hT₁m.sub_const 1) (C := 3) fun x => by
      rw [abs_le]; constructor <;> linarith [(abs_le.1 (hT₁b x)).1, (abs_le.1 (hT₁b x)).2]
  have hiP : Integrable (fun x => (F x - F₁ x) ^ 2) μ :=
    intg_sq_bdd (hFm.sub hF₁m) (C := 3) fun x => by
      have h1 := hF₁b x
      have : 4 / 3 * (κ * (1 - θ) * a) ≤ 1 / 3 := by
        have : κ * (1 - θ) * a ≤ κ * 1 * a := by gcongr; linarith
        linarith
      rw [abs_le]; constructor <;> linarith [(hFb x).1, (hFb x).2, h1.1, h1.2]
  have hxsum : ∫ x, (f x - 1) ^ 2 ∂μ ≤ 3 * (∫ x, (f x - T x) ^ 2 ∂μ + ∫ x, (T x - T₁ x) ^ 2 ∂μ
      + ∫ x, (T₁ x - 1) ^ 2 ∂μ) := by
    have hiF1 : Integrable (fun x => (f x - 1) ^ 2) μ := intg_sq_bdd (hfm.sub_const 1) hf1b
    calc ∫ x, (f x - 1) ^ 2 ∂μ
        ≤ ∫ x, (3 * ((f x - T x) ^ 2 + (T x - T₁ x) ^ 2 + (T₁ x - 1) ^ 2)) ∂μ :=
          integral_mono hiF1 (((hiA.add hiB).add hiC).const_mul 3) fun x =>
            sq_le_three_add (f x) (T x) (T₁ x) 1
      _ = _ := by
          have hs1 : Integrable (fun x => (f x - T x) ^ 2 + (T x - T₁ x) ^ 2) μ := hiA.add hiB
          rw [integral_const_mul, integral_add hs1 hiC, integral_add hiA hiB]
  have hP : ∫ x, (F x - F₁ x) ^ 2 ∂μ ≤ 16 / 9 * κ ^ 2 * ∫ x, (Hν x - H x) ^ 2 ∂μ := by
    calc ∫ x, (F x - F₁ x) ^ 2 ∂μ ≤ ∫ x, 16 / 9 * κ ^ 2 * (Hν x - H x) ^ 2 ∂μ :=
          integral_mono hiP (hI3.const_mul _) hFF₁
      _ = _ := integral_const_mul _ _
  have hx0 : 0 ≤ ∫ x, (f x - 1) ^ 2 ∂μ := integral_nonneg fun y => sq_nonneg _
  have hHν_H' := hHν_H
  exact closing_algebra hx0 hs2 hxsum Q1 Q2 hP hHν_H' Q3 (sq_nonneg κ)

end Closing

end HRS.WeakRef.Abs

end WM_B

section WM_C
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {B : Type*} [Fintype B]

/-- Jensen: `exp(-∫X) ≤ ∫ exp(-X)` for an integrable `X`. -/
lemma jensen_exp_neg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P) (h0 : ∀ ω, 0 ≤ X ω) :
    Real.exp (-∫ ω, X ω ∂P) ≤ ∫ ω, Real.exp (-X ω) ∂P := by
  have hint2 : Integrable (fun ω => Real.exp (-X ω)) P :=
    Integrable.of_bound (Real.measurable_exp.comp hX.neg).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by linarith [h0 ω]))
  set m := ∫ ω, X ω ∂P with hm
  have hI : Integrable (fun ω => Real.exp (-m) * (1 - (X ω - m))) P :=
    ((integrable_const (1:ℝ)).sub (hi.sub (integrable_const m))).const_mul _
  have hlin : ∫ ω, Real.exp (-m) * (1 - (X ω - m)) ∂P = Real.exp (-m) := by
    have h1 : Integrable (fun ω => X ω - m) P := hi.sub (integrable_const m)
    rw [integral_const_mul, integral_sub (f := fun _ => (1:ℝ)) (g := fun ω => X ω - m)
      (integrable_const _) h1, integral_sub (f := X) (g := fun _ => m) hi (integrable_const _)]
    simp [hm]
  calc Real.exp (-m) = ∫ ω, Real.exp (-m) * (1 - (X ω - m)) ∂P := hlin.symm
    _ ≤ ∫ ω, Real.exp (-X ω) ∂P := by
      refine integral_mono hI hint2 fun ω => ?_
      have := Real.add_one_le_exp (-(X ω - m))
      calc Real.exp (-m) * (1 - (X ω - m)) ≤ Real.exp (-m) * Real.exp (-(X ω - m)) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = Real.exp (-X ω) := by rw [← Real.exp_add]; ring_nf


/-- Jensen lower bound for the cavity functional. -/
theorem cavG_ge (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (hn : 0 < n) (a : B → E) (x : E) :
    Real.exp (-((β / N) * (n * ∫ z, V.q x z
        ∂((pinnedLaw V (β / N) n a).map (fun y => y ⟨0, hn⟩)))))
      ≤ cavG V (β / N) a n x := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hP := isProb_pinnedLaw V hlam n a
  set P := pinnedLaw V (β / N) n a with hPdef
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  set ν := P.map (fun y => y i₀) with hν
  set D := Real.exp (V.M + V.M' + β * V.γ) with hD
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  have hνP : ∀ k : Fin n, P.map (fun y => y k) = ν := fun k => marginal_symm V hlam a k i₀
  have hνle : ν ≤ ENNReal.ofReal D • μ := marginal_le V hβ hN0 hN a i₀
  have hq0 : ∀ z, 0 ≤ V.q x z := fun z => V.q_nonneg x z
  have hqm : Measurable (V.q x) := V.measurable_q.comp (measurable_const.prodMk measurable_id)
  have hqi : Integrable (V.q x) μ := V.integrable_q x
  have : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hmeas : ∀ k : Fin n, Measurable (fun y : Fin n → E => V.q x (y k)) :=
    fun k => hqm.comp (measurable_pi_apply k)
  have hint : ∀ k : Fin n, Integrable (fun y : Fin n → E => V.q x (y k)) P := by
    intro k
    have h1 : Integrable (V.q x) ν := (integral_le_of_le_smul hD0 hνle hq0 hqi).1
    rw [← hνP k] at h1
    exact (integrable_map_measure hqm.aestronglyMeasurable (measurable_pi_apply k).aemeasurable).1 h1
  have hmap : ∀ (g : E → ℝ), Measurable g → ∀ k : Fin n,
      ∫ y, g (y k) ∂P = ∫ z, g z ∂ν := by
    intro g hg k
    rw [← hνP k, integral_map (measurable_pi_apply k).aemeasurable hg.aestronglyMeasurable]
  have hXm : Measurable fun y : Fin n → E => (β / N) * ∑ k, V.q x (y k) :=
    measurable_const.mul (Finset.measurable_sum _ fun k _ => hmeas k)
  have hXi : Integrable (fun y : Fin n → E => (β / N) * ∑ k, V.q x (y k)) P :=
    (integrable_finset_sum _ fun k _ => hint k).const_mul _
  have hX0 : ∀ y : Fin n → E, 0 ≤ (β / N) * ∑ k, V.q x (y k) := fun y =>
    mul_nonneg hlam (Finset.sum_nonneg fun k _ => hq0 _)
  have key := jensen_exp_neg P hXm hXi hX0
  have e2 : ∫ y, (β / N) * ∑ k, V.q x (y k) ∂P = (β / N) * (n * ∫ z, V.q x z ∂ν) := by
    rw [integral_const_mul, integral_finset_sum _ fun k _ => hint k,
      Finset.sum_congr rfl fun k _ => hmap (V.q x) hqm k]
    simp
  rw [e2] at key
  have e1 : cavG V (β / N) a n x = ∫ y, Real.exp (-((β / N) * ∑ k, V.q x (y k))) ∂P := by
    simp [cavG, neg_mul, hPdef]
  rw [e1]
  exact key


lemma measurable_rowInt_meas (V : WeakPotential μ) (ν : Measure E) [IsFiniteMeasure ν] :
    Measurable fun x => ∫ y, V.q x y ∂ν := by
  have : Measurable fun p : E × E => V.q p.1 p.2 := V.measurable_q
  exact (this.stronglyMeasurable.integral_prod_right').measurable

set_option maxHeartbeats 1600000 in
/-- **Marginal bound, abstract form** (source `N:eq:weak-marginal`): assuming the kernel inputs
`hKA` (cavity cut estimate) and `hKB` (`L²` convolution estimate for two nearby marginals). -/
theorem marginal_L2 (V : WeakPotential μ) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) {n : ℕ} (hn : 0 < n)
    (hφ : ∀ x, V.φ x = κ₀ * ∫ y, V.q x y ∂μ) (hM0 : 0 ≤ V.M) (hM'0 : 0 ≤ V.M')
    (hκ : weakKappa V κ₀ ≤ 1 / 2)
    (hs : κ₀ * V.γ * Real.exp (V.M + V.M' + κ₀ * V.γ) ≤ 1 / 4)
    (hs2 : 214 * (κ₀ * V.γ) ^ 2 ≤ 1)
    {εG εc : ℝ}
    (hKA : ∀ x, 2 * ((κ₀ / ((n + 1 : ℕ) : ℝ)) * (n * (Real.exp (V.M + V.M' + κ₀ * V.γ)
          * ∫ z, max (V.q x z - ((n + 1 : ℕ) : ℝ)) 0 ∂μ)))
        + (κ₀ / ((n + 1 : ℕ) : ℝ)) ^ 2 / 2 * (2 * n * (Real.exp (V.M + V.M' + κ₀ * V.γ)
          * ∫ z, (min (V.q x z) ((n + 1 : ℕ) : ℝ)) ^ 2 ∂μ)) ≤ εG)
    (hKB : ∀ ν₁ ν₂ : Measure E, IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        ν₁ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + κ₀ * V.γ)) • μ →
        ν₂ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + κ₀ * V.γ)) • μ →
        (∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A| ≤ weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) →
        ∫ x, (∫ y, V.q x y ∂ν₁ - ∫ y, V.q x y ∂ν₂) ^ 2 ∂μ ≤ εc ^ 2) :
    ∃ f : E → ℝ≥0∞,
      (pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
          (fun y => y ⟨0, Nat.succ_pos n⟩) = μ.withDensity f ∧ Measurable f ∧
        (∃ K : ℝ, ∀ x, (f x).toReal ≤ K) ∧
        ∫ x, ((f x).toReal - 1) ^ 2 ∂μ
          ≤ 150 * εG ^ 2 + 214 * κ₀ ^ 2 * εc ^ 2 + 12 * (κ₀ * V.γ / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
  set N : ℕ := n + 1 with hN
  have hN0 : 0 < N := Nat.succ_pos n
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  set lam : ℝ := κ₀ / N with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hκ₀ hNR.le
  set a : Empty → E := fun e => e.elim with hadef
  set D : ℝ := Real.exp (V.M + V.M' + κ₀ * V.γ) with hD
  have hDge : 1 ≤ D := by
    refine Real.one_le_exp ?_
    have := V.γ_nonneg
    positivity
  have hD0 : 0 ≤ D := by linarith
  have hγ := V.γ_nonneg
  obtain ⟨c, hc0, hmarg⟩ := marginal_cavity V hlam a (n := n) ⟨0, Nat.succ_pos n⟩
  have hpin : ∀ x, pinField V lam a x = κ₀ * ∫ y, V.q x y ∂μ := by
    intro x; simp [pinField, hφ]
  set f : E → ℝ := fun x => c * (Real.exp (pinField V lam a x) * cavG V lam a n x) with hfdef
  have hGm : Measurable (cavG V lam a n) := measurable_cavG V hlam a n
  have hHm : Measurable fun x => ∫ y, V.q x y ∂μ := measurable_rowInt_meas V μ
  have hpinm : Measurable (pinField V lam a) := (isField_pinField V hlam a).measurable
  have hfm : Measurable f := by
    simp only [hfdef]
    exact ((Real.measurable_exp.comp hpinm).mul hGm).const_mul c
  have hf0 : ∀ x, 0 ≤ f x := fun x =>
    mul_nonneg hc0.le (mul_nonneg (Real.exp_pos _).le (cavG_nonneg V lam a n x))
  have hπ : (pinnedLaw V lam (n + 1) a).map (fun y => y ⟨0, Nat.succ_pos n⟩)
      = μ.withDensity (fun x => ENNReal.ofReal (f x)) := hmarg
  have hPN : IsProbabilityMeasure (pinnedLaw V lam (n + 1) a) := isProb_pinnedLaw V hlam (n + 1) a
  have hπprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
    rw [← hπ]; infer_instance
  have hlint : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = 1 := by
    have := hπprob.measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hf1 : ∫ x, f x ∂μ = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable,
      hlint]; simp
  -- the cavity marginal
  have hNcav : n + Fintype.card Empty ≤ N := by simp [hN]
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  set ν : Measure E := (pinnedLaw V lam n a).map (fun y => y i₀) with hν
  have hνprob : IsProbabilityMeasure ν := by
    have := isProb_pinnedLaw V hlam n a
    rw [hν]; infer_instance
  have hνle : ν ≤ ENNReal.ofReal D • μ := marginal_le V hκ₀ hN0 hNcav a i₀
  have hq0 : ∀ x z, 0 ≤ V.q x z := V.q_nonneg
  have hqxm : ∀ x, Measurable (V.q x) := fun x =>
    V.measurable_q.comp (measurable_const.prodMk measurable_id)
  set Hν : E → ℝ := fun x => ∫ z, V.q x z ∂ν with hHν
  have hHνm : Measurable Hν := measurable_rowInt_meas V ν
  have hHν0 : ∀ x, 0 ≤ Hν x := fun x => integral_nonneg fun z => hq0 x z
  have hHνD : ∀ x, Hν x ≤ D * V.γ := by
    intro x
    have := (integral_le_of_le_smul hD0 hνle (hq0 x) (V.integrable_q x)).2
    exact this.trans (mul_le_mul_of_nonneg_left (V.row_le x) hD0)
  -- the Laplace residual
  set θ : ℝ := (n : ℝ) / N with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hNR]; simp [hN]
  have hexp : ∀ x, lam * (n * ∫ z, V.q x z ∂ν) = κ₀ * θ * Hν x := by
    intro x; simp only [hlamdef, hθ, hHν]; ring
  have hG1 : ∀ x, |cavG V lam a n x - Real.exp (-(κ₀ * θ * Hν x))| ≤ εG := by
    intro x
    have h := cavG_residual V hκ₀ hN0 hNcav hn a hκ x (L := (N : ℝ)) hNR.le
    rw [hexp] at h
    exact h.trans (hKA x)
  have hG2 : ∀ x, Real.exp (-(κ₀ * θ * Hν x)) ≤ cavG V lam a n x := by
    intro x
    have h := cavG_ge V hκ₀ hN0 hNcav hn a x
    rw [hexp] at h
    exact h
  -- the full marginal and the comparison
  set π : Measure E := μ.withDensity (fun x => ENNReal.ofReal (f x)) with hπdef
  have hπle : π ≤ ENNReal.ofReal D • μ := by
    have h := marginal_le V hκ₀ hN0 (n := n + 1) (B := Empty) (by simp [hN]) a
      (⟨0, Nat.succ_pos n⟩ : Fin (n + 1))
    rw [hπ] at h
    exact h
  have hTV : ∀ A, MeasurableSet A → |ν.real A - π.real A| ≤ weakKappa V κ₀ / N := by
    intro A hA
    have h := rvh_pin_removed V hκ₀ hN0 (n := n) (B := Empty) (by simp [hN]) a hκ
      (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) i₀ hA
    have hsym := marginal_symm V hlam a (n := n + 1) ((⟨0, Nat.succ_pos n⟩ : Fin (n + 1)).succAbove i₀)
      ⟨0, Nat.succ_pos n⟩
    rw [hsym, hπ] at h
    rw [abs_sub_comm]
    exact h
  have hcnv0 := hKB ν π hνprob hπprob hνle hπle hTV
  have hHπ : ∀ x, ∫ y, V.q x y ∂π = ∫ y, V.q x y * f y ∂μ := by
    intro x
    rw [hπdef, integral_withDensity_eq_integral_toReal_smul (hfm.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hf0 y)]
    ring
  have hcnv : ∫ x, (Hν x - ∫ y, V.q x y * f y ∂μ) ^ 2 ∂μ ≤ εc ^ 2 := by
    simp_rw [← hHπ]
    exact hcnv0
  -- closing
  have hcl := closing_L2 (μ := μ) (q := V.q) V.measurable_q V.q_nonneg V.q_symm V.γ_nonneg V.row_le
    V.integrable_q hκ₀ hθ0 hθ1 hDge hs hs2 hHνm hHν0 hHνD hc0 hGm
    (fun x => by simp only [hfdef, hpin]) hf1 hG1 hG2 hcnv
  have hfK : ∀ x, f x ≤ c * Real.exp V.M := by
    intro x
    simp only [hfdef]
    have h1 : Real.exp (pinField V lam a x) ≤ Real.exp V.M :=
      Real.exp_le_exp.2 ((isField_pinField V hlam a).le x)
    have h2 := cavG_le_one V hlam a n x
    have h3 := cavG_nonneg V lam a n x
    calc c * (Real.exp (pinField V lam a x) * cavG V lam a n x)
        ≤ c * (Real.exp V.M * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0.le
          exact mul_le_mul h1 h2 h3 (Real.exp_pos _).le
      _ = c * Real.exp V.M := by ring
  refine ⟨fun x => ENNReal.ofReal (f x), hπ, hfm.ennreal_ofReal, ⟨c * Real.exp V.M, fun x => ?_⟩, ?_⟩
  · rw [ENNReal.toReal_ofReal (hf0 x)]; exact hfK x
  have e1 : 1 - θ = 1 / N := by
    rw [hθ]; field_simp; simp [hN]
  have e2 : κ₀ * (1 - θ) * V.γ = κ₀ * V.γ / N := by rw [e1]; ring
  rw [e2] at hcl
  simp only [ENNReal.toReal_ofReal (hf0 _)]
  exact hcl

end HRS.WeakRef.Abs

end WM_C

section WM_D
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef
open HRS.External

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ}
  {q : Torus d → Torus d → ℝ}

/-- The weak potential of a weak kernel at coupling `κ₀`: `φ = κ₀ (q*μ)`. -/
def mkV (hK : WeakKernel μ a q) (ha : 0 ≤ a) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) : WeakPotential μ where
  φ := fun x => κ₀ * rowInt q μ x
  q := q
  M := κ₀ * a
  M' := 0
  γ := a
  measurable_φ := hK.measurable_rowInt.const_mul κ₀
  measurable_q := hK.meas
  q_nonneg := hK.nonneg
  q_symm := hK.symm
  γ_nonneg := ha
  φ_le := fun x => mul_le_mul_of_nonneg_left (hK.rowInt_le ha x) hκ₀
  integrable_φ := by
    refine Integrable.of_bound (hK.measurable_rowInt.const_mul κ₀).aestronglyMeasurable (κ₀ * a)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hκ₀ (hK.rowInt_nonneg x))]
    exact mul_le_mul_of_nonneg_left (hK.rowInt_le ha x) hκ₀
  neg_le_integral_φ := by
    have : 0 ≤ ∫ x, κ₀ * rowInt q μ x ∂μ :=
      integral_nonneg fun x => mul_nonneg hκ₀ (hK.rowInt_nonneg x)
    simpa using this
  integrable_q := hK.integrable_row
  row_le := fun x => hK.rowInt_le ha x

lemma pairWeight_eq_fieldWeight (hK : WeakKernel μ a q) (ha : 0 ≤ a) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀)
    {N : ℕ} (hN : 0 < N) (X : Config d N) :
    pairWeight q N κ₀ μ X
      = ENNReal.ofReal (Real.exp (-(κ₀ * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2)))
        * fieldWeight (mkV hK ha hκ₀) (pinField (mkV hK ha hκ₀) (κ₀ / N) (fun e : Empty => e.elim))
            (κ₀ / N) X := by
  unfold pairWeight fieldWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [exponent_eq q μ κ₀ X hN]
  have hpe : pairEnergy (mkV hK ha hκ₀) X = (1 / 2) * pairSum q X := by
    simp [pairEnergy, pairSum, mkV]
  rw [hpe]
  have : (N : ℝ) ≠ 0 := by positivity
  simp only [pinField, mkV, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero, rowInt]
  simp only [← Finset.mul_sum]
  field_simp
  ring


lemma pairGibbsLaw_eq_pinnedLaw (hK : WeakKernel μ a q) (ha : 0 ≤ a) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀)
    {N : ℕ} (hN : 0 < N) :
    pairGibbsLaw q N κ₀ μ
      = pinnedLaw (mkV hK ha hκ₀) (κ₀ / N) N (fun e : Empty => e.elim) := by
  set V := mkV hK ha hκ₀ with hV
  have hlam : 0 ≤ κ₀ / N := div_nonneg hκ₀ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  set K₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(κ₀ * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2))) with hK₀
  have hK0 : K₀ ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hKt : K₀ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpw : ∀ X : Config d N, pairWeight q N κ₀ μ X
      = K₀ * fieldWeight V (pinField V (κ₀ / N) (fun e : Empty => e.elim)) (κ₀ / N) X :=
    fun X => pairWeight_eq_fieldWeight hK ha hκ₀ hN X
  have hpp : pairPartition q N κ₀ μ
      = K₀ * fieldNorm V (pinField V (κ₀ / N) (fun e : Empty => e.elim)) (κ₀ / N) N := by
    unfold pairPartition fieldNorm
    simp_rw [hpw]
    exact lintegral_const_mul _ (measurable_fieldWeight hψ.measurable V _)
  unfold pairGibbsLaw pinnedLaw fieldLaw fieldDensity
  congr 1
  funext X
  rw [hpw, hpp, ENNReal.mul_div_mul_left _ _ hK0 hKt, div_eq_mul_inv]

end HRS.WeakRef

end WM_D

section WM_E
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef
open HRS.KernelAux

variable {d : ℕ}

/-- The exponent of the pointwise envelope: `σ = s` for `s > 0` and `σ = d/4` for `s = 0`. -/
def sigmaOf (d : ℕ) (s : ℝ) : ℝ := if s = 0 then (d : ℝ) / 4 else s

lemma continuous_of_lift'' {E : Type*} [TopologicalSpace E] {f : Torus d → E}
    (h : Continuous (Torus.lift f)) : Continuous f := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) :=
    h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h2.isQuotientMap.continuous_iff.2 h

lemma exists_bound_smooth {r : Torus d → ℝ} (hr : Torus.IsSmooth r) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x, |r x| ≤ R := by
  have hc : Continuous r := continuous_of_lift'' (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨max R 0, le_max_right _ _, fun x => (hR x trivial).trans (le_max_left _ _)⟩


lemma sup_le_euc (y : Fin d → ℝ) : ‖y‖ ≤ ‖(WithLp.toLp 2 y : Euc d)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  simpa using PiLp.norm_apply_le (WithLp.toLp 2 y : Euc d) i

lemma euc_le_sup (y : Fin d → ℝ) : ‖(WithLp.toLp 2 y : Euc d)‖ ≤ Real.sqrt d * ‖y‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ i, ‖(WithLp.toLp 2 y : Euc d) i‖ ^ 2 ≤ d * ‖y‖ ^ 2 := by
    calc ∑ i, ‖(WithLp.toLp 2 y : Euc d) i‖ ^ 2 ≤ ∑ _i : Fin d, ‖y‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : ‖(WithLp.toLp 2 y : Euc d) i‖ = ‖y i‖ := rfl
          rw [this]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm y i) 2
      _ = d * ‖y‖ ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 y : Euc d) i‖ ^ 2) ≤ Real.sqrt (d * ‖y‖ ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt d * ‖y‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg _)]

/-- Pointwise envelope of the Riesz kernel (source: `w = g + c_* ≤ C(1 + |x|^{-σ})`). -/
theorem riesz_envelope (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (c : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ Box d, y ≠ 0 →
      periodicRiesz d s (boxPt y) + c ≤ B * (1 + ‖y‖ ^ (-(sigmaOf d s))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  obtain ⟨C1, C2, hC1, hC2, hbox⟩ := CoercAux.periodicRiesz_box_bound_one hd hs0 hsd
  -- local bound: `g ≤ M₁ + M₂ ‖y‖^{-σ}`
  have key : ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ ∀ y ∈ Box d, y ≠ 0 →
      periodicRiesz d s (boxPt y) ≤ M₁ + M₂ * ‖y‖ ^ (-(sigmaOf d s)) := by
    by_cases hs : s = 0
    · subst hs
      have hσ : sigmaOf d 0 = (d : ℝ) / 4 := by simp [sigmaOf]
      obtain ⟨r, δ, hδ, hr, hloc⟩ := KernelD1Aux.log_sing_d1 hd
      obtain ⟨R, hR0, hR⟩ := exists_bound_smooth hr
      set δ' := δ / Real.sqrt d with hδ'
      have hδ'0 : 0 < δ' := div_pos hδ hsqrt
      refine ⟨C1 * δ' ^ (-((0 + (d : ℝ)) / 2)) + C2 + R, 4 / d, by positivity, by positivity, ?_⟩
      intro y hy hy0
      have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
      rw [hσ]
      by_cases hsmall : ‖y‖ < δ'
      · have hx : ‖(WithLp.toLp 2 y : Euc d)‖ < δ := by
          calc ‖(WithLp.toLp 2 y : Euc d)‖ ≤ Real.sqrt d * ‖y‖ := euc_le_sup y
            _ < Real.sqrt d * δ' := mul_lt_mul_of_pos_left hsmall hsqrt
            _ = δ := by rw [hδ']; field_simp
        have hx0 : (WithLp.toLp 2 y : Euc d) ≠ 0 := by
          intro h; apply hy0
          have := congrArg (fun x : Euc d => (x : Fin d → ℝ)) h
          simpa using this
        have hmk : boxPt y = Torus.mk (WithLp.toLp 2 y : Euc d) := rfl
        rw [hmk, hloc _ hx hx0]
        have h1 : Real.log ‖y‖ ≤ Real.log ‖(WithLp.toLp 2 y : Euc d)‖ :=
          Real.log_le_log hyn (sup_le_euc y)
        have h2 : -Real.log ‖y‖ ≤ ‖y‖ ^ (-((d : ℝ) / 4)) / ((d : ℝ) / 4) := by
          have := Real.log_le_rpow_div (inv_nonneg.2 hyn.le) (show 0 < (d : ℝ) / 4 by positivity)
          rw [Real.log_inv, Real.inv_rpow hyn.le] at this
          rwa [← Real.rpow_neg hyn.le] at this
        have h3 := hR (Torus.mk (WithLp.toLp 2 y : Euc d))
        have h4 := (abs_le.1 h3).2
        have hCC : 0 ≤ C1 * δ' ^ (-((0 + (d : ℝ)) / 2)) := mul_nonneg hC1 (Real.rpow_nonneg hδ'0.le _)
        have h5 : 0 ≤ ‖y‖ ^ (-((d : ℝ) / 4)) := Real.rpow_nonneg hyn.le _
        calc -Real.log ‖(WithLp.toLp 2 y : Euc d)‖ + r (Torus.mk (WithLp.toLp 2 y : Euc d))
            ≤ ‖y‖ ^ (-((d : ℝ) / 4)) / ((d : ℝ) / 4) + R := by linarith
          _ ≤ _ := by
            have : ‖y‖ ^ (-((d : ℝ) / 4)) / ((d : ℝ) / 4) = 4 / d * ‖y‖ ^ (-((d : ℝ) / 4)) := by
              field_simp
            rw [this]; linarith
      · push_neg at hsmall
        have h1 := hbox y hy hy0
        have h2 : ‖y‖ ^ (-((0 + (d : ℝ)) / 2)) ≤ δ' ^ (-((0 + (d : ℝ)) / 2)) :=
          Real.rpow_le_rpow_of_nonpos hδ'0 hsmall (by have : (0:ℝ) ≤ (0 + (d:ℝ)) / 2 := by positivity
                                                      linarith)
        have h5 : 0 ≤ ‖y‖ ^ (-((d : ℝ) / 4)) := Real.rpow_nonneg hyn.le _
        calc periodicRiesz d 0 (boxPt y) ≤ |periodicRiesz d 0 (boxPt y)| := le_abs_self _
          _ ≤ C1 * ‖y‖ ^ (-((0 + (d : ℝ)) / 2)) + C2 := h1
          _ ≤ C1 * δ' ^ (-((0 + (d : ℝ)) / 2)) + C2 := by gcongr
          _ ≤ _ := by
            have : 0 ≤ 4 / (d : ℝ) * ‖y‖ ^ (-((d : ℝ) / 4)) := by positivity
            linarith
    · have hs0' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hσ : sigmaOf d s = s := by simp [sigmaOf, hs]
      obtain ⟨r, δ, hδ, hr, hloc⟩ := KernelD1Aux.local_sing_d1 hd hs0' hsd
      obtain ⟨R, hR0, hR⟩ := exists_bound_smooth hr
      set δ' := δ / Real.sqrt d with hδ'
      have hδ'0 : 0 < δ' := div_pos hδ hsqrt
      refine ⟨C1 * δ' ^ (-((s + (d : ℝ)) / 2)) + C2 + R, 1, by positivity, by norm_num, ?_⟩
      intro y hy hy0
      have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
      rw [hσ]
      by_cases hsmall : ‖y‖ < δ'
      · have hx : ‖(WithLp.toLp 2 y : Euc d)‖ < δ := by
          calc ‖(WithLp.toLp 2 y : Euc d)‖ ≤ Real.sqrt d * ‖y‖ := euc_le_sup y
            _ < Real.sqrt d * δ' := mul_lt_mul_of_pos_left hsmall hsqrt
            _ = δ := by rw [hδ']; field_simp
        have hx0 : (WithLp.toLp 2 y : Euc d) ≠ 0 := by
          intro h; apply hy0
          have := congrArg (fun x : Euc d => (x : Fin d → ℝ)) h
          simpa using this
        have hmk : boxPt y = Torus.mk (WithLp.toLp 2 y : Euc d) := rfl
        rw [hmk, hloc _ hx hx0]
        have h1 : ‖(WithLp.toLp 2 y : Euc d)‖ ^ (-s) ≤ ‖y‖ ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos hyn (sup_le_euc y) (by linarith)
        have h4 := (abs_le.1 (hR (Torus.mk (WithLp.toLp 2 y : Euc d)))).2
        have hCC : 0 ≤ C1 * δ' ^ (-((s + (d : ℝ)) / 2)) := mul_nonneg hC1 (Real.rpow_nonneg hδ'0.le _)
        linarith
      · push_neg at hsmall
        have h1 := hbox y hy hy0
        have h2 : ‖y‖ ^ (-((s + (d : ℝ)) / 2)) ≤ δ' ^ (-((s + (d : ℝ)) / 2)) :=
          Real.rpow_le_rpow_of_nonpos hδ'0 hsmall (by have : (0:ℝ) ≤ (s + (d:ℝ)) / 2 := by positivity
                                                      linarith)
        have h5 : 0 ≤ ‖y‖ ^ (-s) := Real.rpow_nonneg hyn.le _
        calc periodicRiesz d s (boxPt y) ≤ |periodicRiesz d s (boxPt y)| := le_abs_self _
          _ ≤ C1 * ‖y‖ ^ (-((s + (d : ℝ)) / 2)) + C2 := h1
          _ ≤ C1 * δ' ^ (-((s + (d : ℝ)) / 2)) + C2 := by gcongr
          _ ≤ _ := by linarith
  obtain ⟨M₁, M₂, hM₁, hM₂, hM⟩ := key
  refine ⟨max (max (M₁ + |c|) M₂) 1, le_max_right _ _, fun y hy hy0 => ?_⟩
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have h5 : 0 ≤ ‖y‖ ^ (-(sigmaOf d s)) := Real.rpow_nonneg hyn.le _
  have h1 := hM y hy hy0
  have hb1 : M₁ + |c| ≤ max (max (M₁ + |c|) M₂) 1 := (le_max_left _ _).trans (le_max_left _ _)
  have hb2 : M₂ ≤ max (max (M₁ + |c|) M₂) 1 := (le_max_right _ _).trans (le_max_left _ _)
  have hc := le_abs_self c
  nlinarith [mul_le_mul_of_nonneg_right hb2 h5, abs_nonneg c]

end HRS.WeakRef

end WM_E

section WM_F
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ}

/-- Polar coordinates for the sup norm on `ℝ^d`. -/
lemma polar_integral (hd : 1 ≤ d) (f : ℝ → ℝ) :
    ∫ y : Fin d → ℝ, f ‖y‖ = (d : ℝ) * 2 ^ d * ∫ t in Ioi (0 : ℝ), t ^ (d - 1) * f t := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h := integral_fun_norm_addHaar (volume : Measure (Fin d → ℝ)) f
  have hf : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  rw [hf] at h
  have hb : (volume : Measure (Fin d → ℝ)).real (Metric.ball 0 1) = 2 ^ d := by
    rw [Measure.real, Real.volume_pi_ball _ one_pos]
    simp
  rw [hb] at h
  simpa [nsmul_eq_mul, smul_eq_mul, mul_assoc] using h

lemma polar_integrable (hd : 1 ≤ d) {f : ℝ → ℝ} :
    Integrable (fun y : Fin d → ℝ => f ‖y‖) ↔
      IntegrableOn (fun t : ℝ => t ^ (d - 1) * f t) (Ioi 0) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h := integrable_fun_norm_addHaar (volume : Measure (Fin d → ℝ)) (f := f)
  have hf : Module.finrank ℝ (Fin d → ℝ) = d := by simp
  rw [hf] at h
  simpa [smul_eq_mul] using h


lemma radial_pow_mul (hd : 1 ≤ d) {α t : ℝ} (ht : 0 < t) :
    t ^ (d - 1) * t ^ (-α) = t ^ ((d : ℝ) - 1 - α) := by
  have h1 : t ^ (d - 1) = t ^ (((d - 1 : ℕ) : ℝ)) := (Real.rpow_natCast t (d - 1)).symm
  rw [h1, ← Real.rpow_add ht]
  congr 1
  rw [Nat.cast_sub hd]; push_cast; ring

/-- Annulus integral of a power of the radius. -/
lemma polar_Ico_power (hd : 1 ≤ d) {α r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∫⁻ y : Fin d → ℝ, ENNReal.ofReal ((Ico r R).indicator (fun t => t ^ (-α)) ‖y‖)
      = ENNReal.ofReal ((d : ℝ) * 2 ^ d * ∫ t in r..R, t ^ ((d : ℝ) - 1 - α)) := by
  set f : ℝ → ℝ := (Ico r R).indicator (fun t => t ^ (-α)) with hf
  have hcont : ContinuousOn (fun t : ℝ => t ^ ((d : ℝ) - 1 - α)) (Icc r R) :=
    ContinuousOn.rpow_const continuousOn_id fun t ht =>
      Or.inl (show t ≠ 0 from ne_of_gt (hr.trans_le ht.1))
  have hIco : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 1 - α)) (Ico r R) :=
    hcont.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hfun : (fun t : ℝ => t ^ (d - 1) * f t)
      = (Ico r R).indicator (fun t : ℝ => t ^ ((d : ℝ) - 1 - α)) := by
    funext t
    by_cases ht : t ∈ Ico r R
    · simp only [hf, indicator_of_mem ht]
      exact radial_pow_mul hd (hr.trans_le ht.1)
    · simp [hf, indicator_of_notMem ht]
  have hintOn : IntegrableOn (fun t : ℝ => t ^ (d - 1) * f t) (Ioi 0) := by
    rw [hfun]
    exact (integrable_indicator_iff measurableSet_Ico).2 hIco |>.integrableOn
  have hint : Integrable (fun y : Fin d → ℝ => f ‖y‖) := (polar_integrable hd).2 hintOn
  have hnn : ∀ t, 0 ≤ f t := fun t => by
    by_cases ht : t ∈ Ico r R
    · simp only [hf, indicator_of_mem ht]
      exact Real.rpow_nonneg (hr.le.trans ht.1) _
    · simp [hf, indicator_of_notMem ht]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => hnn _)]
  rw [polar_integral hd f]
  congr 2
  rw [hfun, setIntegral_indicator measurableSet_Ico]
  have : Ioi (0 : ℝ) ∩ Ico r R = Ico r R := by
    ext t; simp only [mem_inter_iff, mem_Ico, mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨hr.trans_le h.1, h⟩⟩
  rw [this, intervalIntegral.integral_of_le hrR, integral_Ioc_eq_integral_Ioo, ← integral_Ico_eq_integral_Ioo]


/-- Ball integral of a power of the radius. -/
lemma polar_Ioo_power (hd : 1 ≤ d) {α ρ : ℝ} (hρ : 0 < ρ) (hα : α < d) :
    ∫⁻ y : Fin d → ℝ, ENNReal.ofReal ((Ioo 0 ρ).indicator (fun t => t ^ (-α)) ‖y‖)
      = ENNReal.ofReal ((d : ℝ) * 2 ^ d * (ρ ^ ((d : ℝ) - α) / ((d : ℝ) - α))) := by
  set f : ℝ → ℝ := (Ioo 0 ρ).indicator (fun t => t ^ (-α)) with hf
  have he : (-1 : ℝ) < (d : ℝ) - 1 - α := by linarith
  have hIoo : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 1 - α)) (Ioo 0 ρ) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ρ) he)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hρ.le |>.1 this).mono_set Ioo_subset_Ioc_self
  have hfun : (fun t : ℝ => t ^ (d - 1) * f t)
      = (Ioo 0 ρ).indicator (fun t : ℝ => t ^ ((d : ℝ) - 1 - α)) := by
    funext t
    by_cases ht : t ∈ Ioo 0 ρ
    · simp only [hf, indicator_of_mem ht]
      exact radial_pow_mul hd ht.1
    · simp [hf, indicator_of_notMem ht]
  have hintOn : IntegrableOn (fun t : ℝ => t ^ (d - 1) * f t) (Ioi 0) := by
    rw [hfun]
    exact (integrable_indicator_iff measurableSet_Ioo).2 hIoo |>.integrableOn
  have hint : Integrable (fun y : Fin d → ℝ => f ‖y‖) := (polar_integrable hd).2 hintOn
  have hnn : ∀ t, 0 ≤ f t := fun t => by
    by_cases ht : t ∈ Ioo 0 ρ
    · simp only [hf, indicator_of_mem ht]
      exact Real.rpow_nonneg ht.1.le _
    · simp [hf, indicator_of_notMem ht]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => hnn _)]
  rw [polar_integral hd f]
  congr 2
  rw [hfun, setIntegral_indicator measurableSet_Ioo]
  have : Ioi (0 : ℝ) ∩ Ioo 0 ρ = Ioo 0 ρ := by
    ext t; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le,
    integral_rpow (Or.inl he)]
  have h0 : (0 : ℝ) ^ ((d : ℝ) - 1 - α + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0]
  have : (d : ℝ) - 1 - α + 1 = (d : ℝ) - α := by ring
  rw [this]; ring


open HRS.KernelAux in
/-- Transfer of a torus integral to a radial integral on `ℝ^d`. -/
lemma lintegral_torus_le_radial (hd : 1 ≤ d) (F : Torus d → ℝ≥0∞) (φ : ℝ → ℝ)
    (hF : ∀ y ∈ Box d, y ≠ 0 → F (boxPt y) ≤ ENNReal.ofReal (φ ‖y‖)) :
    ∫⁻ z : Torus d, F z ≤ ∫⁻ y : Fin d → ℝ, ENNReal.ofReal (φ ‖y‖) := by
  rw [lintegral_torus_box]
  refine le_trans (lintegral_mono_ae ?_) (setLIntegral_le_lintegral _ _)
  filter_upwards [ae_restrict_of_ae (ae_ne_pi hd), ae_restrict_mem (measurableSet_Box d)] with y hy hyB
  exact hF y hyB hy


open HRS.KernelAux in
/-- First level-set integral: `∫ (w - L)_+ ≤ C L^{1 - d/σ}`. -/
theorem lev1 (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB1 : 1 ≤ B)
    {w : Torus d → ℝ} (hw : ∀ y ∈ Box d, y ≠ 0 → w (boxPt y) ≤ B * (1 + ‖y‖ ^ (-σ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L →
      ∫⁻ z : Torus d, ENNReal.ofReal (max (w z - L) 0)
        ≤ ENNReal.ofReal (C * L ^ (1 - (d : ℝ) / σ)) := by
  have hB0 : 0 < B := by linarith
  have hdσ : 0 < (d : ℝ) - σ := by linarith
  set K : ℝ := (d : ℝ) * 2 ^ d / ((d : ℝ) - σ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨(B * K + B * (1 + K)) * (2 * B) ^ ((d : ℝ) / σ - 1), by positivity, fun L hL => ?_⟩
  have hexp : 1 - (d : ℝ) / σ < 0 := by
    have : 1 < (d : ℝ) / σ := by rw [lt_div_iff₀ hσ0]; linarith
    linarith
  by_cases hbig : 2 * B ≤ L
  · -- radial cutoff at ρ
    set ρ : ℝ := (2 * B / L) ^ (1 / σ) with hρ
    have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
    have hρσ : ρ ^ (-σ) = L / (2 * B) := by
      rw [hρ, ← Real.rpow_mul (by positivity)]
      have : 1 / σ * (-σ) = -1 := by field_simp
      rw [this, Real.rpow_neg_one, inv_div]
    have hpt : ∀ y ∈ Box d, y ≠ 0 → ENNReal.ofReal (max (w (boxPt y) - L) 0)
        ≤ ENNReal.ofReal (B * (Ioo 0 ρ).indicator (fun t => t ^ (-σ)) ‖y‖) := by
      intro y hy hy0
      have ht : 0 < ‖y‖ := norm_pos_iff.2 hy0
      refine ENNReal.ofReal_le_ofReal ?_
      have hwy := hw y hy hy0
      by_cases hlt : ‖y‖ < ρ
      · rw [indicator_of_mem (show ‖y‖ ∈ Ioo 0 ρ from ⟨ht, hlt⟩)]
        refine max_le ?_ (mul_nonneg hB0.le (Real.rpow_nonneg ht.le _))
        nlinarith
      · push_neg at hlt
        rw [indicator_of_notMem (show ‖y‖ ∉ Ioo 0 ρ from fun h => absurd h.2 (not_lt.2 hlt))]
        have h1 : ‖y‖ ^ (-σ) ≤ ρ ^ (-σ) := Real.rpow_le_rpow_of_nonpos hρ0 hlt (by linarith)
        rw [hρσ] at h1
        have h2 : B * (L / (2 * B)) = L / 2 := by field_simp
        refine max_le ?_ (by simp)
        nlinarith
    calc ∫⁻ z : Torus d, ENNReal.ofReal (max (w z - L) 0)
        ≤ ∫⁻ y : Fin d → ℝ, ENNReal.ofReal (B * (Ioo 0 ρ).indicator (fun t => t ^ (-σ)) ‖y‖) :=
          lintegral_torus_le_radial hd _ (fun t => B * (Ioo 0 ρ).indicator (fun t => t ^ (-σ)) t) hpt
      _ = ENNReal.ofReal B * ∫⁻ y : Fin d → ℝ,
            ENNReal.ofReal ((Ioo 0 ρ).indicator (fun t => t ^ (-σ)) ‖y‖) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul hB0.le]
      _ = ENNReal.ofReal (B * ((d : ℝ) * 2 ^ d * (ρ ^ ((d : ℝ) - σ) / ((d : ℝ) - σ)))) := by
          rw [polar_Ioo_power hd hρ0 hσd, ← ENNReal.ofReal_mul hB0.le]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hρpow : ρ ^ ((d : ℝ) - σ) = (2 * B) ^ ((d : ℝ) / σ - 1) * L ^ (1 - (d : ℝ) / σ) := by
            rw [hρ, ← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) hL.le,
              show (1 / σ * ((d : ℝ) - σ)) = (d : ℝ) / σ - 1 by field_simp,
              div_eq_mul_inv, ← Real.rpow_neg hL.le]
            congr 2; ring
          have : B * ((d : ℝ) * 2 ^ d * (ρ ^ ((d : ℝ) - σ) / ((d : ℝ) - σ)))
              = B * K * (2 * B) ^ ((d : ℝ) / σ - 1) * L ^ (1 - (d : ℝ) / σ) := by
            rw [hρpow, hK]; ring
          rw [this]
          have hp : 0 ≤ (2 * B) ^ ((d : ℝ) / σ - 1) * L ^ (1 - (d : ℝ) / σ) := by positivity
          nlinarith [mul_nonneg hB0.le hK0]
  · -- small `L`: use the global bound
    rw [not_le] at hbig
    have hpt : ∀ y ∈ Box d, y ≠ 0 → ENNReal.ofReal (max (w (boxPt y) - L) 0)
        ≤ ENNReal.ofReal (2 * B * (Ioo 0 1).indicator (fun t => t ^ (-σ)) ‖y‖) := by
      intro y hy hy0
      have ht : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hy1 : ‖y‖ < 1 := lt_of_le_of_lt (Box_norm_le hy) (by norm_num)
      refine ENNReal.ofReal_le_ofReal ?_
      rw [indicator_of_mem (show ‖y‖ ∈ Ioo 0 1 from ⟨ht, hy1⟩)]
      have hwy := hw y hy hy0
      have hu1 : 1 ≤ ‖y‖ ^ (-σ) := by
        have := Real.rpow_le_rpow_of_nonpos ht hy1.le (show -σ ≤ 0 by linarith)
        simpa using this
      refine max_le ?_ (by have := Real.rpow_nonneg ht.le (-σ); positivity)
      nlinarith
    calc ∫⁻ z : Torus d, ENNReal.ofReal (max (w z - L) 0)
        ≤ ∫⁻ y : Fin d → ℝ, ENNReal.ofReal (2 * B * (Ioo 0 1).indicator (fun t => t ^ (-σ)) ‖y‖) :=
          lintegral_torus_le_radial hd _ (fun t => 2 * B * (Ioo 0 1).indicator (fun t => t ^ (-σ)) t) hpt
      _ = ENNReal.ofReal (2 * B) * ∫⁻ y : Fin d → ℝ,
            ENNReal.ofReal ((Ioo 0 1).indicator (fun t => t ^ (-σ)) ‖y‖) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (2 * B * ((d : ℝ) * 2 ^ d * (1 ^ ((d : ℝ) - σ) / ((d : ℝ) - σ)))) := by
          rw [polar_Ioo_power hd one_pos hσd, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (2 * B) ^ (1 - (d : ℝ) / σ) ≤ L ^ (1 - (d : ℝ) / σ) :=
            Real.rpow_le_rpow_of_nonpos hL hbig.le hexp.le
          have h2 : (2 * B) ^ ((d : ℝ) / σ - 1) * (2 * B) ^ (1 - (d : ℝ) / σ) = 1 := by
            rw [← Real.rpow_add (by positivity)]; simp
          have : 2 * B * ((d : ℝ) * 2 ^ d * (1 ^ ((d : ℝ) - σ) / ((d : ℝ) - σ))) = 2 * B * K := by
            rw [Real.one_rpow, hK]; ring
          rw [this]
          have hp : 0 ≤ (2 * B) ^ ((d : ℝ) / σ - 1) := by positivity
          have h3 : 2 * B * K ≤ (B * K + B * (1 + K)) * ((2 * B) ^ ((d : ℝ) / σ - 1) * (2 * B) ^ (1 - (d : ℝ) / σ)) := by
            rw [h2]; nlinarith [mul_nonneg hB0.le hK0]
          calc 2 * B * K ≤ _ := h3
            _ ≤ (B * K + B * (1 + K)) * (2 * B) ^ ((d : ℝ) / σ - 1) * L ^ (1 - (d : ℝ) / σ) := by
              rw [mul_assoc]
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left h1 hp


open HRS.KernelAux in
/-- Second level-set integral, reduced to an annulus integral. -/
theorem lev2_base (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB1 : 1 ≤ B)
    {w : Torus d → ℝ} (hw : ∀ y ∈ Box d, y ≠ 0 → w (boxPt y) ≤ B * (1 + ‖y‖ ^ (-σ)))
    (hw0 : ∀ y ∈ Box d, y ≠ 0 → 0 ≤ w (boxPt y)) {L : ℝ} (hL : 1 ≤ L) :
    ∫⁻ z : Torus d, ENNReal.ofReal ((min (w z) L) ^ 2)
      ≤ ENNReal.ofReal (L ^ 2 * 2 ^ d * (L ^ (-(1 / σ))) ^ d + 2 * B ^ 2 * 2 ^ d
          + 2 * B ^ 2 * ((d : ℝ) * 2 ^ d * ∫ t in (L ^ (-(1 / σ)))..1, t ^ ((d : ℝ) - 1 - 2 * σ))) := by
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  set r : ℝ := L ^ (-(1 / σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by have : 0 < 1 / σ := by positivity
                                                                  linarith)
  have hrσ : r ^ (-σ) = L := by
    rw [hr, ← Real.rpow_mul hL0.le]
    have : -(1 / σ) * (-σ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hpt : ∀ y ∈ Box d, y ≠ 0 → ENNReal.ofReal ((min (w (boxPt y)) L) ^ 2)
      ≤ ENNReal.ofReal (L ^ 2 * (Ioo 0 r).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖
          + 2 * B ^ 2 * (Ioo 0 1).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖
          + 2 * B ^ 2 * (Ico r 1).indicator (fun t => t ^ (-(2 * σ))) ‖y‖) := by
    intro y hy hy0
    have ht : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hy1 : ‖y‖ < 1 := lt_of_le_of_lt (Box_norm_le hy) (by norm_num)
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (Ioo (0 : ℝ) 1).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖ = 1 := by
      rw [indicator_of_mem (show ‖y‖ ∈ Ioo 0 1 from ⟨ht, hy1⟩)]; simp
    rw [h1]
    have hw0y := hw0 y hy hy0
    have hwy := hw y hy hy0
    by_cases hlt : ‖y‖ < r
    · rw [indicator_of_mem (show ‖y‖ ∈ Ioo 0 r from ⟨ht, hlt⟩)]
      rw [indicator_of_notMem (show ‖y‖ ∉ Ico r 1 from fun h => absurd h.1 (not_le.2 hlt))]
      have : (min (w (boxPt y)) L) ^ 2 ≤ L ^ 2 := by
        have h0 : 0 ≤ min (w (boxPt y)) L := le_min hw0y hL0.le
        nlinarith [min_le_right (w (boxPt y)) L]
      simp only [Real.rpow_zero, neg_zero, mul_one, mul_zero, add_zero]
      linarith [sq_nonneg B]
    · push_neg at hlt
      rw [indicator_of_notMem (show ‖y‖ ∉ Ioo 0 r from fun h => absurd h.2 (not_lt.2 hlt))]
      rw [indicator_of_mem (show ‖y‖ ∈ Ico r 1 from ⟨hlt, hy1⟩)]
      have h0 : 0 ≤ min (w (boxPt y)) L := le_min hw0y hL0.le
      have h2 : (min (w (boxPt y)) L) ^ 2 ≤ (w (boxPt y)) ^ 2 := by
        nlinarith [min_le_left (w (boxPt y)) L]
      have h3 : (w (boxPt y)) ^ 2 ≤ (B * (1 + ‖y‖ ^ (-σ))) ^ 2 := by
        nlinarith
      have h4 : (B * (1 + ‖y‖ ^ (-σ))) ^ 2 ≤ 2 * B ^ 2 + 2 * B ^ 2 * ‖y‖ ^ (-(2 * σ)) := by
        have : ‖y‖ ^ (-(2 * σ)) = (‖y‖ ^ (-σ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; push_cast; ring
        rw [this]
        nlinarith [sq_nonneg (B * (1 - ‖y‖ ^ (-σ)))]
      simp only [Real.rpow_zero, neg_zero, mul_one, mul_zero, zero_add]
      nlinarith [sq_nonneg L]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hnn : ∀ (α : ℝ) (S : Set ℝ) (y : Fin d → ℝ), 0 ≤ S.indicator (fun t => t ^ (-α)) ‖y‖ := by
    intro α S y
    by_cases h : ‖y‖ ∈ S
    · rw [indicator_of_mem h]; exact Real.rpow_nonneg (norm_nonneg _) _
    · rw [indicator_of_notMem h]
  set g₁ : (Fin d → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal ((Ioo 0 r).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖) with hg₁
  set g₂ : (Fin d → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal ((Ioo 0 1).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖) with hg₂
  set g₃ : (Fin d → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal ((Ico r 1).indicator (fun t => t ^ (-(2 * σ))) ‖y‖) with hg₃
  have hm1 : Measurable g₁ :=
    (((measurable_id.pow_const _).indicator measurableSet_Ioo).comp measurable_norm).ennreal_ofReal
  have hm2 : Measurable g₂ :=
    (((measurable_id.pow_const _).indicator measurableSet_Ioo).comp measurable_norm).ennreal_ofReal
  have hm3 : Measurable g₃ :=
    (((measurable_id.pow_const _).indicator measurableSet_Ico).comp measurable_norm).ennreal_ofReal
  have e1 : ∫⁻ y, g₁ y = ENNReal.ofReal ((d : ℝ) * 2 ^ d * (r ^ ((d : ℝ) - 0) / ((d : ℝ) - 0))) :=
    polar_Ioo_power hd hr0 (α := 0) hd0
  have e2 : ∫⁻ y, g₂ y = ENNReal.ofReal ((d : ℝ) * 2 ^ d * ((1 : ℝ) ^ ((d : ℝ) - 0) / ((d : ℝ) - 0))) :=
    polar_Ioo_power hd one_pos (α := 0) hd0
  have e3 : ∫⁻ y, g₃ y = ENNReal.ofReal ((d : ℝ) * 2 ^ d * ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ)) :=
    polar_Ico_power hd (α := 2 * σ) hr0 hr1
  have hsum : ∀ y : Fin d → ℝ, ENNReal.ofReal (L ^ 2 * (Ioo 0 r).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖
          + 2 * B ^ 2 * (Ioo 0 1).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖
          + 2 * B ^ 2 * (Ico r 1).indicator (fun t => t ^ (-(2 * σ))) ‖y‖)
        = ENNReal.ofReal (L ^ 2) * g₁ y + ENNReal.ofReal (2 * B ^ 2) * g₂ y
          + ENNReal.ofReal (2 * B ^ 2) * g₃ y := by
    intro y
    have a1 := hnn 0 (Ioo 0 r) y
    have a2 := hnn 0 (Ioo 0 1) y
    have a3 := hnn (2 * σ) (Ico r 1) y
    have p1 : 0 ≤ L ^ 2 * (Ioo 0 r).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖ := mul_nonneg (sq_nonneg _) a1
    have p2 : 0 ≤ 2 * B ^ 2 * (Ioo 0 1).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖ :=
      mul_nonneg (by positivity) a2
    have p3 : 0 ≤ 2 * B ^ 2 * (Ico r 1).indicator (fun t => t ^ (-(2 * σ))) ‖y‖ :=
      mul_nonneg (by positivity) a3
    simp only [hg₁, hg₂, hg₃]
    rw [ENNReal.ofReal_add (add_nonneg p1 p2) p3, ENNReal.ofReal_add p1 p2,
      ENNReal.ofReal_mul (sq_nonneg L), ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * B ^ 2),
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * B ^ 2)]
  calc ∫⁻ z : Torus d, ENNReal.ofReal ((min (w z) L) ^ 2)
      ≤ ∫⁻ y : Fin d → ℝ, ENNReal.ofReal (L ^ 2 * (Ioo 0 r).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖
          + 2 * B ^ 2 * (Ioo 0 1).indicator (fun t => t ^ (-(0 : ℝ))) ‖y‖
          + 2 * B ^ 2 * (Ico r 1).indicator (fun t => t ^ (-(2 * σ))) ‖y‖) :=
        lintegral_torus_le_radial hd _ (fun t => L ^ 2 * (Ioo 0 r).indicator (fun t => t ^ (-(0 : ℝ))) t
          + 2 * B ^ 2 * (Ioo 0 1).indicator (fun t => t ^ (-(0 : ℝ))) t
          + 2 * B ^ 2 * (Ico r 1).indicator (fun t => t ^ (-(2 * σ))) t) hpt
    _ = ENNReal.ofReal (L ^ 2) * (∫⁻ y, g₁ y) + ENNReal.ofReal (2 * B ^ 2) * (∫⁻ y, g₂ y)
          + ENNReal.ofReal (2 * B ^ 2) * (∫⁻ y, g₃ y) := by
        simp_rw [hsum]
        have hA : Measurable fun y : Fin d → ℝ => ENNReal.ofReal (L ^ 2) * g₁ y := hm1.const_mul _
        have hB' : Measurable fun y : Fin d → ℝ => ENNReal.ofReal (2 * B ^ 2) * g₂ y := hm2.const_mul _
        rw [lintegral_add_left (f := fun y => ENNReal.ofReal (L ^ 2) * g₁ y + ENNReal.ofReal (2 * B ^ 2) * g₂ y)
          (hA.add hB'), lintegral_add_left (f := fun y => ENNReal.ofReal (L ^ 2) * g₁ y) hA,
          lintegral_const_mul _ hm1, lintegral_const_mul _ hm2, lintegral_const_mul _ hm3]
    _ = _ := by
        have hJ : 0 ≤ ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) :=
          intervalIntegral.integral_nonneg hr1 fun t ht => Real.rpow_nonneg (hr0.le.trans ht.1) _
        have hrd : r ^ ((d : ℝ) - 0) = r ^ d := by
          rw [sub_zero, Real.rpow_natCast]
        have h1d : (1 : ℝ) ^ ((d : ℝ) - 0) = 1 := Real.one_rpow _
        rw [e1, e2, e3, hrd, h1d]
        have q1 : 0 ≤ (d : ℝ) * 2 ^ d * (r ^ d / ((d : ℝ) - 0)) := by
          have := pow_nonneg hr0.le d; rw [sub_zero]; positivity
        have q2 : 0 ≤ (d : ℝ) * 2 ^ d * ((1 : ℝ) / ((d : ℝ) - 0)) := by rw [sub_zero]; positivity
        have q3 : 0 ≤ (d : ℝ) * 2 ^ d * ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) := by positivity
        rw [← ENNReal.ofReal_mul (sq_nonneg L), ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * B ^ 2),
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * B ^ 2),
          ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg L) q1) (mul_nonneg (by positivity) q2),
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (sq_nonneg L) q1) (mul_nonneg (by positivity) q2))
            (mul_nonneg (by positivity) q3)]
        congr 1
        rw [sub_zero]
        have hd0' : (d : ℝ) ≠ 0 := hd0.ne'
        field_simp


lemma ball_term {σ L : ℝ} (hσ0 : 0 < σ) (hL : 1 ≤ L) :
    L ^ 2 * 2 ^ d * (L ^ (-(1 / σ))) ^ d = 2 ^ d * L ^ (2 - (d : ℝ) / σ) := by
  have hL0 : 0 < L := by linarith
  have h1 : (L ^ (-(1 / σ))) ^ d = L ^ (-((d : ℝ) / σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
  rw [h1]
  have h2 : L ^ 2 = L ^ ((2 : ℝ)) := (Real.rpow_two L).symm
  have h3 : L ^ ((2 : ℝ)) * L ^ (-((d : ℝ) / σ)) = L ^ (2 - (d : ℝ) / σ) := by
    rw [← Real.rpow_add hL0, ← sub_eq_add_neg]
  rw [h2]
  calc L ^ ((2 : ℝ)) * 2 ^ d * L ^ (-((d : ℝ) / σ))
      = 2 ^ d * (L ^ ((2 : ℝ)) * L ^ (-((d : ℝ) / σ))) := by ring
    _ = _ := by rw [h3]

lemma annulus_power {σ L : ℝ} (hσ0 : 0 < σ) (hL : 1 ≤ L) :
    (L ^ (-(1 / σ))) ^ ((d : ℝ) - 2 * σ) = L ^ (2 - (d : ℝ) / σ) := by
  have hL0 : 0 < L := by linarith
  rw [← Real.rpow_mul hL0.le]; congr 1; field_simp; ring


open HRS.KernelAux in
theorem lev2a (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB1 : 1 ≤ B)
    {w : Torus d → ℝ} (hw : ∀ y ∈ Box d, y ≠ 0 → w (boxPt y) ≤ B * (1 + ‖y‖ ^ (-σ)))
    (hw0 : ∀ y ∈ Box d, y ≠ 0 → 0 ≤ w (boxPt y)) (h2 : 2 * σ < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      ∫⁻ z : Torus d, ENNReal.ofReal ((min (w z) L) ^ 2) ≤ ENNReal.ofReal C := by
  have hB0 : 0 < B := by linarith
  have he : (-1 : ℝ) < (d : ℝ) - 1 - 2 * σ := by linarith
  have hpos : 0 < (d : ℝ) - 2 * σ := by linarith
  refine ⟨2 ^ d + 2 * B ^ 2 * 2 ^ d + 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / ((d : ℝ) - 2 * σ)), by positivity, fun L hL => ?_⟩
  refine (lev2_base hd hσ0 hσd hB1 hw hw0 hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : 0 < L := by linarith
  set r : ℝ := L ^ (-(1 / σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by have : 0 < 1 / σ := by positivity
                                                                  linarith)
  rw [ball_term hσ0 hL]
  have h1 : L ^ (2 - (d : ℝ) / σ) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hL ?_
    have : 2 < (d : ℝ) / σ := by rw [lt_div_iff₀ hσ0]; linarith
    linarith
  have hJ : ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) ≤ 1 / ((d : ℝ) - 2 * σ) := by
    rw [integral_rpow (Or.inl he)]
    have h3 : (d : ℝ) - 1 - 2 * σ + 1 = (d : ℝ) - 2 * σ := by ring
    rw [h3, Real.one_rpow]
    have : 0 ≤ r ^ ((d : ℝ) - 2 * σ) := Real.rpow_nonneg hr0.le _
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hcoef : 0 ≤ 2 * B ^ 2 * ((d : ℝ) * 2 ^ d) := by positivity
  have := mul_le_mul_of_nonneg_left hJ hcoef
  have e1 : 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / ((d : ℝ) - 2 * σ)) = 2 * B ^ 2 * ((d : ℝ) * 2 ^ d) * (1 / ((d : ℝ) - 2 * σ)) := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left h1 h2d]


open HRS.KernelAux in
theorem lev2b (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB1 : 1 ≤ B)
    {w : Torus d → ℝ} (hw : ∀ y ∈ Box d, y ≠ 0 → w (boxPt y) ≤ B * (1 + ‖y‖ ^ (-σ)))
    (hw0 : ∀ y ∈ Box d, y ≠ 0 → 0 ≤ w (boxPt y)) (h2 : 2 * σ = d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      ∫⁻ z : Torus d, ENNReal.ofReal ((min (w z) L) ^ 2)
        ≤ ENNReal.ofReal (C * Real.log (Real.exp 1 * L)) := by
  have hB0 : 0 < B := by linarith
  refine ⟨2 ^ d + 2 * B ^ 2 * 2 ^ d + 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / σ), by positivity, fun L hL => ?_⟩
  refine (lev2_base hd hσ0 hσd hB1 hw hw0 hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : 0 < L := by linarith
  set r : ℝ := L ^ (-(1 / σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  rw [ball_term hσ0 hL]
  have hexp : 2 - (d : ℝ) / σ = 0 := by
    have : (d : ℝ) = 2 * σ := h2.symm
    rw [this]; field_simp; ring
  rw [hexp, Real.rpow_zero, mul_one]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hJ : ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) = Real.log L / σ := by
    have : ∀ t : ℝ, t ^ ((d : ℝ) - 1 - 2 * σ) = t⁻¹ := by
      intro t
      have : (d : ℝ) - 1 - 2 * σ = -1 := by rw [← h2]; ring
      rw [this, Real.rpow_neg_one]
    simp_rw [this]
    rw [integral_inv_of_pos hr0 one_pos, one_div, Real.log_inv, hr, Real.log_rpow hL0]
    field_simp
  rw [hJ]
  have hlogeL : Real.log (Real.exp 1 * L) = 1 + Real.log L := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hL0.ne', Real.log_exp]
  rw [hlogeL]
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hc1 : 0 ≤ 2 * B ^ 2 * 2 ^ d := by positivity
  have hc2 : 0 ≤ 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / σ) := by positivity
  have e1 : 2 * B ^ 2 * ((d : ℝ) * 2 ^ d * (Real.log L / σ))
      = 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / σ) * Real.log L := by ring
  rw [e1]
  nlinarith [mul_nonneg hc2 hlog]

open HRS.KernelAux in
theorem lev2c (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB1 : 1 ≤ B)
    {w : Torus d → ℝ} (hw : ∀ y ∈ Box d, y ≠ 0 → w (boxPt y) ≤ B * (1 + ‖y‖ ^ (-σ)))
    (hw0 : ∀ y ∈ Box d, y ≠ 0 → 0 ≤ w (boxPt y)) (h2 : (d : ℝ) < 2 * σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      ∫⁻ z : Torus d, ENNReal.ofReal ((min (w z) L) ^ 2)
        ≤ ENNReal.ofReal (C * L ^ (2 - (d : ℝ) / σ)) := by
  have hB0 : 0 < B := by linarith
  have hpos : 0 < 2 * σ - (d : ℝ) := by linarith
  refine ⟨2 ^ d + 2 * B ^ 2 * 2 ^ d + 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / (2 * σ - (d : ℝ))), by positivity, fun L hL => ?_⟩
  refine (lev2_base hd hσ0 hσd hB1 hw hw0 hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : 0 < L := by linarith
  set r : ℝ := L ^ (-(1 / σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by have : 0 < 1 / σ := by positivity
                                                                  linarith)
  rw [ball_term hσ0 hL]
  have h1 : 1 ≤ L ^ (2 - (d : ℝ) / σ) := by
    refine Real.one_le_rpow hL ?_
    have : (d : ℝ) / σ < 2 := by rw [div_lt_iff₀ hσ0]; linarith
    linarith
  have hJ : ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) ≤ L ^ (2 - (d : ℝ) / σ) / (2 * σ - (d : ℝ)) := by
    have he : (d : ℝ) - 1 - 2 * σ ≠ -1 := by intro h; linarith
    rw [integral_rpow (Or.inr ⟨he, by
      rw [Set.mem_uIcc]; push Not; exact ⟨fun h => absurd h (not_le.2 hr0), fun h => absurd h (by norm_num)⟩⟩)]
    have h3 : (d : ℝ) - 1 - 2 * σ + 1 = (d : ℝ) - 2 * σ := by ring
    rw [h3, Real.one_rpow, annulus_power hσ0 hL]
    have : (1 - L ^ (2 - (d : ℝ) / σ)) / ((d : ℝ) - 2 * σ)
        = (L ^ (2 - (d : ℝ) / σ) - 1) / (2 * σ - (d : ℝ)) := by
      have : (d : ℝ) - 2 * σ ≠ 0 := by intro h; linarith
      field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hcoef : 0 ≤ 2 * B ^ 2 * ((d : ℝ) * 2 ^ d) := by positivity
  have := mul_le_mul_of_nonneg_left hJ hcoef
  have e1 : 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / (2 * σ - (d : ℝ)))
      = 2 * B ^ 2 * ((d : ℝ) * 2 ^ d) * (1 / (2 * σ - (d : ℝ))) := by field_simp
  have e2 : 2 * B ^ 2 * ((d : ℝ) * 2 ^ d) * (L ^ (2 - (d : ℝ) / σ) / (2 * σ - (d : ℝ)))
      = 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / (2 * σ - (d : ℝ))) * L ^ (2 - (d : ℝ) / σ) := by ring
  have hLp : 0 ≤ L ^ (2 - (d : ℝ) / σ) := by positivity
  have hc2 : 0 ≤ 2 * B ^ 2 * ((d : ℝ) * 2 ^ d / (2 * σ - (d : ℝ))) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h2d, mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * B ^ 2 * 2 ^ d by positivity)]

end HRS.WeakRef

end WM_F

section WM_G
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {q : E → E → ℝ}

/-- `L²` estimate of `q * |h|` from row bounds of the two pieces `min(q,N)` and `(q - N)_+`. -/
theorem conv_abstract (hqm : Measurable (Function.uncurry q)) (hq0 : ∀ x y, 0 ≤ q x y)
    (hqs : ∀ x y, q x y = q y x) (hqi : ∀ x, Integrable (q x) μ) {N a₂ b₁ : ℝ} (hN : 0 ≤ N)
    (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁)
    (hrow2 : ∀ x, ∫ y, max (q x y - N) 0 ∂μ ≤ a₂)
    (hrow1 : ∀ x, ∫ y, (min (q x y) N) ^ 2 ∂μ ≤ b₁)
    {h : E → ℝ} (hh : Measurable h) {M ε : ℝ} (hM : 0 ≤ M) (hhM : ∀ y, |h y| ≤ M)
    (hε : ∫ y, |h y| ∂μ ≤ ε) :
    ∫ x, (∫ y, q x y * |h y| ∂μ) ^ 2 ∂μ ≤ 2 * (ε ^ 2 * b₁ + a₂ ^ 2 * (M * ε)) := by
  set q₁ : E → E → ℝ := fun x y => min (q x y) N with hq₁
  set q₂ : E → E → ℝ := fun x y => max (q x y - N) 0 with hq₂
  have hq₁m : Measurable (Function.uncurry q₁) := hqm.min measurable_const
  have hq₂m : Measurable (Function.uncurry q₂) := (hqm.sub_const N).max measurable_const
  have hq₁0 : ∀ x y, 0 ≤ q₁ x y := fun x y => le_min (hq0 x y) hN
  have hq₂0 : ∀ x y, 0 ≤ q₂ x y := fun x y => le_max_right _ _
  have hq₁s : ∀ x y, q₁ x y = q₁ y x := fun x y => by simp only [hq₁, hqs x y]
  have hq₂s : ∀ x y, q₂ x y = q₂ y x := fun x y => by simp only [hq₂, hqs x y]
  have hq₁N : ∀ x y, q₁ x y ≤ N := fun x y => min_le_right _ _
  have hq₂q : ∀ x y, q₂ x y ≤ q x y := fun x y => max_le (by linarith [hq0 x y]) (hq0 x y)
  have hqx : ∀ x, Measurable (q x) := fun x => hqm.comp (measurable_const.prodMk measurable_id)
  have hq₁x : ∀ x, Measurable (q₁ x) := fun x => hq₁m.comp (measurable_const.prodMk measurable_id)
  have hq₂x : ∀ x, Measurable (q₂ x) := fun x => hq₂m.comp (measurable_const.prodMk measurable_id)
  have hq₂i : ∀ x, Integrable (q₂ x) μ := fun x =>
    Integrable.mono' (hqi x) (hq₂x x).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq₂0 x y)]; exact hq₂q x y)
  have habs : Measurable fun y => |h y| := hh.abs
  have hM' : ∀ y, |(|h y|)| ≤ M := fun y => by rw [abs_abs]; exact hhM y
  -- integrability of the pieces
  have hi₁ : ∀ x, Integrable (fun y => q₁ x y * |h y|) μ := fun x =>
    intg_bdd ((hq₁x x).mul habs) (C := N * M) fun y => by
      rw [abs_of_nonneg (mul_nonneg (hq₁0 x y) (abs_nonneg _))]
      exact mul_le_mul (hq₁N x y) (hhM y) (abs_nonneg _) hN
  have hi₂ : ∀ x, Integrable (fun y => q₂ x y * |h y|) μ := fun x =>
    Integrable.mono' ((hqi x).mul_const M) ((hq₂x x).mul habs).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq₂0 x y) (abs_nonneg _))]
        exact mul_le_mul (hq₂q x y) (hhM y) (abs_nonneg _) (hq0 x y))
  have hsplit : ∀ x, ∫ y, q x y * |h y| ∂μ = ∫ y, q₁ x y * |h y| ∂μ + ∫ y, q₂ x y * |h y| ∂μ := by
    intro x
    rw [← integral_add (hi₁ x) (hi₂ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hq₁, hq₂]
    rw [← add_mul]
    congr 1
    rcases le_total (q x y) N with h1 | h1
    · simp [min_eq_left h1, max_eq_right (by linarith : q x y - N ≤ 0)]
    · simp [min_eq_right h1, max_eq_left (by linarith : 0 ≤ q x y - N)]
  -- Part 2: Schur
  have hB2 : ∫ x, (∫ y, q₂ x y * |h y| ∂μ) ^ 2 ∂μ ≤ a₂ ^ 2 * (M * ε) := by
    have hs := schur_sq (μ := μ) hq₂m hq₂0 hq₂s ha₂ hrow2 hq₂i habs hM hM'
    refine hs.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have hsq : ∀ y, |h y| ^ 2 ≤ M * |h y| := fun y => by
      nlinarith [abs_nonneg (h y), hhM y]
    calc ∫ y, |h y| ^ 2 ∂μ ≤ ∫ y, M * |h y| ∂μ :=
          integral_mono (intg_sq_bdd habs (C := M) hM') (hh.abs.const_mul M |> fun hm => intg_bdd hm (C := M * M)
            (fun y => by
              rw [abs_of_nonneg (mul_nonneg hM (abs_nonneg _))]
              exact mul_le_mul_of_nonneg_left (hhM y) hM)) hsq
      _ = M * ∫ y, |h y| ∂μ := integral_const_mul _ _
      _ ≤ M * ε := mul_le_mul_of_nonneg_left hε hM
  -- Part 1: Cauchy-Schwarz and Fubini
  have hint0 : Integrable (fun y => |h y|) μ := intg_bdd habs (C := M) hM'
  have hε0 : 0 ≤ ε := (integral_nonneg fun y => abs_nonneg _).trans hε
  have hpt1 : ∀ x, (∫ y, q₁ x y * |h y| ∂μ) ^ 2 ≤ ε * ∫ y, |h y| * q₁ x y ^ 2 ∂μ := by
    intro x
    have h1 := cs_weight (μ := μ) habs (fun y => abs_nonneg _) hint0 (hq₁x x) hN (fun y => by
      rw [abs_of_nonneg (hq₁0 x y)]; exact hq₁N x y)
    have e : ∫ y, q₁ x y * |h y| ∂μ = ∫ y, |h y| * q₁ x y ∂μ := by
      simp_rw [mul_comm (q₁ x _)]
    rw [e]
    refine h1.trans (mul_le_mul_of_nonneg_right hε (integral_nonneg fun y => mul_nonneg (abs_nonneg _) (sq_nonneg _)))
  have hprod : Integrable (fun p : E × E => |h p.2| * q₁ p.1 p.2 ^ 2) (μ.prod μ) := by
    refine Integrable.of_bound ((habs.comp measurable_snd).mul ((hq₁m.comp measurable_id).pow_const 2)).aestronglyMeasurable
      (M * N ^ 2) (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    refine mul_le_mul (hhM _) ?_ (sq_nonneg _) hM
    have := hq₁0 p.1 p.2; have := hq₁N p.1 p.2
    nlinarith
  have hJm : Measurable fun x => ∫ y, |h y| * q₁ x y ^ 2 ∂μ := by
    have : Measurable fun p : E × E => |h p.2| * q₁ p.1 p.2 ^ 2 :=
      (habs.comp measurable_snd).mul ((hq₁m.comp measurable_id).pow_const 2)
    exact (this.stronglyMeasurable.integral_prod_right').measurable
  have hJi : Integrable (fun x => ∫ y, |h y| * q₁ x y ^ 2 ∂μ) μ := hprod.integral_prod_left
  have hJb : ∫ x, ∫ y, |h y| * q₁ x y ^ 2 ∂μ ∂μ ≤ ε * b₁ := by
    rw [integral_integral_swap hprod]
    have : ∀ y, ∫ x, |h y| * q₁ x y ^ 2 ∂μ ≤ |h y| * b₁ := by
      intro y
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc ∫ x, q₁ x y ^ 2 ∂μ = ∫ x, (min (q y x) N) ^ 2 ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only [hq₁, hqs x y]
        _ ≤ b₁ := hrow1 y
    calc ∫ y, ∫ x, |h y| * q₁ x y ^ 2 ∂μ ∂μ ≤ ∫ y, |h y| * b₁ ∂μ :=
          integral_mono hprod.integral_prod_right (hint0.mul_const _) this
      _ = (∫ y, |h y| ∂μ) * b₁ := integral_mul_const _ _
      _ ≤ ε * b₁ := mul_le_mul_of_nonneg_right hε hb₁
  have hA1m : Measurable fun x => ∫ y, q₁ x y * |h y| ∂μ := measurable_rowInt' hq₁m habs
  have hA1b : ∀ x, |∫ y, q₁ x y * |h y| ∂μ| ≤ N * M := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => q₁ x y * |h y|) (C := N * M)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq₁0 x y) (abs_nonneg _))]
        exact mul_le_mul (hq₁N x y) (hhM y) (abs_nonneg _) hN)
    simpa using this
  have hA2m : Measurable fun x => ∫ y, q₂ x y * |h y| ∂μ := measurable_rowInt' hq₂m habs
  have hB1 : ∫ x, (∫ y, q₁ x y * |h y| ∂μ) ^ 2 ∂μ ≤ ε ^ 2 * b₁ := by
    calc ∫ x, (∫ y, q₁ x y * |h y| ∂μ) ^ 2 ∂μ ≤ ∫ x, ε * ∫ y, |h y| * q₁ x y ^ 2 ∂μ ∂μ :=
          integral_mono (intg_sq_bdd hA1m hA1b) (hJi.const_mul ε) hpt1
      _ = ε * ∫ x, ∫ y, |h y| * q₁ x y ^ 2 ∂μ ∂μ := integral_const_mul _ _
      _ ≤ ε * (ε * b₁) := mul_le_mul_of_nonneg_left hJb hε0
      _ = ε ^ 2 * b₁ := by ring
  -- combine
  have hA2b : ∀ x, |∫ y, q₂ x y * |h y| ∂μ| ≤ M * a₂ := fun x => by
    have h1 : ∫ y, q₂ x y * |h y| ∂μ ≤ ∫ y, M * q₂ x y ∂μ :=
      integral_mono (hi₂ x) ((hq₂i x).const_mul M) fun y => by
        have := mul_le_mul_of_nonneg_left (hhM y) (hq₂0 x y)
        linarith [mul_comm (q₂ x y) M]
    have h2 : ∫ y, M * q₂ x y ∂μ = M * ∫ y, q₂ x y ∂μ := integral_const_mul _ _
    have h3 : 0 ≤ ∫ y, q₂ x y * |h y| ∂μ := integral_nonneg fun y => mul_nonneg (hq₂0 x y) (abs_nonneg _)
    rw [abs_of_nonneg h3]
    have h4 : ∫ y, q₂ x y ∂μ ≤ a₂ := hrow2 x
    nlinarith
  have hpt : ∀ x, (∫ y, q x y * |h y| ∂μ) ^ 2
      ≤ 2 * (∫ y, q₁ x y * |h y| ∂μ) ^ 2 + 2 * (∫ y, q₂ x y * |h y| ∂μ) ^ 2 := by
    intro x
    rw [hsplit x]
    nlinarith [sq_nonneg (∫ y, q₁ x y * |h y| ∂μ - ∫ y, q₂ x y * |h y| ∂μ)]
  have hAm : Measurable fun x => ∫ y, q x y * |h y| ∂μ := measurable_rowInt' hqm habs
  have hAb : ∀ x, |∫ y, q x y * |h y| ∂μ| ≤ N * M + M * a₂ := fun x => by
    rw [hsplit x]
    exact (abs_add_le _ _).trans (add_le_add (hA1b x) (hA2b x))
  calc ∫ x, (∫ y, q x y * |h y| ∂μ) ^ 2 ∂μ
      ≤ ∫ x, (2 * (∫ y, q₁ x y * |h y| ∂μ) ^ 2 + 2 * (∫ y, q₂ x y * |h y| ∂μ) ^ 2) ∂μ :=
        integral_mono (intg_sq_bdd hAm hAb) (((intg_sq_bdd hA1m hA1b).const_mul 2).add
          ((intg_sq_bdd hA2m hA2b).const_mul 2)) hpt
    _ = 2 * ∫ x, (∫ y, q₁ x y * |h y| ∂μ) ^ 2 ∂μ + 2 * ∫ x, (∫ y, q₂ x y * |h y| ∂μ) ^ 2 ∂μ := by
        rw [integral_add ((intg_sq_bdd hA1m hA1b).const_mul 2) ((intg_sq_bdd hA2m hA2b).const_mul 2),
          integral_const_mul, integral_const_mul]
    _ ≤ 2 * (ε ^ 2 * b₁ + a₂ ^ 2 * (M * ε)) := by linarith


/-- A probability measure `≤ D μ` has a bounded measurable density. -/
lemma exists_density_le {ν : Measure E} {D : ℝ} (hD : 0 ≤ D) (hν : ν ≤ ENNReal.ofReal D • μ) :
    ∃ g : E → ℝ, Measurable g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ D) ∧
      ν = μ.withDensity (fun y => ENNReal.ofReal (g y)) := by
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    calc ν Set.univ ≤ (ENNReal.ofReal D • μ) Set.univ := hν _
      _ < ⊤ := by simp
  have hrn : ν.rnDeriv μ ≤ᵐ[μ] fun _ => ENNReal.ofReal D := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _) fun A hA _ => ?_
    rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
    calc ν A ≤ (ENNReal.ofReal D • μ) A := hν A
      _ = ENNReal.ofReal D * μ A := by simp
  have hfin : ∀ᵐ y ∂μ, ν.rnDeriv μ y < ⊤ := Measure.rnDeriv_lt_top _ _
  refine ⟨fun y => min D (ν.rnDeriv μ y).toReal, ?_, fun y => ⟨le_min hD ENNReal.toReal_nonneg, min_le_left _ _⟩, ?_⟩
  · exact measurable_const.min (Measure.measurable_rnDeriv _ _).ennreal_toReal
  · conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ν μ hac]
    refine withDensity_congr_ae ?_
    filter_upwards [hrn, hfin] with y h1 h2
    have h3 : (ν.rnDeriv μ y).toReal ≤ D := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal hD] at this
    rw [min_eq_right h3, ENNReal.ofReal_toReal h2.ne]


lemma integral_density {g : E → ℝ} (hgm : Measurable g) (hg0 : ∀ y, 0 ≤ g y) {f : E → ℝ} :
    ∫ y, f y ∂(μ.withDensity (fun y => ENNReal.ofReal (g y))) = ∫ y, g y * f y ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hgm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hg0 y)]

lemma real_density {g : E → ℝ} (hgm : Measurable g) (hg0 : ∀ y, 0 ≤ g y) (A : Set E)
    (hA : MeasurableSet A) :
    (μ.withDensity (fun y => ENNReal.ofReal (g y))).real A = ∫ y in A, g y ∂μ := by
  rw [Measure.real, withDensity_apply _ hA,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hg0 y)
      hgm.aestronglyMeasurable]

set_option maxHeartbeats 800000 in
/-- Measure form of the `L²` convolution estimate. -/
theorem conv_measures (hqm : Measurable (Function.uncurry q)) (hq0 : ∀ x y, 0 ≤ q x y)
    (hqs : ∀ x y, q x y = q y x) (hqi : ∀ x, Integrable (q x) μ) {N a₂ b₁ D ε₀ : ℝ} (hN : 0 ≤ N)
    (ha₂ : 0 ≤ a₂) (hb₁ : 0 ≤ b₁)
    (hrow2 : ∀ x, ∫ y, max (q x y - N) 0 ∂μ ≤ a₂)
    (hrow1 : ∀ x, ∫ y, (min (q x y) N) ^ 2 ∂μ ≤ b₁) (hD : 0 ≤ D)
    (ν₁ ν₂ : Measure E) (h₁ : ν₁ ≤ ENNReal.ofReal D • μ) (h₂ : ν₂ ≤ ENNReal.ofReal D • μ)
    (hTV : ∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A| ≤ ε₀) :
    ∫ x, (∫ y, q x y ∂ν₁ - ∫ y, q x y ∂ν₂) ^ 2 ∂μ
      ≤ 2 * ((2 * ε₀) ^ 2 * b₁ + a₂ ^ 2 * (D * (2 * ε₀))) := by
  obtain ⟨g₁, hg₁m, hg₁, rfl⟩ := exists_density_le hD h₁
  obtain ⟨g₂, hg₂m, hg₂, rfl⟩ := exists_density_le hD h₂
  set h : E → ℝ := fun y => g₁ y - g₂ y with hhdef
  have hhm : Measurable h := hg₁m.sub hg₂m
  have hhM : ∀ y, |h y| ≤ D := fun y => by
    rw [abs_le]; constructor <;> linarith [(hg₁ y).1, (hg₁ y).2, (hg₂ y).1, (hg₂ y).2]
  have hqx : ∀ x, Measurable (q x) := fun x => hqm.comp (measurable_const.prodMk measurable_id)
  have hε₀ : 0 ≤ ε₀ := (abs_nonneg _).trans (hTV Set.univ MeasurableSet.univ)
  -- L¹ bound
  have hg₁i : Integrable g₁ μ := intg_bdd hg₁m (C := D) fun y => by
    rw [abs_of_nonneg (hg₁ y).1]; exact (hg₁ y).2
  have hg₂i : Integrable g₂ μ := intg_bdd hg₂m (C := D) fun y => by
    rw [abs_of_nonneg (hg₂ y).1]; exact (hg₂ y).2
  have hL1 : ∫ y, |h y| ∂μ ≤ 2 * ε₀ := by
    set S : Set E := {y | g₂ y < g₁ y} with hS
    have hSm : MeasurableSet S := measurableSet_lt hg₂m hg₁m
    have hhi : Integrable (fun y => |h y|) μ := intg_bdd hhm.abs (C := D) fun y => by
      rw [abs_abs]; exact hhM y
    rw [← integral_add_compl hSm hhi]
    have e1 : ∫ y in S, |h y| ∂μ = ∫ y in S, g₁ y ∂μ - ∫ y in S, g₂ y ∂μ := by
      rw [← integral_sub hg₁i.integrableOn hg₂i.integrableOn]
      refine setIntegral_congr_fun hSm fun y hy => ?_
      simp only [hhdef]; rw [abs_of_pos (sub_pos.2 hy)]
    have e2 : ∫ y in Sᶜ, |h y| ∂μ = ∫ y in Sᶜ, g₂ y ∂μ - ∫ y in Sᶜ, g₁ y ∂μ := by
      rw [← integral_sub hg₂i.integrableOn hg₁i.integrableOn]
      refine setIntegral_congr_fun hSm.compl fun y hy => ?_
      have : g₁ y ≤ g₂ y := by simpa [hS] using hy
      simp only [hhdef]; rw [abs_of_nonpos (sub_nonpos.2 this)]; ring
    rw [e1, e2]
    have t1 := hTV S hSm
    have t2 := hTV Sᶜ hSm.compl
    rw [real_density hg₁m (fun y => (hg₁ y).1) S hSm, real_density hg₂m (fun y => (hg₂ y).1) S hSm] at t1
    rw [real_density hg₁m (fun y => (hg₁ y).1) Sᶜ hSm.compl,
      real_density hg₂m (fun y => (hg₂ y).1) Sᶜ hSm.compl] at t2
    rw [abs_le] at t1 t2
    linarith [t1.2, t2.1]
  -- the difference of fields
  have hdiff : ∀ x, ∫ y, q x y ∂(μ.withDensity (fun y => ENNReal.ofReal (g₁ y)))
      - ∫ y, q x y ∂(μ.withDensity (fun y => ENNReal.ofReal (g₂ y))) = ∫ y, q x y * h y ∂μ := by
    intro x
    rw [integral_density hg₁m (fun y => (hg₁ y).1), integral_density hg₂m (fun y => (hg₂ y).1)]
    have i1 : Integrable (fun y => g₁ y * q x y) μ :=
      Integrable.mono' ((hqi x).const_mul D) (hg₁m.mul (hqx x)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg₁ y).1 (hq0 x y))]
          exact mul_le_mul_of_nonneg_right (hg₁ y).2 (hq0 x y))
    have i2 : Integrable (fun y => g₂ y * q x y) μ :=
      Integrable.mono' ((hqi x).const_mul D) (hg₂m.mul (hqx x)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg₂ y).1 (hq0 x y))]
          exact mul_le_mul_of_nonneg_right (hg₂ y).2 (hq0 x y))
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hhdef]; ring
  have hsq : ∀ x, (∫ y, q x y ∂(μ.withDensity (fun y => ENNReal.ofReal (g₁ y)))
      - ∫ y, q x y ∂(μ.withDensity (fun y => ENNReal.ofReal (g₂ y)))) ^ 2
      ≤ (∫ y, q x y * |h y| ∂μ) ^ 2 := by
    intro x
    rw [hdiff x]
    have hb : |∫ y, q x y * h y ∂μ| ≤ ∫ y, q x y * |h y| ∂μ := by
      refine (abs_integral_le_integral_abs).trans ?_
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) ?_
        (Filter.Eventually.of_forall fun y => ?_)
      · exact Integrable.mono' ((hqi x).const_mul D) ((hqx x).mul hhm.abs).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 x y) (abs_nonneg _))]
            exact mul_le_mul_of_nonneg_left (hhM y) (hq0 x y) |>.trans (le_of_eq (mul_comm _ _)))
      · show |q x y * h y| ≤ q x y * |h y|
        rw [abs_mul, abs_of_nonneg (hq0 x y)]
    have := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rwa [sq_abs] at this
  have hqrow : ∀ x, ∫ y, q x y ∂μ ≤ N + a₂ := by
    intro x
    have h1 : ∫ y, q x y ∂μ ≤ ∫ y, (N + max (q x y - N) 0) ∂μ :=
      integral_mono (hqi x) ((integrable_const N).add (Integrable.mono' (hqi x)
        ((hqx x).sub_const N |>.max measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
          exact max_le (by linarith [hq0 x y]) (hq0 x y)))) fun y => by
        rcases le_total (q x y) N with h | h
        · rw [max_eq_right (by linarith)]; linarith
        · rw [max_eq_left (by linarith)]; linarith
    have h2 : ∫ y, (N + max (q x y - N) 0) ∂μ = N + ∫ y, max (q x y - N) 0 ∂μ := by
      rw [integral_add (integrable_const N) (Integrable.mono' (hqi x)
        ((hqx x).sub_const N |>.max measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
          exact max_le (by linarith [hq0 x y]) (hq0 x y)))]
      simp
    linarith [hrow2 x]
  have hG0 : ∀ x, 0 ≤ ∫ y, q x y * |h y| ∂μ := fun x =>
    integral_nonneg fun y => mul_nonneg (hq0 x y) (abs_nonneg _)
  have hGb : ∀ x, |∫ y, q x y * |h y| ∂μ| ≤ D * (N + a₂) := by
    intro x
    rw [abs_of_nonneg (hG0 x)]
    have hint : Integrable (fun y => q x y * |h y|) μ :=
      Integrable.mono' ((hqi x).const_mul D) ((hqx x).mul hhm.abs).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 x y) (abs_nonneg _))]
          exact mul_le_mul_of_nonneg_left (hhM y) (hq0 x y) |>.trans (le_of_eq (mul_comm _ _)))
    calc ∫ y, q x y * |h y| ∂μ ≤ ∫ y, D * q x y ∂μ :=
          integral_mono hint ((hqi x).const_mul D) fun y => by
            have := mul_le_mul_of_nonneg_left (hhM y) (hq0 x y)
            linarith [mul_comm (q x y) D]
      _ = D * ∫ y, q x y ∂μ := integral_const_mul _ _
      _ ≤ D * (N + a₂) := mul_le_mul_of_nonneg_left (hqrow x) hD
  have hGm : Measurable fun x => ∫ y, q x y * |h y| ∂μ := measurable_rowInt' hqm hhm.abs
  have hmain := conv_abstract hqm hq0 hqs hqi hN ha₂ hb₁ hrow2 hrow1 hhm hD hhM hL1
  calc ∫ x, (∫ y, q x y ∂(μ.withDensity (fun y => ENNReal.ofReal (g₁ y)))
        - ∫ y, q x y ∂(μ.withDensity (fun y => ENNReal.ofReal (g₂ y)))) ^ 2 ∂μ
      ≤ ∫ x, (∫ y, q x y * |h y| ∂μ) ^ 2 ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (intg_sq_bdd hGm hGb) (Filter.Eventually.of_forall hsq)
    _ ≤ _ := hmain

end HRS.WeakRef.Abs

end WM_G

section WM_H
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ}

lemma sigmaOf_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) : 0 < sigmaOf d s := by
  unfold sigmaOf
  have : (0 : ℝ) < d := by exact_mod_cast hd
  split_ifs with h
  · positivity
  · exact lt_of_le_of_ne hs0 (Ne.symm h)

lemma sigmaOf_lt (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) : sigmaOf d s < d := by
  unfold sigmaOf
  have : (0 : ℝ) < d := by exact_mod_cast hd
  split_ifs with h
  · linarith
  · exact hsd

lemma two_sigmaOf_lt_iff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) :
    2 * sigmaOf d s < d ↔ s < (d : ℝ) / 2 := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  unfold sigmaOf
  split_ifs with h
  · subst h; constructor <;> intro _ <;> linarith
  · constructor <;> intro h' <;> linarith

lemma sigmaOf_eq (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) : sigmaOf d s = s := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  unfold sigmaOf
  rw [if_neg]
  intro h; subst h; linarith

lemma inv_le_deltaN (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)⁻¹ ≤ deltaN d s N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold deltaN
  split_ifs with h1 h2
  · exact le_rfl
  · have : 1 ≤ Real.log (Real.exp 1 * N) := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
      have := Real.log_nonneg hN'
      linarith
    have h0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
    nlinarith
  · push Not at h1
    have hs : 0 < s := by
      rcases lt_or_eq_of_le h1 with h | h
      · linarith
      · have : s ≠ (d : ℝ) / 2 := h2
        exact absurd h.symm this
    have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne h1 (Ne.symm h2)
    have h4 : -1 ≤ 1 - (d : ℝ) / s := by
      have : (d : ℝ) / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith
      linarith
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN' h4

lemma rpow_le_deltaN (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - (d : ℝ) / sigmaOf d s) ≤ deltaN d s N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ0 := sigmaOf_pos hd hs0
  unfold deltaN
  split_ifs with h1 h2
  · -- s < d/2
    have h2σ : 2 * sigmaOf d s < d := (two_sigmaOf_lt_iff hd hs0).2 h1
    have h3 : 1 - (d : ℝ) / sigmaOf d s ≤ -1 := by
      have : 2 ≤ (d : ℝ) / sigmaOf d s := by rw [le_div_iff₀ hσ0]; linarith
      linarith
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN' h3
  · have hσ : sigmaOf d s = s := sigmaOf_eq hd (by rw [h2])
    rw [hσ]
    have : 1 - (d : ℝ) / s = -1 := by
      have hs : 0 < s := by rw [h2]; positivity
      rw [h2]; field_simp; ring
    rw [this, Real.rpow_neg_one]
    have : 1 ≤ Real.log (Real.exp 1 * N) := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
      have := Real.log_nonneg hN'
      linarith
    have h0 : 0 ≤ (N : ℝ)⁻¹ := by positivity
    nlinarith
  · push Not at h1
    have hσ : sigmaOf d s = s := sigmaOf_eq hd h1
    rw [hσ]


open HRS.KernelAux in
theorem kernel_levels (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ L : ℝ, 0 < L → ∫⁻ z : Torus d, ENNReal.ofReal (max (periodicRiesz d s z + cstar - L) 0)
          ≤ ENNReal.ofReal (C₁ * L ^ (1 - (d : ℝ) / sigmaOf d s))) ∧
      (∀ N : ℕ, 2 ≤ N → ∫⁻ z : Torus d, ENNReal.ofReal ((min (periodicRiesz d s z + cstar) N) ^ 2)
          ≤ ENNReal.ofReal (C₂ * (N * deltaN d s N))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ0 := sigmaOf_pos hd hs0
  have hσd := sigmaOf_lt hd hsd
  obtain ⟨B, hB1, hB⟩ := riesz_envelope hd hs0 hsd cstar
  set w : Torus d → ℝ := fun z => periodicRiesz d s z + cstar with hwdef
  have hwB : ∀ y ∈ Box d, y ≠ 0 → w (boxPt y) ≤ B * (1 + ‖y‖ ^ (-(sigmaOf d s))) := hB
  have hw0 : ∀ y ∈ Box d, y ≠ 0 → 0 ≤ w (boxPt y) := fun y hy hy0 => by
    have := hw (boxPt y) (fun h => hy0 (boxPt_eq_zero hy h))
    simp only [hwdef]; linarith
  obtain ⟨C₁, hC₁, hlev1⟩ := lev1 hd hσ0 hσd hB1 hwB
  have h2 : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ N : ℕ, 2 ≤ N → ∫⁻ z : Torus d,
      ENNReal.ofReal ((min (periodicRiesz d s z + cstar) N) ^ 2)
        ≤ ENNReal.ofReal (C₂ * (N * deltaN d s N)) := by
    rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
    · have h2σ : 2 * sigmaOf d s < d := (two_sigmaOf_lt_iff hd hs0).2 h
      obtain ⟨C, hC, hlev⟩ := lev2a hd hσ0 hσd hB1 hwB hw0 h2σ
      refine ⟨C, hC, fun N hN => ?_⟩
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hNpos : (0 : ℝ) < N := by linarith
      have : (N : ℝ) * deltaN d s N = 1 := by
        unfold deltaN; rw [if_pos h]; field_simp
      rw [this, mul_one]
      exact hlev N hN1
    · have hσ : sigmaOf d s = s := sigmaOf_eq hd (by rw [h])
      have h2σ : 2 * sigmaOf d s = d := by rw [hσ, h]; ring
      obtain ⟨C, hC, hlev⟩ := lev2b hd hσ0 hσd hB1 hwB hw0 h2σ
      refine ⟨C, hC, fun N hN => ?_⟩
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hNpos : (0 : ℝ) < N := by linarith
      have : (N : ℝ) * deltaN d s N = Real.log (Real.exp 1 * N) := by
        unfold deltaN; rw [if_neg (not_lt.2 h.ge), if_pos h]; field_simp
      rw [this]
      exact hlev N hN1
    · have hσ : sigmaOf d s = s := sigmaOf_eq hd h.le
      have h2σ : (d : ℝ) < 2 * sigmaOf d s := by rw [hσ]; linarith
      obtain ⟨C, hC, hlev⟩ := lev2c hd hσ0 hσd hB1 hwB hw0 h2σ
      refine ⟨C, hC, fun N hN => ?_⟩
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hNpos : (0 : ℝ) < N := by linarith
      have : (N : ℝ) * deltaN d s N = (N : ℝ) ^ (2 - (d : ℝ) / sigmaOf d s) := by
        unfold deltaN; rw [if_neg (not_lt.2 h.le), if_neg h.ne', hσ]
        have : (2 : ℝ) - (d : ℝ) / s = 1 + (1 - (d : ℝ) / s) := by ring
        rw [this, Real.rpow_add hNpos, Real.rpow_one]
      rw [this]
      exact hlev N hN1
  obtain ⟨C₂, hC₂, h2'⟩ := h2
  exact ⟨C₁, C₂, hC₁, hC₂, hlev1, h2'⟩

end HRS.WeakRef

end WM_H

section WM_I
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ}

lemma ae_ne_withDensityReal (hd : 1 ≤ d) (ρ : Torus d → ℝ) (x : Torus d) :
    ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := by
  have h : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
    rw [ae_iff]
    simpa using volume_singleton_torus hd x
  exact (withDensity_absolutelyContinuous _ _).ae_le h

/-- Row bounds of a kernel dominated by the Riesz envelope. -/
theorem row_bounds (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) (A Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧
      ∀ (ρ : Torus d → ℝ) [IsProbabilityMeasure (withDensityReal ρ)], (∀ x, ρ x ≤ Λ₀) →
        ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, 0 ≤ q x y) →
        (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
        ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
          ∫ y, max (q x y - N) 0 ∂(withDensityReal ρ) ≤ Ca * deltaN d s N ∧
          ∫ y, (min (q x y) N) ^ 2 ∂(withDensityReal ρ) ≤ Cb * (N * deltaN d s N) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hlev1, hlev2⟩ := kernel_levels hd hs0 hsd cstar hw
  set Ā : ℝ := max A 1 with hĀ
  have hĀ1 : 1 ≤ Ā := le_max_right _ _
  have hĀ0 : 0 < Ā := by linarith
  have hAĀ : A ≤ Ā := le_max_left _ _
  set e : ℝ := 1 - (d : ℝ) / sigmaOf d s with he
  refine ⟨Λ₀ * Ā * C₁ * Ā ^ (-e), Λ₀ * Ā ^ 2 * C₂, by positivity, by positivity, ?_⟩
  intro ρ _ hρ q hqm hq0 hqA N hN x
  set μ := withDensityReal ρ with hμ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by linarith
  set w : Torus d → ℝ := fun z => periodicRiesz d s z + cstar with hwdef
  have hqx : Measurable (q x) := hqm.comp (measurable_const.prodMk measurable_id)
  have hae := ae_ne_withDensityReal hd ρ x
  have hpt : ∀ y, y ≠ x → q x y ≤ Ā * w (x - y) ∧ 0 ≤ w (x - y) := by
    intro y hy
    have h1 := hw (x - y) (sub_ne_zero.2 (Ne.symm hy))
    have h2 := hqA x y
    have h0 : 0 ≤ w (x - y) := by simp only [hwdef]; linarith
    refine ⟨h2.trans ?_, h0⟩
    exact mul_le_mul_of_nonneg_right hAĀ h0
  constructor
  · -- tail
    have hnn : ∀ y, 0 ≤ max (q x y - N) 0 := fun y => le_max_right _ _
    have hm : Measurable fun y => max (q x y - N) 0 := (hqx.sub_const _).max measurable_const
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hm.aestronglyMeasurable]
    have hle : ∫⁻ y, ENNReal.ofReal (max (q x y - N) 0) ∂μ
        ≤ ENNReal.ofReal (Λ₀ * Ā * C₁ * (N / Ā) ^ e) := by
      calc ∫⁻ y, ENNReal.ofReal (max (q x y - N) 0) ∂μ
          ≤ ∫⁻ y, (ENNReal.ofReal Ā * ENNReal.ofReal (max (w (x - y) - N / Ā) 0)) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae] with y hy
            obtain ⟨h1, h0⟩ := hpt y hy
            rw [← ENNReal.ofReal_mul hĀ0.le]
            refine ENNReal.ofReal_le_ofReal (max_le ?_ (mul_nonneg hĀ0.le (le_max_right _ _)))
            have : Ā * (w (x - y) - N / Ā) ≤ Ā * max (w (x - y) - N / Ā) 0 :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) hĀ0.le
            have e2 : Ā * (w (x - y) - N / Ā) = Ā * w (x - y) - N := by field_simp
            linarith
        _ ≤ ENNReal.ofReal Λ₀ * ∫⁻ z, (ENNReal.ofReal Ā * ENNReal.ofReal (max (w z - N / Ā) 0)) :=
            KernelAux2.lintegral_conv_le ρ Λ₀ hρ
              (fun z => ENNReal.ofReal Ā * ENNReal.ofReal (max (w z - N / Ā) 0)) x
        _ = ENNReal.ofReal Λ₀ * (ENNReal.ofReal Ā * ∫⁻ z, ENNReal.ofReal (max (w z - N / Ā) 0)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal Λ₀ * (ENNReal.ofReal Ā * ENNReal.ofReal (C₁ * (N / Ā) ^ e)) := by
            gcongr
            exact hlev1 _ (by positivity)
        _ = _ := by
            rw [← ENNReal.ofReal_mul hĀ0.le, ← ENNReal.ofReal_mul hΛ₀]
            congr 1; ring
    have hbd : Λ₀ * Ā * C₁ * (N / Ā) ^ e ≤ Λ₀ * Ā * C₁ * Ā ^ (-e) * deltaN d s N := by
      have h1 : (N / Ā) ^ e = (N : ℝ) ^ e * Ā ^ (-e) := by
        rw [Real.div_rpow hNpos.le hĀ0.le, Real.rpow_neg hĀ0.le, div_eq_mul_inv]
      rw [h1]
      have h2 := rpow_le_deltaN hd hs0 hsd (N := N) (by omega)
      have h3 : 0 ≤ Λ₀ * Ā * C₁ * Ā ^ (-e) := by positivity
      calc Λ₀ * Ā * C₁ * ((N : ℝ) ^ e * Ā ^ (-e)) = Λ₀ * Ā * C₁ * Ā ^ (-e) * (N : ℝ) ^ e := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3
    have hpos : 0 ≤ Λ₀ * Ā * C₁ * (N / Ā) ^ e := by positivity
    calc (∫⁻ y, ENNReal.ofReal (max (q x y - N) 0) ∂μ).toReal
        ≤ (ENNReal.ofReal (Λ₀ * Ā * C₁ * (N / Ā) ^ e)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = Λ₀ * Ā * C₁ * (N / Ā) ^ e := ENNReal.toReal_ofReal hpos
      _ ≤ _ := hbd
  · -- second moment
    have hnn : ∀ y, 0 ≤ (min (q x y) N) ^ 2 := fun y => sq_nonneg _
    have hm : Measurable fun y => (min (q x y) N) ^ 2 := (hqx.min measurable_const).pow_const 2
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hm.aestronglyMeasurable]
    have hle : ∫⁻ y, ENNReal.ofReal ((min (q x y) N) ^ 2) ∂μ
        ≤ ENNReal.ofReal (Λ₀ * Ā ^ 2 * (C₂ * (N * deltaN d s N))) := by
      calc ∫⁻ y, ENNReal.ofReal ((min (q x y) N) ^ 2) ∂μ
          ≤ ∫⁻ y, (ENNReal.ofReal (Ā ^ 2) * ENNReal.ofReal ((min (w (x - y)) N) ^ 2)) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae] with y hy
            obtain ⟨h1, h0⟩ := hpt y hy
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hq0' := hq0 x y
            have h2 : min (q x y) N ≤ Ā * min (w (x - y)) N := by
              rw [mul_min_of_nonneg _ _ hĀ0.le]
              exact le_min ((min_le_left _ _).trans h1)
                ((min_le_right _ _).trans (le_mul_of_one_le_left hNpos.le hĀ1))
            have h3 : 0 ≤ min (q x y) N := le_min hq0' hNpos.le
            have := pow_le_pow_left₀ h3 h2 2
            calc (min (q x y) N) ^ 2 ≤ (Ā * min (w (x - y)) N) ^ 2 := this
              _ = Ā ^ 2 * (min (w (x - y)) N) ^ 2 := by ring
        _ ≤ ENNReal.ofReal Λ₀ * ∫⁻ z, (ENNReal.ofReal (Ā ^ 2) * ENNReal.ofReal ((min (w z) N) ^ 2)) :=
            KernelAux2.lintegral_conv_le ρ Λ₀ hρ
              (fun z => ENNReal.ofReal (Ā ^ 2) * ENNReal.ofReal ((min (w z) N) ^ 2)) x
        _ = ENNReal.ofReal Λ₀ * (ENNReal.ofReal (Ā ^ 2) * ∫⁻ z, ENNReal.ofReal ((min (w z) N) ^ 2)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal Λ₀ * (ENNReal.ofReal (Ā ^ 2) * ENNReal.ofReal (C₂ * (N * deltaN d s N))) := by
            gcongr
            exact hlev2 N hN
        _ = _ := by
            rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hΛ₀]
            congr 1; ring
    have hdel : 0 ≤ deltaN d s N := deltaN_nonneg s (by omega)
    have hpos : 0 ≤ Λ₀ * Ā ^ 2 * (C₂ * (N * deltaN d s N)) := by positivity
    calc (∫⁻ y, ENNReal.ofReal ((min (q x y) N) ^ 2) ∂μ).toReal
        ≤ (ENNReal.ofReal (Λ₀ * Ā ^ 2 * (C₂ * (N * deltaN d s N)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = Λ₀ * Ā ^ 2 * (C₂ * (N * deltaN d s N)) := ENNReal.toReal_ofReal hpos
      _ = Λ₀ * Ā ^ 2 * C₂ * (N * deltaN d s N) := by ring

end HRS.WeakRef

end WM_I

section WM_J
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ}


lemma continuous_of_lift3 {E : Type*} [TopologicalSpace E] {f : Torus d → E}
    (h : Continuous (Torus.lift f)) : Continuous f := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) :=
    h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h2.isQuotientMap.continuous_iff.2 h

lemma le_cbNorm_zero {ρ : Torus d → ℝ} (hρ : Torus.IsSmooth ρ) (x : Torus d) :
    ρ x ≤ Torus.cbNorm 0 ρ := by
  have hc : Continuous ρ := continuous_of_lift3 (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) from hρ).continuous
  unfold Torus.cbNorm
  simp only [zero_add, Finset.range_one, Finset.sum_singleton]
  have hbdd : BddAbove (Set.range fun y : Euc d => ‖iteratedFDeriv ℝ 0 (Torus.lift ρ) y‖) := by
    obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨R, ?_⟩
    rintro _ ⟨y, rfl⟩
    show ‖iteratedFDeriv ℝ 0 (Torus.lift ρ) y‖ ≤ R
    rw [norm_iteratedFDeriv_zero]
    exact hR (Torus.mk y) trivial
  have h := le_ciSup hbdd (Torus.rep x)
  have e : ‖iteratedFDeriv ℝ 0 (Torus.lift ρ) (Torus.rep x)‖ = |ρ x| := by
    rw [norm_iteratedFDeriv_zero]
    simp [Torus.lift, Torus.mk_rep]
  rw [e] at h
  exact (le_abs_self _).trans h


lemma ka_alg {κ₀ D Ca Cb δ T1 T2 n NR : ℝ} (hκ₀ : 0 ≤ κ₀) (hD0 : 0 ≤ D) (hn0 : 0 ≤ n)
    (hNR : 0 < NR) (hnN : n ≤ NR) (hδ : 0 ≤ δ) (hT10 : 0 ≤ T1) (hT20 : 0 ≤ T2)
    (hT1 : T1 ≤ Ca * δ) (hT2 : T2 ≤ Cb * (NR * δ)) :
    2 * ((κ₀ / NR) * (n * (D * T1))) + (κ₀ / NR) ^ 2 / 2 * (2 * n * (D * T2))
      ≤ (2 * κ₀ * D * Ca + κ₀ ^ 2 * D * Cb) * δ := by
  have hr : n / NR ≤ 1 := by rw [div_le_one hNR]; exact hnN
  have hr0 : 0 ≤ n / NR := div_nonneg hn0 hNR.le
  have e1 : 2 * ((κ₀ / NR) * (n * (D * T1))) = 2 * κ₀ * (n / NR) * D * T1 := by
    field_simp
  have e2 : (κ₀ / NR) ^ 2 / 2 * (2 * n * (D * T2)) = κ₀ ^ 2 * (n / NR) * D * T2 / NR := by
    field_simp
  rw [e1, e2]
  have a1 : 2 * κ₀ * (n / NR) * D * T1 ≤ 2 * κ₀ * D * (Ca * δ) := by
    have h1 : 2 * κ₀ * (n / NR) * D * T1 ≤ 2 * κ₀ * 1 * D * T1 := by
      have : 0 ≤ 2 * κ₀ * D * T1 := by positivity
      nlinarith
    have h2 : 2 * κ₀ * D * T1 ≤ 2 * κ₀ * D * (Ca * δ) := by
      exact mul_le_mul_of_nonneg_left hT1 (by positivity)
    linarith
  have a2 : κ₀ ^ 2 * (n / NR) * D * T2 / NR ≤ κ₀ ^ 2 * D * (Cb * δ) := by
    rw [div_le_iff₀ hNR]
    have h1 : κ₀ ^ 2 * (n / NR) * D * T2 ≤ κ₀ ^ 2 * 1 * D * T2 := by
      have : 0 ≤ κ₀ ^ 2 * D * T2 := by positivity
      nlinarith
    have h2 : κ₀ ^ 2 * D * T2 ≤ κ₀ ^ 2 * D * (Cb * (NR * δ)) :=
      mul_le_mul_of_nonneg_left hT2 (by positivity)
    have e3 : κ₀ ^ 2 * D * (Cb * (NR * δ)) = κ₀ ^ 2 * D * (Cb * δ) * NR := by ring
    linarith
  have e4 : (2 * κ₀ * D * Ca + κ₀ ^ 2 * D * Cb) * δ = 2 * κ₀ * D * (Ca * δ) + κ₀ ^ 2 * D * (Cb * δ) := by ring
  linarith

lemma kb_alg {ε₀ Ca Cb D E δ NR : ℝ} (hε₀ : 0 ≤ ε₀) (h2ε : 2 * ε₀ ≤ 1 / NR) (hNR : 1 ≤ NR)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hD0 : 0 ≤ D) (hDE : D ≤ E) (hδ : 0 ≤ δ) (hδ1 : NR⁻¹ ≤ δ) :
    2 * ((2 * ε₀) ^ 2 * (Cb * (NR * δ)) + (Ca * δ) ^ 2 * (D * (2 * ε₀)))
      ≤ 2 * (Cb + Ca ^ 2 * E) * δ ^ 2 := by
  have hNR0 : 0 < NR := by linarith
  have hE0 : 0 ≤ E := hD0.trans hDE
  have h1 : (2 * ε₀) ^ 2 ≤ (1 / NR) ^ 2 := pow_le_pow_left₀ (by positivity) h2ε 2
  have h2 : (2 * ε₀) ^ 2 * (Cb * (NR * δ)) ≤ (1 / NR) ^ 2 * (Cb * (NR * δ)) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 : (1 / NR) ^ 2 * (Cb * (NR * δ)) = Cb * δ * NR⁻¹ := by field_simp
  have h4 : Cb * δ * NR⁻¹ ≤ Cb * δ * δ := mul_le_mul_of_nonneg_left hδ1 (by positivity)
  have h5 : (Ca * δ) ^ 2 * (D * (2 * ε₀)) ≤ (Ca * δ) ^ 2 * (E * 1) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : 2 * ε₀ ≤ 1 := h2ε.trans (by rw [div_le_one hNR0]; exact hNR)
    exact mul_le_mul hDE this (by positivity) hE0
  have h6 : (Ca * δ) ^ 2 * (E * 1) = Ca ^ 2 * E * δ ^ 2 := by ring
  nlinarith


lemma final_alg {κ₀ P D E Ca Cb δ Kc a NR : ℝ} (hκ₀ : 0 ≤ κ₀) (hκP : κ₀ ≤ P) (hD0 : 0 ≤ D)
    (hDE : D ≤ E) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hδ : 0 ≤ δ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hNR : 0 < NR) (hδ1 : NR⁻¹ ≤ δ) :
    150 * ((2 * κ₀ * D * Ca + κ₀ ^ 2 * D * Cb) * δ) ^ 2 + 214 * κ₀ ^ 2 * (Kc * δ) ^ 2
        + 12 * (κ₀ * a / NR) ^ 2
      ≤ (150 * (2 * P * E * Ca + P ^ 2 * E * Cb) ^ 2 + 214 * P ^ 2 * Kc ^ 2 + 12 * P ^ 2) * δ ^ 2 := by
  have hP0 : 0 ≤ P := hκ₀.trans hκP
  have hE0 : 0 ≤ E := hD0.trans hDE
  have h1 : 0 ≤ 2 * κ₀ * D * Ca + κ₀ ^ 2 * D * Cb := by positivity
  have h2 : 2 * κ₀ * D * Ca + κ₀ ^ 2 * D * Cb ≤ 2 * P * E * Ca + P ^ 2 * E * Cb := by
    have a1 : 2 * κ₀ * D * Ca ≤ 2 * P * E * Ca := by gcongr
    have a2 : κ₀ ^ 2 * D * Cb ≤ P ^ 2 * E * Cb := by gcongr
    linarith
  have h3 : ((2 * κ₀ * D * Ca + κ₀ ^ 2 * D * Cb) * δ) ^ 2
      ≤ ((2 * P * E * Ca + P ^ 2 * E * Cb) * δ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h2 hδ) 2
  have h4 : κ₀ ^ 2 * (Kc * δ) ^ 2 ≤ P ^ 2 * (Kc * δ) ^ 2 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hκ₀ hκP 2) (sq_nonneg _)
  have h5 : κ₀ * a / NR ≤ P * δ := by
    have : κ₀ * a ≤ P := by
      calc κ₀ * a ≤ κ₀ * 1 := mul_le_mul_of_nonneg_left ha1 hκ₀
        _ ≤ P := by linarith
    rw [div_eq_mul_inv]
    exact mul_le_mul this hδ1 (by positivity) hP0
  have h6 : (κ₀ * a / NR) ^ 2 ≤ (P * δ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h5 2
  have e1 : ((2 * P * E * Ca + P ^ 2 * E * Cb) * δ) ^ 2 = (2 * P * E * Ca + P ^ 2 * E * Cb) ^ 2 * δ ^ 2 := by ring
  have e2 : (Kc * δ) ^ 2 = Kc ^ 2 * δ ^ 2 := by ring
  have e3 : (P * δ) ^ 2 = P ^ 2 * δ ^ 2 := by ring
  nlinarith [h3, h4, h6, e1, e2, e3]

end HRS.WeakRef

end WM_J

section WM_K
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {B : Type*} [Fintype B]

/-- Disintegration of the `(n+1)`-particle ensemble with respect to coordinate `i`: integral of a
function of `(y_i, y_{-i})`. -/
theorem lintegral_pinned_succ (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) (Φ : E → (Fin n → E) → ℝ≥0∞)
    (hΦ : Measurable fun p : E × (Fin n → E) => Φ p.1 p.2) :
    ∫⁻ y, Φ (y i) (fun k => y (i.succAbove k)) ∂(pinnedLaw V lam (n + 1) a)
      = ∫⁻ x, pinWeight V lam a n x * ∫⁻ y, Φ x y ∂(pinnedLaw V lam n (pinsWith a x)) ∂μ := by
  have hψ := isField_pinField V hlam a
  have hψx : ∀ x, IsField μ (pinField V lam (pinsWith a x)) V.M
      (V.M' + lam * Fintype.card (Option B) * V.γ) := fun x => isField_pinField V hlam _
  change ∫⁻ y, Φ (y i) (fun k => y (i.succAbove k)) ∂(fieldLaw V (pinField V lam a) lam (n + 1)) = _
  unfold fieldLaw
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hsymm : ∀ (x : E) (y : Fin n → E), e.symm (x, y) = insertAt i x y := fun _ _ => rfl
  have hdens := measurable_fieldDensity hψ.measurable V lam (n + 1)
  have hΨ : Measurable fun y : Fin (n + 1) → E => Φ (y i) (fun k => y (i.succAbove k)) :=
    hΦ.comp (show Measurable fun y : Fin (n + 1) → E => (y i, fun k => y (i.succAbove k)) from
      (measurable_pi_apply i).prodMk (measurable_pi_iff.2 fun k => measurable_pi_apply _))
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens hΨ]
  set h : (Fin (n + 1) → E) → ℝ≥0∞ := fun y =>
    fieldDensity V (pinField V lam a) lam (n + 1) y * Φ (y i) (fun k => y (i.succAbove k)) with hh
  have hhm : Measurable h := hdens.mul hΨ
  have step1 : ∫⁻ y, h y ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫⁻ p, h (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => h (e.symm p))
    rw [← this]
    exact lintegral_congr fun y => by rw [e.symm_apply_apply]
  change ∫⁻ y, h y ∂(Measure.pi fun _ : Fin (n + 1) => μ) = _
  rw [step1, lintegral_prod (fun p => h (e.symm p)) (hhm.comp e.symm.measurable).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [hsymm]
  have hΦx : Measurable fun y : Fin n → E => Φ x y := hΦ.comp (measurable_const.prodMk measurable_id)
  have hx : ∀ y : Fin n → E, h (insertAt i x y)
      = (ENNReal.ofReal (Real.exp (pinField V lam a x)) * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹)
        * (fieldWeight V (pinField V lam (pinsWith a x)) lam y * Φ x y) := by
    intro y
    simp only [hh, insertAt_same]
    have : (fun k => insertAt i x y (i.succAbove k)) = y := funext fun k => insertAt_succAbove i x y k
    rw [this]
    unfold fieldDensity
    rw [fieldWeight_insertAt]; ring
  simp_rw [hx]
  have hNx := fieldNorm_pos (hψx x).measurable V lam n
  have hNxt := fieldNorm_lt_top (V := V) (hψx x) hlam n
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (fieldNorm_pos hψ.measurable V lam (n + 1)).ne'))]
  change _ = _ * ∫⁻ y, Φ x y ∂(fieldLaw V (pinField V lam (pinsWith a x)) lam n)
  unfold fieldLaw
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_fieldDensity (hψx x).measurable V lam n) hΦx]
  have hfd : ∀ y, ((fun y => fieldDensity V (pinField V lam (pinsWith a x)) lam n y) * fun y => Φ x y) y
      = (fieldNorm V (pinField V lam (pinsWith a x)) lam n)⁻¹
        * (fieldWeight V (pinField V lam (pinsWith a x)) lam y * Φ x y) := by
    intro y
    simp only [Pi.mul_apply]
    unfold fieldDensity; ring
  rw [lintegral_congr hfd, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hNx.ne')]
  unfold pinWeight
  have hcancel : fieldNorm V (pinField V lam (pinsWith a x)) lam n
      * (fieldNorm V (pinField V lam (pinsWith a x)) lam n)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hNx.ne' hNxt.ne
  set Nx := fieldNorm V (pinField V lam (pinsWith a x)) lam n
  set I := ∫⁻ (a_1 : Fin n → E), fieldWeight V (pinField V lam (pinsWith a x)) lam a_1 * Φ x a_1
    ∂Measure.pi fun x => μ
  calc ENNReal.ofReal (Real.exp (pinField V lam a x)) * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹ * I
      = ENNReal.ofReal (Real.exp (pinField V lam a x)) * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹
        * ((Nx * Nx⁻¹) * I) := by rw [hcancel, one_mul]
    _ = _ := by ring


/-- Marginals of a field ensemble whose field has the extra decay `ψ ≤ M - ε`. -/
theorem marginal_le_field {ψ : E → ℝ} {M M₁ lam Λ : ℝ} (V : WeakPotential μ)
    (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) {n : ℕ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (ε : E → ℝ) (hε0 : ∀ z, 0 ≤ ε z) (hψε : ∀ z, ψ z ≤ M - ε z) (i : Fin n) :
    (fieldLaw V ψ lam n).map (fun y => y i)
      ≤ μ.withDensity (fun z => ENNReal.ofReal (Real.exp (M + Λ) * Real.exp (-ε z))) := by
  have hP : IsProbabilityMeasure (fieldLaw V ψ lam n) :=
    (fieldSpec (V := V) hψ hlam n).isProb
  refine Measure.le_iff.2 fun A hA => ?_
  rw [Measure.map_apply (measurable_pi_apply _) hA]
  have hS : MeasurableSet ((fun y : Fin n → E => y i) ⁻¹' A) := measurable_pi_apply _ hA
  have hinv := invariant_density (μ := μ) (W := fieldDensity V ψ lam n)
    (measurable_fieldDensity hψ.measurable V _ n) (fieldDensity_pos hψ hlam n)
    (fieldDensity_le hψ hlam n) i
    (φ := ((fun y : Fin n → E => y i) ⁻¹' A).indicator 1) (measurable_one.indicator hS)
  change ∫⁻ x, ∫⁻ z, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞)
      (update x i z) ∂(siteKernel μ (fieldDensity V ψ lam n) i x) ∂(fieldLaw V ψ lam n)
      = ∫⁻ x, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞) x
          ∂(fieldLaw V ψ lam n) at hinv
  have h1 : ∀ x : Fin n → E, ∫⁻ z, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞)
      (update x i z) ∂(siteKernel μ (fieldDensity V ψ lam n) i x)
      = siteKernel μ (fieldDensity V ψ lam n) i x A := by
    intro x
    rw [← lintegral_indicator_one hA]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ A
    · simp [Set.indicator_apply, hz]
    · simp [Set.indicator_apply, hz]
  simp_rw [h1] at hinv
  have hsite : ∀ x : Fin n → E, siteKernel μ (fieldDensity V ψ lam n) i x A
      ≤ (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (M + Λ) * Real.exp (-ε z)))) A := by
    intro x
    rw [siteKernel_fieldDensity hψ hlam, withDensity_apply _ hA, withDensity_apply _ hA]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    have h1 := exp_le_integral_siteU (V := V) hψ hlam i x
    have h2 : Real.exp (-Λ) ≤ ∫ z', siteU V ψ lam i x z' ∂μ :=
      le_trans (Real.exp_le_exp.2 (by linarith)) h1
    rw [div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) h2)]
    have h3 : siteU V ψ lam i x z ≤ Real.exp (M - ε z) := by
      unfold siteU
      refine Real.exp_le_exp.2 ?_
      have := mul_nonneg hlam (sumq_nonneg V i x z)
      linarith [hψε z]
    calc siteU V ψ lam i x z ≤ Real.exp (M - ε z) := h3
      _ = Real.exp (M + Λ) * Real.exp (-ε z) * Real.exp (-Λ) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc (fieldLaw V ψ lam n) ((fun y : Fin n → E => y i) ⁻¹' A)
      = ∫⁻ x, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞) x
          ∂(fieldLaw V ψ lam n) := by rw [lintegral_indicator_one hS]
    _ = ∫⁻ x, siteKernel μ (fieldDensity V ψ lam n) i x A ∂(fieldLaw V ψ lam n) := hinv.symm
    _ ≤ ∫⁻ _x, (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (M + Λ) * Real.exp (-ε z)))) A
          ∂(fieldLaw V ψ lam n) := lintegral_mono hsite
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]


/-- Marginals of the pinned ensemble: density `≤ C e^{-λ q(z, x₀)}` with respect to `μ`. -/
theorem pinned_marginal_le_decay (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + (Fintype.card B + 1) ≤ N) (a : B → E) (x₀ : E) (i : Fin n) :
    (pinnedLaw V (β / N) n (pinsWith a x₀)).map (fun y => y i)
      ≤ μ.withDensity (fun z => ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)
          * Real.exp (-((β / N) * V.q z x₀)))) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam (pinsWith a x₀)
  have hΛ := weak_Lambda_le V hβ hN0 (B := Option B) (n := n) (by simpa [Fintype.card_option] using hN)
  have hψa := isField_pinField V hlam a
  have := marginal_le_field V hψ hlam (n := n) (Λ := V.M' + β * V.γ)
    (by
      have h := hΛ
      simpa using h)
    (fun z => (β / N) * V.q z x₀) (fun z => mul_nonneg hlam (V.q_nonneg _ _))
    (fun z => by
      rw [pinField_pinsWith]
      linarith [hψa.le z]) i
  rw [← add_assoc] at this
  exact this


/-- Wu's inequality for `G = N⁻¹ ∑_{i<j} q - ∑ H`, reduced to second moments of the single-coordinate
fluctuation `g_i = N⁻¹ ∑_{l ≠ i} q(x_i, x_l) - H(x_i)` (source `N:eq:row-variance`, first step). -/
theorem evariance_G_le (V : WeakPotential μ) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) {n : ℕ}
    (hκ : weakKappa V κ₀ ≤ 1 / 2) (H : E → ℝ) (hHm : Measurable H)
    (G : (Fin (n + 1) → E) → ℝ)
    (hG : ∀ X, G X = (1 / ((n + 1 : ℕ) : ℝ)) * pairEnergy V X - ∑ k, H (X k)) :
    evariance G (pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ 2 * ∑ i : Fin (n + 1), ∫⁻ x, ‖(1 / ((n + 1 : ℕ) : ℝ)) * ∑ l ∈ Finset.univ.erase i,
            V.q (x i) (x l) - H (x i)‖ₑ ^ 2
          ∂(pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hlam : 0 ≤ κ₀ / ((n + 1 : ℕ) : ℝ) := div_nonneg hκ₀ (Nat.cast_nonneg (n + 1))
  set a₀ : Empty → E := fun e => e.elim with ha₀
  set P := pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀ with hP
  have hψ := isField_pinField V hlam a₀
  have hGm : Measurable G := by
    have : G = fun X => (1 / ((n + 1 : ℕ) : ℝ)) * pairEnergy V X - ∑ k, H (X k) := funext hG
    rw [this]
    exact (measurable_pairEnergy V |>.const_mul _).sub
      (Finset.measurable_sum _ fun k _ => hHm.comp (measurable_pi_apply k))
  have hW := weak_resampling V hκ₀ hN0 (n := n + 1) (B := Empty) (by simp) a₀ hκ G hGm
  refine hW.trans ?_
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun (i : Fin (n + 1)) (_ : i ∈ Finset.univ) => ?_)

  -- the one-coordinate observable
  set Ψ : (Fin (n + 1) → E) → ℝ≥0∞ := fun X =>
    ‖(1 / ((n + 1 : ℕ) : ℝ)) * ∑ l ∈ Finset.univ.erase i, V.q (X i) (X l) - H (X i)‖ₑ ^ 2 with hΨ
  have hΨm : Measurable Ψ := by
    refine (Measurable.enorm ?_).pow_const 2
    refine (measurable_const.mul (Finset.measurable_sum _ fun l _ => ?_)).sub
      (hHm.comp (measurable_pi_apply i))
    exact V.measurable_q.comp (show Measurable fun X : Fin (n + 1) → E => (X i, X l) from
      (measurable_pi_apply i).prodMk (measurable_pi_apply l))
  have hsite : ∀ x : Fin (n + 1) → E,
      evariance (fun z => G (update x i z)) (siteKernel μ (pinnedDensity V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀) i x)
        ≤ ∫⁻ z, Ψ (update x i z) ∂(siteKernel μ (pinnedDensity V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀) i x) := by
    intro x
    have hprob : IsProbabilityMeasure (siteKernel μ (pinnedDensity V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀) i x) := by
      have := (fieldSpec (V := V) hψ hlam (n + 1)).isMarkov i
      exact (fieldSpec_G (V := V) hψ hlam (n + 1) i ▸ this).isProbabilityMeasure x
    set g : E → ℝ := fun z => (1 / ((n + 1 : ℕ) : ℝ)) * ∑ l ∈ Finset.univ.erase i, V.q z (x l) - H z with hgdef
    have hgm : Measurable g := by
      refine (measurable_const.mul (Finset.measurable_sum _ fun l _ => ?_)).sub hHm
      exact V.measurable_q.comp (measurable_id.prodMk measurable_const)
    have hGupd : (fun z => G (update x i z)) = fun z => g z
        + ((1 / ((n + 1 : ℕ) : ℝ)) * HRS.External.pairRest V i x - ∑ k ∈ Finset.univ.erase i, H (x k)) := by
      funext z
      rw [hG, pairEnergy_update, sum_update_psi]
      simp only [hgdef]; ring
    rw [hGupd, evariance_add_const' _ hgm.aestronglyMeasurable]
    refine (evariance_le_lintegral_sub _ hgm.aestronglyMeasurable 0).trans ?_
    refine le_of_eq (lintegral_congr fun z => ?_)
    simp only [hΨ, sub_zero, hgdef]
    have e1 : ∑ l ∈ Finset.univ.erase i, V.q (update x i z i) (update x i z l)
        = ∑ l ∈ Finset.univ.erase i, V.q z (x l) :=
      Finset.sum_congr rfl fun l hl => by simp [Finset.ne_of_mem_erase hl]
    rw [e1, update_self]
  calc ∫⁻ x, evariance (fun z => G (update x i z)) (siteKernel μ (pinnedDensity V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀) i x) ∂P
      ≤ ∫⁻ x, ∫⁻ z, Ψ (update x i z) ∂(siteKernel μ (pinnedDensity V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀) i x) ∂P :=
        lintegral_mono hsite
    _ = ∫⁻ x, Ψ x ∂P := by
        have := (fieldSpec (V := V) hψ hlam (n + 1)).invariant i Ψ hΨm
        exact this

end HRS.WeakRef.Abs

end WM_K

section WM_L
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {B : Type*} [Fintype B]

lemma enorm_sq_eq (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

lemma enorm_sq_le (a m : ℝ) : ‖a‖ₑ ^ 2 ≤ 2 * ‖a - m‖ₑ ^ 2 + 2 * ‖m‖ₑ ^ 2 := by
  rw [enorm_sq_eq, enorm_sq_eq, enorm_sq_eq]
  have h : a ^ 2 ≤ 2 * (a - m) ^ 2 + 2 * m ^ 2 := by nlinarith [sq_nonneg (a - 2 * m)]
  calc ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal (2 * (a - m) ^ 2 + 2 * m ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = 2 * ENNReal.ofReal ((a - m) ^ 2) + 2 * ENNReal.ofReal (m ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp

lemma sq_mul_exp_le {u lam : ℝ} (hu : 0 ≤ u) (hlam : 0 < lam) :
    u ^ 2 * Real.exp (-(lam * u)) ≤ (2 / lam * Real.exp (-1)) ^ 2 := by
  have h1 := Real.mul_exp_neg_le_exp_neg_one (lam * u / 2)
  have h2 : u * Real.exp (-(lam * u / 2)) = 2 / lam * ((lam * u / 2) * Real.exp (-(lam * u / 2))) := by
    field_simp
  have h3 : u * Real.exp (-(lam * u / 2)) ≤ 2 / lam * Real.exp (-1) := by
    rw [h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : u ^ 2 * Real.exp (-(lam * u)) = (u * Real.exp (-(lam * u / 2))) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [h4]
  exact pow_le_pow_left₀ (by positivity) h3 2

/-- Second moment of the fluctuation of the row sum under the pinned ensemble. -/
theorem cond_moment (V : WeakPotential μ) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) {n : ℕ} (hn : 0 < n)
    (hκ : weakKappa V κ₀ ≤ 1 / 2) (a₀ : Empty → E) (x : E) (h : ℝ) :
    ∫⁻ y, ‖(1 / ((n + 1 : ℕ) : ℝ)) * ∑ k, V.q x (y k) - h‖ₑ ^ 2
        ∂(pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) n (pinsWith a₀ x))
      ≤ ENNReal.ofReal (4 * n * Real.exp (V.M + V.M' + κ₀ * V.γ) / ((n + 1 : ℕ) : ℝ) ^ 2
            * ∫ z, V.q x z ^ 2 * Real.exp (-((κ₀ / ((n + 1 : ℕ) : ℝ)) * V.q z x)) ∂μ)
        + 2 * ‖(n / ((n + 1 : ℕ) : ℝ)) * ∫ z, V.q x z
            ∂((pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) n (pinsWith a₀ x)).map (fun y => y ⟨0, hn⟩)) - h‖ₑ ^ 2 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hNr0 : 0 < Nr := by positivity
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  set lam : ℝ := κ₀ / Nr with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hκ₀.le hNr0.le
  have hlam0 : 0 < lam := div_pos hκ₀ hNr0
  set D : ℝ := Real.exp (V.M + V.M' + κ₀ * V.γ) with hD
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  set P' := pinnedLaw V lam n (pinsWith a₀ x) with hP'
  have hP'prob : IsProbabilityMeasure P' := isProb_pinnedLaw V hlam n (pinsWith a₀ x)
  set π : Measure E := P'.map (fun y => y ⟨0, hn⟩) with hπ
  have hqx : Measurable (V.q x) := V.measurable_q.comp (measurable_const.prodMk measurable_id)
  have hqm : ∀ k : Fin n, Measurable fun y : Fin n → E => V.q x (y k) :=
    fun k => hqx.comp (measurable_pi_apply k)
  set Y : (Fin n → E) → ℝ := fun y => ∑ k, V.q x (y k) with hY
  have hYm : Measurable Y := Finset.measurable_sum _ fun k _ => hqm k
  set Z : (Fin n → E) → ℝ := fun y => (1 / Nr) * Y y - h with hZ
  have hZm : Measurable Z := (hYm.const_mul _).sub_const _
  -- the marginal bound
  have hπle := pinned_marginal_le_decay V hκ₀.le (N := n + 1) (n := n) hN0
    (by simp) a₀ x ⟨0, hn⟩
  have hπle' : π ≤ μ.withDensity (fun z => ENNReal.ofReal (D * Real.exp (-(lam * V.q z x)))) := hπle
  -- Step A
  have hA : ∫⁻ y, ‖Z y‖ₑ ^ 2 ∂P' ≤ 2 * evariance Z P' + 2 * ‖∫ y, Z y ∂P'‖ₑ ^ 2 := by
    calc ∫⁻ y, ‖Z y‖ₑ ^ 2 ∂P'
        ≤ ∫⁻ y, (2 * ‖Z y - ∫ y, Z y ∂P'‖ₑ ^ 2 + 2 * ‖∫ y, Z y ∂P'‖ₑ ^ 2) ∂P' :=
          lintegral_mono fun y => enorm_sq_le _ _
      _ = 2 * ∫⁻ y, ‖Z y - ∫ y, Z y ∂P'‖ₑ ^ 2 ∂P' + 2 * ‖∫ y, Z y ∂P'‖ₑ ^ 2 := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
            lintegral_const, measure_univ, mul_one]
      _ = _ := rfl
  -- Step C: evariance of Z
  have hC : evariance Z P' = ENNReal.ofReal ((1 / Nr) ^ 2) * evariance Y P' := by
    have : Z = fun y => (1 / Nr) * Y y + (-h) := funext fun y => by simp only [hZ]; ring
    rw [this, evariance_add_const' _ ((hYm.const_mul _).aestronglyMeasurable), evariance_mul]
  -- Step D: Wu linear
  have hD' : evariance Y P' ≤ 2 * n * evariance (V.q x) π := by
    have h1 := weak_linear_variance_symm V hκ₀.le hN0 (n := n) (N := n + 1) (B := Option Empty)
      (by simp [Fintype.card_option]) (pinsWith a₀ x) hκ (V.q x) hqx
    have h0 : P'.map (fun y => y ⟨0, hn⟩) = P'.map (fun y => y (0 : Fin n)) :=
      marginal_symm V hlam (pinsWith a₀ x) ⟨0, hn⟩ 0
    rw [hπ, h0]
    exact h1
  -- Step E: second moment of q under the marginal
  have hQ : evariance (V.q x) π ≤ ENNReal.ofReal (D * ∫ z, V.q x z ^ 2 * Real.exp (-(lam * V.q z x)) ∂μ) := by
    refine (evariance_le_lintegral_sub π hqx.aestronglyMeasurable 0).trans ?_
    have hgm : Measurable fun z => ENNReal.ofReal (D * Real.exp (-(lam * V.q z x))) := by
      refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp ?_))
      exact (measurable_const.mul (V.measurable_q.comp (measurable_id.prodMk measurable_const))).neg
    have hfm : Measurable fun z => ‖V.q x z - 0‖ₑ ^ 2 := ((hqx.sub_const 0).enorm).pow_const 2
    have hint : Integrable (fun z => D * (V.q x z ^ 2 * Real.exp (-(lam * V.q z x)))) μ := by
      refine Integrable.of_bound ?_ (D * (2 / lam * Real.exp (-1)) ^ 2) (Filter.Eventually.of_forall fun z => ?_)
      · exact (measurable_const.mul ((hqx.pow_const 2).mul (Real.measurable_exp.comp
          ((measurable_const.mul (V.measurable_q.comp (measurable_id.prodMk measurable_const))).neg)))).aestronglyMeasurable
      · have hq0 := V.q_nonneg x z
        have := sq_mul_exp_le hq0 hlam0
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := Real.exp_pos (-(lam * V.q z x)); positivity)]
        have e : V.q z x = V.q x z := V.q_symm _ _
        rw [e]
        exact mul_le_mul_of_nonneg_left this hD0
    calc ∫⁻ z, ‖V.q x z - 0‖ₑ ^ 2 ∂π
        ≤ ∫⁻ z, ‖V.q x z - 0‖ₑ ^ 2 ∂(μ.withDensity (fun z => ENNReal.ofReal (D * Real.exp (-(lam * V.q z x))))) :=
          lintegral_mono' hπle' le_rfl
      _ = ∫⁻ z, ENNReal.ofReal (D * Real.exp (-(lam * V.q z x))) * ‖V.q x z - 0‖ₑ ^ 2 ∂μ :=
          lintegral_withDensity_eq_lintegral_mul _ hgm hfm
      _ = ∫⁻ z, ENNReal.ofReal (D * (V.q x z ^ 2 * Real.exp (-(lam * V.q z x)))) ∂μ := by
          refine lintegral_congr fun z => ?_
          rw [sub_zero, enorm_sq_eq, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
      _ = ENNReal.ofReal (∫ z, D * (V.q x z ^ 2 * Real.exp (-(lam * V.q z x))) ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => by
            have := Real.exp_pos (-(lam * V.q z x)); positivity)).symm
      _ = _ := by rw [integral_const_mul]
  -- the mean
  have hπD : π ≤ ENNReal.ofReal D • μ := by
    refine hπle'.trans ?_
    rw [← withDensity_const]
    refine withDensity_mono (Filter.Eventually.of_forall fun z => ENNReal.ofReal_le_ofReal ?_)
    have : Real.exp (-(lam * V.q z x)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := mul_nonneg hlam (V.q_nonneg z x); linarith)
    nlinarith
  have hqπ : Integrable (V.q x) π :=
    (integral_le_of_le_smul hD0 hπD (fun z => V.q_nonneg x z) (V.integrable_q x)).1
  have hπk : ∀ k : Fin n, P'.map (fun y => y k) = π := fun k => marginal_symm V hlam _ k ⟨0, hn⟩
  have hint : ∀ k : Fin n, Integrable (fun y : Fin n → E => V.q x (y k)) P' := by
    intro k
    have h1 := hqπ
    rw [← hπk k] at h1
    exact (integrable_map_measure hqx.aestronglyMeasurable (measurable_pi_apply k).aemeasurable).1 h1
  have hmean : ∫ y, Z y ∂P' = (n / Nr) * ∫ z, V.q x z ∂π - h := by
    have e1 : ∫ y, Y y ∂P' = n * ∫ z, V.q x z ∂π := by
      simp only [hY]
      rw [integral_finset_sum _ fun k _ => hint k]
      have : ∀ k : Fin n, ∫ y, V.q x (y k) ∂P' = ∫ z, V.q x z ∂π := fun k => by
        rw [← hπk k, integral_map (measurable_pi_apply k).aemeasurable hqx.aestronglyMeasurable]
      rw [Finset.sum_congr rfl fun k _ => this k]
      simp
    have hYi : Integrable Y P' := by simp only [hY]; exact integrable_finset_sum _ fun k _ => hint k
    simp only [hZ]
    rw [integral_sub (hYi.const_mul _) (integrable_const _), integral_const_mul, e1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  -- assemble
  calc ∫⁻ y, ‖(1 / ((n + 1 : ℕ) : ℝ)) * ∑ k, V.q x (y k) - h‖ₑ ^ 2 ∂P'
      = ∫⁻ y, ‖Z y‖ₑ ^ 2 ∂P' := rfl
    _ ≤ 2 * evariance Z P' + 2 * ‖∫ y, Z y ∂P'‖ₑ ^ 2 := hA
    _ ≤ 2 * (ENNReal.ofReal ((1 / Nr) ^ 2) * (2 * n * ENNReal.ofReal (D * ∫ z, V.q x z ^ 2 * Real.exp (-(lam * V.q z x)) ∂μ)))
          + 2 * ‖∫ y, Z y ∂P'‖ₑ ^ 2 := by
        rw [hC]
        gcongr
        exact hD'.trans (mul_le_mul' le_rfl hQ)
    _ = _ := by
        rw [hmean]
        congr 1
        have hQ0 : 0 ≤ ∫ z, V.q x z ^ 2 * Real.exp (-(lam * V.q z x)) ∂μ :=
          integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
        have : (2 : ℝ≥0∞) * (ENNReal.ofReal ((1 / Nr) ^ 2) * (2 * (n : ℝ≥0∞) * ENNReal.ofReal (D * ∫ z, V.q x z ^ 2 * Real.exp (-(lam * V.q z x)) ∂μ)))
            = ENNReal.ofReal (2 * ((1 / Nr) ^ 2 * (2 * n * (D * ∫ z, V.q x z ^ 2 * Real.exp (-(lam * V.q z x)) ∂μ)))) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1 / Nr) ^ 2),
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * n)]
          simp [ENNReal.ofReal_natCast]
        rw [this]
        congr 1
        field_simp
        ring

end HRS.WeakRef.Abs

end WM_L

section WM_M
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {B : Type*} [Fintype B]

lemma measurable_pinWeight (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) (n : ℕ) :
    Measurable (pinWeight V lam a n) := by
  have hψ := isField_pinField V hlam a
  have h1 : pinWeight V lam a n = fun x =>
      fieldNorm V (pinField V lam a) lam n * ENNReal.ofReal (cavG V lam a n x)
        * ENNReal.ofReal (Real.exp (pinField V lam a x))
        * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹ := by
    funext x
    unfold pinWeight
    rw [fieldNorm_pin_eq V hlam a x n]
  rw [h1]
  have hpm : Measurable (pinField V lam a) := hψ.measurable
  exact (((measurable_const.mul (measurable_cavG V hlam a n).ennreal_ofReal).mul
    (Real.measurable_exp.comp hpm).ennreal_ofReal).mul measurable_const)

/-- The density of a marginal of the pinned ensemble is `≤ D` almost everywhere. -/
lemma pinWeight_le_ae (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + 1 + Fintype.card B ≤ N) (a : B → E) :
    ∀ᵐ x ∂μ, pinWeight V (β / N) a n x ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + β * V.γ)) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (measurable_pinWeight V hlam a n) ?_
  intro A hA _
  have h1 := marginal_self_succ V hlam a (n := n) 0
  have h2 := marginal_le V hβ hN0 hN a (0 : Fin (n + 1))
  rw [h1] at h2
  have := h2 A
  rw [withDensity_apply _ hA] at this
  rw [setLIntegral_const]
  simpa using this


lemma sum_erase_succAbove {n : ℕ} (i : Fin (n + 1)) (F : Fin (n + 1) → ℝ) :
    ∑ l ∈ Finset.univ.erase i, F l = ∑ k : Fin n, F (i.succAbove k) := by
  have h1 := Fin.sum_univ_succAbove F i
  have h2 := Finset.add_sum_erase Finset.univ F (Finset.mem_univ i)
  linarith

lemma msq_le {r θ hp H' Th γ Nr : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hθ : |θ| ≤ Th)
    (hH0 : 0 ≤ H') (hHa : H' ≤ γ) (hNr : 0 < Nr) :
    (r * θ + r * hp - H' / Nr) ^ 2 ≤ 3 * Th ^ 2 + 3 * hp ^ 2 + 3 * γ ^ 2 / Nr ^ 2 := by
  have h1 : (r * θ) ^ 2 ≤ Th ^ 2 := by
    have : |r * θ| ≤ Th := by
      rw [abs_mul, abs_of_nonneg hr0]
      calc r * |θ| ≤ 1 * Th := mul_le_mul hr1 hθ (abs_nonneg _) (by norm_num)
        _ = Th := one_mul _
    have := pow_le_pow_left₀ (abs_nonneg _) this 2
    rwa [sq_abs] at this
  have h2 : (r * hp) ^ 2 ≤ hp ^ 2 := by
    rw [mul_pow]
    have : r ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg hp]
  have h3 : (H' / Nr) ^ 2 ≤ γ ^ 2 / Nr ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hH0 hHa 2) (by positivity)
  have key : ∀ a b c : ℝ, (a + b - c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
    intro a b c; nlinarith [sq_nonneg (a - b), sq_nonneg (a + c), sq_nonneg (b + c)]
  have := key (r * θ) (r * hp) (H' / Nr)
  have e : 3 * γ ^ 2 / Nr ^ 2 = 3 * (γ ^ 2 / Nr ^ 2) := by ring
  rw [e]
  nlinarith

set_option maxHeartbeats 1600000 in
/-- Second moment of the single-coordinate fluctuation `g_i` under the full ensemble. -/
theorem second_moment_gi (V : WeakPotential μ) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) {n : ℕ} (hn : 0 < n)
    (hκ : weakKappa V κ₀ ≤ 1 / 2) (a₀ : Empty → E) (i : Fin (n + 1))
    {Qb Thb εf : ℝ}
    (hQb : ∀ x, ∫ z, V.q x z ^ 2 * Real.exp (-((κ₀ / ((n + 1 : ℕ) : ℝ)) * V.q z x)) ∂μ ≤ Qb)
    (hThb : ∀ (x : E) (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        ν₁ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + κ₀ * V.γ)) • μ →
        ν₂ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + κ₀ * V.γ)) • μ →
        (∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A|
          ≤ 2 * weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) →
        |∫ z, V.q x z ∂ν₁ - ∫ z, V.q x z ∂ν₂| ≤ Thb)
    (g : E → ℝ) (hgm : Measurable g) (hg : ∀ y, 0 ≤ g y ∧ g y ≤ Real.exp (V.M + V.M' + κ₀ * V.γ))
    (hgπ : (pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀).map (fun y => y i)
      = μ.withDensity (fun y => ENNReal.ofReal (g y)))
    (hgf : ∫ y, (g y - 1) ^ 2 ∂μ ≤ εf ^ 2) :
    ∫⁻ x, ‖(1 / ((n + 1 : ℕ) : ℝ)) * ∑ l ∈ Finset.univ.erase i, V.q (x i) (x l)
          - (∫ y, V.q (x i) y ∂μ)‖ₑ ^ 2
        ∂(pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀)
      ≤ ENNReal.ofReal (4 * n * Real.exp (V.M + V.M' + κ₀ * V.γ) / ((n + 1 : ℕ) : ℝ) ^ 2 * Qb
          + 6 * Thb ^ 2 + 6 * V.γ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2
          + 6 * Real.exp (V.M + V.M' + κ₀ * V.γ) * V.γ ^ 2 * εf ^ 2) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hNr0 : 0 < Nr := by positivity
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  set lam : ℝ := κ₀ / Nr with hlamdef
  have hlam : 0 ≤ lam := div_nonneg hκ₀.le hNr0.le
  set D : ℝ := Real.exp (V.M + V.M' + κ₀ * V.γ) with hD
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  set P := pinnedLaw V lam (n + 1) a₀ with hP
  have hPprob : IsProbabilityMeasure P := isProb_pinnedLaw V hlam (n + 1) a₀
  set H : E → ℝ := fun x => ∫ y, V.q x y ∂μ with hH
  have hHm : Measurable H := measurable_rowInt_meas V μ
  have hH0 : ∀ x, 0 ≤ H x := fun x => integral_nonneg fun y => V.q_nonneg x y
  have hHa : ∀ x, H x ≤ V.γ := fun x => V.row_le x
  have hγ0 := V.γ_nonneg
  set π : Measure E := P.map (fun y => y i) with hπ
  have hqx : ∀ x, Measurable (V.q x) := fun x =>
    V.measurable_q.comp (measurable_const.prodMk measurable_id)
  -- Step 1: disintegration over the value of coordinate `i`
  set Φ : E → (Fin n → E) → ℝ≥0∞ := fun x y =>
    ‖(1 / Nr) * ∑ k, V.q x (y k) - H x‖ₑ ^ 2 with hΦ
  have hΦm : Measurable fun p : E × (Fin n → E) => Φ p.1 p.2 := by
    refine (Measurable.enorm ?_).pow_const 2
    refine (measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)).sub (hHm.comp measurable_fst)
    exact V.measurable_q.comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))
  have e1 : ∀ X : Fin (n + 1) → E, ‖(1 / Nr) * ∑ l ∈ Finset.univ.erase i, V.q (X i) (X l)
        - (∫ y, V.q (X i) y ∂μ)‖ₑ ^ 2 = Φ (X i) (fun k => X (i.succAbove k)) := by
    intro X
    simp only [hΦ, hH]
    rw [sum_erase_succAbove i (fun l => V.q (X i) (X l))]
  simp_rw [e1]
  rw [lintegral_pinned_succ V hlam a₀ i Φ hΦm]
  -- the field of the full marginal
  set Hπ : E → ℝ := fun x => ∫ z, V.q x z ∂π with hHπdef
  have hHπ : ∀ x, Hπ x = ∫ z, V.q x z * g z ∂μ := by
    intro x
    simp only [hHπdef]
    rw [hgπ, integral_density hgm (fun y => (hg y).1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  have hDg : ∀ y, |g y - 1| ≤ D + 1 := fun y => by
    rw [abs_le]; constructor <;> linarith [(hg y).1, (hg y).2]
  have hHπH : ∀ x, Hπ x - H x = ∫ z, V.q x z * (g z - 1) ∂μ := by
    intro x
    rw [hHπ x]
    have h1 : Integrable (fun z => V.q x z * g z) μ :=
      Integrable.mono' ((V.integrable_q x).const_mul D) ((hqx x).mul hgm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (V.q_nonneg x z) (hg z).1), mul_comm]
          exact mul_le_mul_of_nonneg_right (hg z).2 (V.q_nonneg x z))
    simp only [hH, mul_sub, mul_one]
    rw [integral_sub h1 (V.integrable_q x)]
  have hSchur : ∫ x, (Hπ x - H x) ^ 2 ∂μ ≤ V.γ ^ 2 * εf ^ 2 := by
    simp_rw [hHπH]
    have hs := schur_sq (μ := μ) V.measurable_q V.q_nonneg V.q_symm hγ0 V.row_le V.integrable_q
      (hgm.sub_const 1) (C := D + 1) (by linarith) hDg
    refine hs.trans ?_
    exact mul_le_mul_of_nonneg_left hgf (sq_nonneg _)
  haveI : Nonempty E := Measure.nonempty_of_neZero μ
  obtain ⟨x₀⟩ := (inferInstance : Nonempty E)
  have hQb0 : 0 ≤ Qb := (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le).trans (hQb x₀)
  set c₁ : ℝ := 4 * n * D / Nr ^ 2 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hNrn : Nr = (n : ℝ) + 1 := by simp [hNr]
  have hπprob : IsProbabilityMeasure π := by rw [hπ]; infer_instance
  have hπD : π ≤ ENNReal.ofReal D • μ := by
    have := marginal_le V hκ₀.le hN0 (n := n + 1) (B := Empty) (by simp) a₀ i
    exact this
  have hx : ∀ x, ∫⁻ y, Φ x y ∂(pinnedLaw V lam n (pinsWith a₀ x))
      ≤ ENNReal.ofReal (c₁ * Qb) + ENNReal.ofReal (6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2)
        + 6 * ENNReal.ofReal ((Hπ x - H x) ^ 2) := by
    intro x
    have hcm := cond_moment V hκ₀ hn hκ a₀ x (H x)
    set πx : Measure E := (pinnedLaw V lam n (pinsWith a₀ x)).map (fun y => y ⟨0, hn⟩) with hπx
    have hπxprob : IsProbabilityMeasure πx := by
      have := isProb_pinnedLaw V hlam n (pinsWith a₀ x)
      rw [hπx]; infer_instance
    have hπxD : πx ≤ ENNReal.ofReal D • μ :=
      marginal_le V hκ₀.le hN0 (n := n) (B := Option Empty) (N := n + 1)
        (by simp [Fintype.card_option]) (pinsWith a₀ x) ⟨0, hn⟩
    have hTV : ∀ A, MeasurableSet A → |πx.real A - π.real A| ≤ 2 * weakKappa V κ₀ / Nr := by
      intro A hA
      have h1 := rvh_pin_comparison V hκ₀.le hN0 (n := n) (B := Empty) (by simp) a₀ hκ i ⟨0, hn⟩ x hA
      have hsym : (pinnedLaw V lam (n + 1) a₀).map (fun y => y (i.succAbove ⟨0, hn⟩))
          = π := marginal_symm V hlam a₀ _ i
      rw [hsym] at h1
      exact h1
    have hθ := hThb x πx π hπxprob hπprob hπxD hπD hTV
    have hMsq := msq_le (r := (n : ℝ) / Nr) (θ := ∫ z, V.q x z ∂πx - ∫ z, V.q x z ∂π)
      (hp := Hπ x - H x) (H' := H x) (Th := Thb) (γ := V.γ) (Nr := Nr)
      (by positivity) (by rw [div_le_one hNr0, hNrn]; linarith) hθ (hH0 x) (hHa x) hNr0
    have hMeq : (n : ℝ) / Nr * ∫ z, V.q x z ∂πx - H x
        = (n : ℝ) / Nr * (∫ z, V.q x z ∂πx - ∫ z, V.q x z ∂π) + (n : ℝ) / Nr * (Hπ x - H x)
          - H x / Nr := by
      have : Hπ x = ∫ z, V.q x z ∂π := rfl
      rw [this]
      field_simp
      rw [hNrn]; ring
    refine hcm.trans ?_
    have hA : ENNReal.ofReal (4 * n * D / Nr ^ 2 * ∫ z, V.q x z ^ 2 * Real.exp (-(lam * V.q z x)) ∂μ)
        ≤ ENNReal.ofReal (c₁ * Qb) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hQb x) hc₁0)
    have hB : 2 * ‖(n : ℝ) / Nr * ∫ z, V.q x z ∂πx - H x‖ₑ ^ 2
        ≤ ENNReal.ofReal (6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2) + 6 * ENNReal.ofReal ((Hπ x - H x) ^ 2) := by
      rw [enorm_sq_eq, hMeq]
      have h1 : ENNReal.ofReal (((n : ℝ) / Nr * (∫ z, V.q x z ∂πx - ∫ z, V.q x z ∂π)
          + (n : ℝ) / Nr * (Hπ x - H x) - H x / Nr) ^ 2)
          ≤ ENNReal.ofReal (3 * Thb ^ 2 + 3 * (Hπ x - H x) ^ 2 + 3 * V.γ ^ 2 / Nr ^ 2) :=
        ENNReal.ofReal_le_ofReal hMsq
      have hThb0 : 0 ≤ Thb := (abs_nonneg _).trans hθ
      calc 2 * ENNReal.ofReal _ ≤ 2 * ENNReal.ofReal (3 * Thb ^ 2 + 3 * (Hπ x - H x) ^ 2 + 3 * V.γ ^ 2 / Nr ^ 2) :=
            mul_le_mul' le_rfl h1
        _ = ENNReal.ofReal (6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2) + 6 * ENNReal.ofReal ((Hπ x - H x) ^ 2) := by
            have e : 2 * (3 * Thb ^ 2 + 3 * (Hπ x - H x) ^ 2 + 3 * V.γ ^ 2 / Nr ^ 2)
                = (6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2) + 6 * (Hπ x - H x) ^ 2 := by ring
            rw [show (2 : ℝ≥0∞) * ENNReal.ofReal (3 * Thb ^ 2 + 3 * (Hπ x - H x) ^ 2 + 3 * V.γ ^ 2 / Nr ^ 2)
                = ENNReal.ofReal (2 * (3 * Thb ^ 2 + 3 * (Hπ x - H x) ^ 2 + 3 * V.γ ^ 2 / Nr ^ 2)) by
              rw [ENNReal.ofReal_mul (by norm_num)]; simp, e,
              ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num)]
            simp
    calc _ ≤ ENNReal.ofReal (c₁ * Qb)
          + 2 * ‖(n : ℝ) / Nr * ∫ z, V.q x z ∂πx - H x‖ₑ ^ 2 := by
          gcongr
      _ ≤ ENNReal.ofReal (c₁ * Qb) + (ENNReal.ofReal (6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2)
          + 6 * ENNReal.ofReal ((Hπ x - H x) ^ 2)) := by gcongr
      _ = _ := by ring
  -- integrate against the density of coordinate `i`
  have hwm := measurable_pinWeight V hlam a₀ n
  have hwle := pinWeight_le_ae V hκ₀.le hN0 (n := n) (B := Empty) (by simp) a₀
  have hw1 : ∫⁻ x, pinWeight V lam a₀ n x ∂μ = 1 := lintegral_pinWeight V hlam a₀ i ⟨0, hn⟩
  -- measurability and boundedness of `Hπ - H`
  have hHπm : Measurable Hπ := by
    have : Hπ = fun x => ∫ z, V.q x z * g z ∂μ := funext hHπ
    rw [this]; exact measurable_rowInt' V.measurable_q hgm
  have hHπb : ∀ x, |Hπ x - H x| ≤ D * V.γ + V.γ := by
    intro x
    have h1 : 0 ≤ Hπ x := by rw [hHπ x]; exact integral_nonneg fun z => mul_nonneg (V.q_nonneg x z) (hg z).1
    have h2 : Hπ x ≤ D * V.γ := by
      rw [hHπ x]
      calc ∫ z, V.q x z * g z ∂μ ≤ ∫ z, D * V.q x z ∂μ :=
            integral_mono (Integrable.mono' ((V.integrable_q x).const_mul D) ((hqx x).mul hgm).aestronglyMeasurable
              (Filter.Eventually.of_forall fun z => by
                rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (V.q_nonneg x z) (hg z).1), mul_comm]
                exact mul_le_mul_of_nonneg_right (hg z).2 (V.q_nonneg x z)))
              ((V.integrable_q x).const_mul D) fun z => by
              have := mul_le_mul_of_nonneg_left (hg z).2 (V.q_nonneg x z)
              linarith [mul_comm (V.q x z) D]
        _ = D * ∫ z, V.q x z ∂μ := integral_const_mul _ _
        _ ≤ D * V.γ := mul_le_mul_of_nonneg_left (V.row_le x) hD0
    rw [abs_le]; constructor <;> linarith [hH0 x, hHa x]
  have hint : Integrable (fun x => (Hπ x - H x) ^ 2) μ := intg_sq_bdd (hHπm.sub hHm) hHπb
  have hlint : ∫⁻ x, ENNReal.ofReal ((Hπ x - H x) ^ 2) ∂μ = ENNReal.ofReal (∫ x, (Hπ x - H x) ^ 2 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  have hAm : Measurable fun x => ENNReal.ofReal ((Hπ x - H x) ^ 2) :=
    (((hHπm.sub hHm).pow_const 2)).ennreal_ofReal
  set A₀ : ℝ≥0∞ := ENNReal.ofReal (c₁ * Qb) + ENNReal.ofReal (6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2) with hA₀
  calc ∫⁻ x, pinWeight V lam a₀ n x * ∫⁻ y, Φ x y ∂(pinnedLaw V lam n (pinsWith a₀ x)) ∂μ
      ≤ ∫⁻ x, pinWeight V lam a₀ n x * (A₀ + 6 * ENNReal.ofReal ((Hπ x - H x) ^ 2)) ∂μ :=
        lintegral_mono fun x => mul_le_mul' le_rfl (hx x)
    _ = A₀ + 6 * ∫⁻ x, pinWeight V lam a₀ n x * ENNReal.ofReal ((Hπ x - H x) ^ 2) ∂μ := by
        have e : ∀ x, pinWeight V lam a₀ n x * (A₀ + 6 * ENNReal.ofReal ((Hπ x - H x) ^ 2))
            = pinWeight V lam a₀ n x * A₀ + 6 * (pinWeight V lam a₀ n x * ENNReal.ofReal ((Hπ x - H x) ^ 2)) := by
          intro x; ring
        simp_rw [e]
        rw [lintegral_add_left (f := fun x => pinWeight V lam a₀ n x * A₀) (hwm.mul measurable_const),
          lintegral_mul_const _ hwm, hw1, one_mul, lintegral_const_mul' 6 _ (by norm_num)]
    _ ≤ A₀ + 6 * (ENNReal.ofReal D * ∫⁻ x, ENNReal.ofReal ((Hπ x - H x) ^ 2) ∂μ) := by
        gcongr
        rw [← lintegral_const_mul _ hAm]
        refine lintegral_mono_ae ?_
        filter_upwards [hwle] with x hx'
        exact mul_le_mul' hx' le_rfl
    _ = A₀ + ENNReal.ofReal (6 * D * ∫ x, (Hπ x - H x) ^ 2 ∂μ) := by
        have hI0 : 0 ≤ ∫ x, (Hπ x - H x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
        rw [hlint, ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 6 * D), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]
        simp [mul_assoc]
    _ ≤ ENNReal.ofReal (4 * n * D / Nr ^ 2 * Qb + 6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2 + 6 * D * V.γ ^ 2 * εf ^ 2) := by
        have hThb0 : 0 ≤ Thb := by
          have := hThb x₀ π π hπprob hπprob hπD hπD (fun A hA => by
            rw [sub_self, abs_zero]
            exact div_nonneg (mul_nonneg (by norm_num) (weakKappa_nonneg V hκ₀.le)) hNr0.le)
          exact (abs_nonneg _).trans this
        have hI : 6 * D * ∫ x, (Hπ x - H x) ^ 2 ∂μ ≤ 6 * D * (V.γ ^ 2 * εf ^ 2) :=
          mul_le_mul_of_nonneg_left hSchur (by positivity)
        have hI0 : 0 ≤ ∫ x, (Hπ x - H x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
        have hp1 : 0 ≤ c₁ * Qb := mul_nonneg hc₁0 hQb0
        have hp2 : 0 ≤ 6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2 := by positivity
        rw [hA₀, ← ENNReal.ofReal_add hp1 hp2,
          ← ENNReal.ofReal_add (add_nonneg hp1 hp2) (mul_nonneg (by positivity) hI0)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hc₁]
        nlinarith

end HRS.WeakRef.Abs

end WM_M

section WM_N
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {B : Type*} [Fintype B]

/-- **Variance bound** (source `N:eq:pressure-variance`, abstract form). -/
theorem variance_G_le (V : WeakPotential μ) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) {n : ℕ} (hn : 0 < n)
    (hκ : weakKappa V κ₀ ≤ 1 / 2) (a₀ : Empty → E)
    {Qb Thb εf : ℝ}
    (hQb : ∀ x, ∫ z, V.q x z ^ 2 * Real.exp (-((κ₀ / ((n + 1 : ℕ) : ℝ)) * V.q z x)) ∂μ ≤ Qb)
    (hThb : ∀ (x : E) (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        ν₁ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + κ₀ * V.γ)) • μ →
        ν₂ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + κ₀ * V.γ)) • μ →
        (∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A|
          ≤ 2 * weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) →
        |∫ z, V.q x z ∂ν₁ - ∫ z, V.q x z ∂ν₂| ≤ Thb)
    (g : E → ℝ) (hgm : Measurable g) (hg : ∀ y, 0 ≤ g y ∧ g y ≤ Real.exp (V.M + V.M' + κ₀ * V.γ))
    (hgπ : (pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀).map (fun y => y ⟨0, Nat.succ_pos n⟩)
      = μ.withDensity (fun y => ENNReal.ofReal (g y)))
    (hgf : ∫ y, (g y - 1) ^ 2 ∂μ ≤ εf ^ 2)
    (G : (Fin (n + 1) → E) → ℝ)
    (hG : ∀ X, G X = (1 / ((n + 1 : ℕ) : ℝ)) * pairEnergy V X - ∑ k, ∫ y, V.q (X k) y ∂μ) :
    variance G (pinnedLaw V (κ₀ / ((n + 1 : ℕ) : ℝ)) (n + 1) a₀)
      ≤ 2 * ((n : ℝ) + 1) * (4 * n * Real.exp (V.M + V.M' + κ₀ * V.γ) / ((n + 1 : ℕ) : ℝ) ^ 2 * Qb
          + 6 * Thb ^ 2 + 6 * V.γ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2
          + 6 * Real.exp (V.M + V.M' + κ₀ * V.γ) * V.γ ^ 2 * εf ^ 2) := by
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hNr0 : 0 < Nr := by positivity
  have hlam : 0 ≤ κ₀ / Nr := div_nonneg hκ₀.le hNr0.le
  set D : ℝ := Real.exp (V.M + V.M' + κ₀ * V.γ) with hD
  set P := pinnedLaw V (κ₀ / Nr) (n + 1) a₀ with hP
  have hPprob : IsProbabilityMeasure P := isProb_pinnedLaw V hlam (n + 1) a₀
  set H : E → ℝ := fun x => ∫ y, V.q x y ∂μ with hH
  have hHm : Measurable H := measurable_rowInt_meas V μ
  set S : ℝ := 4 * n * D / Nr ^ 2 * Qb + 6 * Thb ^ 2 + 6 * V.γ ^ 2 / Nr ^ 2 + 6 * D * V.γ ^ 2 * εf ^ 2 with hS
  have hev := evariance_G_le V hκ₀.le hκ H hHm G hG
  haveI : Nonempty E := Measure.nonempty_of_neZero μ
  obtain ⟨x₀⟩ := (inferInstance : Nonempty E)
  have hQb0 : 0 ≤ Qb := (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le).trans (hQb x₀)
  have hS0 : 0 ≤ S := by
    have : 0 ≤ D := (Real.exp_pos _).le
    simp only [hS]; positivity
  have hterm : ∀ i : Fin (n + 1), ∫⁻ x, ‖(1 / Nr) * ∑ l ∈ Finset.univ.erase i, V.q (x i) (x l)
        - (∫ y, V.q (x i) y ∂μ)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal S := by
    intro i
    have hgi : P.map (fun y => y i) = μ.withDensity (fun y => ENNReal.ofReal (g y)) := by
      rw [← hgπ]; exact marginal_symm V hlam a₀ i ⟨0, Nat.succ_pos n⟩
    exact second_moment_gi V hκ₀ hn hκ a₀ i hQb hThb g hgm hg hgi hgf
  have hbound : evariance G P ≤ ENNReal.ofReal (2 * ((n : ℝ) + 1) * S) := by
    refine hev.trans ?_
    calc 2 * ∑ i : Fin (n + 1), ∫⁻ x, ‖(1 / Nr) * ∑ l ∈ Finset.univ.erase i, V.q (x i) (x l)
          - (∫ y, V.q (x i) y ∂μ)‖ₑ ^ 2 ∂P
        ≤ 2 * ∑ _i : Fin (n + 1), ENNReal.ofReal S :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hterm i)
      _ = ENNReal.ofReal (2 * ((n : ℝ) + 1) * S) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have e : ENNReal.ofReal (2 * ((n : ℝ) + 1)) = 2 * ((n : ℝ≥0∞) + 1) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by norm_num)]
            simp
          rw [ENNReal.ofReal_mul (by positivity), e]
          push_cast
          ring
  have hGm : Measurable G := by
    have : G = fun X => (1 / Nr) * pairEnergy V X - ∑ k, H (X k) := funext hG
    rw [this]
    exact (measurable_pairEnergy V |>.const_mul _).sub
      (Finset.measurable_sum _ fun k _ => hHm.comp (measurable_pi_apply k))
  have hlt : evariance G P < ⊤ := lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hmem : MemLp G 2 P := (evariance_lt_top_iff_memLp hGm.aestronglyMeasurable).1 hlt
  have h2 := hbound
  rw [← ofReal_variance hmem] at h2
  have hS2 : 0 ≤ 2 * ((n : ℝ) + 1) * S := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hS2).1 h2

end HRS.WeakRef.Abs

end WM_N

section WM_O
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

/-- ODE comparison: `ψ'' ≤ V` on `(0, β]` with `W' = V`, `W(0) = 0` gives `ψ(β) ≤ ψ(0) + β (ψ'(0) + W(β))`. -/
theorem ode_bound {ψ m v V W : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hψ : ∀ t, 0 < t → HasDerivAt ψ (m t) t) (hm : ∀ t, 0 < t → HasDerivAt m (v t) t)
    (hv : ∀ t ∈ Ioc 0 β, v t ≤ V t) (hV0 : ∀ t ∈ Ioc 0 β, 0 ≤ V t)
    (hW : ∀ t, 0 < t → HasDerivAt W (V t) t) (hWc : ContinuousWithinAt W (Ici 0) 0) (hW0 : W 0 = 0)
    (hψc : ContinuousWithinAt ψ (Ici 0) 0) (hmc : ContinuousWithinAt m (Ici 0) 0) :
    ψ β ≤ ψ 0 + β * (m 0 + W β) := by
  have hcontOn : ∀ f : ℝ → ℝ, (∀ t, 0 < t → ContinuousAt f t) → ContinuousWithinAt f (Ici 0) 0 →
      ContinuousOn f (Icc 0 β) := by
    intro f hf hf0 t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact hf0.mono Icc_subset_Ici_self
    · exact (hf t h).continuousWithinAt
  have hint : ∀ t ∈ interior (Icc 0 β), 0 < t ∧ t < β := fun t ht => by
    rw [interior_Icc] at ht; exact ht
  have hWc' := hcontOn W (fun t ht => (hW t ht).continuousAt) hWc
  have hmc' := hcontOn m (fun t ht => (hm t ht).continuousAt) hmc
  have hψc' := hcontOn ψ (fun t ht => (hψ t ht).continuousAt) hψc
  -- `W` is monotone on `[0, β]`
  have hWmono : MonotoneOn W (Icc 0 β) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 β) hWc'
      (fun t ht => (hW t (hint t ht).1).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [(hW t (hint t ht).1).deriv]
    exact hV0 t ⟨(hint t ht).1, (hint t ht).2.le⟩
  -- `m - W` is antitone on `[0, β]`
  have hk : AntitoneOn (fun t => m t - W t) (Icc 0 β) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 β) (hmc'.sub hWc')
      (fun t ht => ((hm t (hint t ht).1).sub (hW t (hint t ht).1)).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    have hd : HasDerivAt (fun t => m t - W t) (v t - V t) t :=
      (hm t (hint t ht).1).sub (hW t (hint t ht).1)
    rw [hd.deriv]
    have := hv t ⟨(hint t ht).1, (hint t ht).2.le⟩
    linarith
  have hmW : ∀ t ∈ Icc 0 β, m t ≤ m 0 + W β := by
    intro t ht
    have h1 := hk (show (0 : ℝ) ∈ Icc 0 β from ⟨le_rfl, hβ.le⟩) ht ht.1
    have h2 := hWmono ht (show β ∈ Icc 0 β from ⟨hβ.le, le_rfl⟩) ht.2
    simp only [hW0, sub_zero] at h1
    linarith
  -- `ψ - c t` is antitone
  have hh : AntitoneOn (fun t => ψ t - (m 0 + W β) * t) (Icc 0 β) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 β)
      (hψc'.sub (continuousOn_const.mul continuousOn_id))
      (fun t ht => ((hψ t (hint t ht).1).sub ((hasDerivAt_id t).const_mul _)).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    have hd : HasDerivAt (fun t => ψ t - (m 0 + W β) * t) (m t - (m 0 + W β)) t := by
      have := (hψ t (hint t ht).1).sub ((hasDerivAt_id t).const_mul (m 0 + W β))
      convert this using 1 <;> first | rfl | (simp; done) | (funext y; simp) | ring
    rw [hd.deriv]
    have := hmW t ⟨(hint t ht).1.le, (hint t ht).2.le⟩
    linarith
  have := hh (show (0 : ℝ) ∈ Icc 0 β from ⟨le_rfl, hβ.le⟩) (show β ∈ Icc 0 β from ⟨hβ.le, le_rfl⟩) hβ.le
  simp only [mul_zero, sub_zero] at this
  linarith


lemma moment_bound {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, -K ≤ g → ∀ s : ℝ, t / 2 ≤ s → s ≤ 2 * t →
      |g| ^ m * Real.exp (-(s * g)) ≤ C := by
  refine ⟨Real.exp (4 * K * t) * ((m.factorial : ℝ) * (2 / t) ^ m), by positivity, ?_⟩
  intro g hg s hs1 hs2
  set w : ℝ := g + 2 * K with hw
  have hw0 : 0 ≤ w := by linarith
  have hgw : |g| ≤ w := by
    rw [abs_le]; constructor <;> linarith
  have h1 : |g| ^ m ≤ w ^ m := pow_le_pow_left₀ (abs_nonneg _) hgw m
  have h2 : Real.exp (-(s * g)) ≤ Real.exp (4 * K * t) * Real.exp (-(t / 2 * w)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : -(s * g) = 2 * K * s - s * w := by rw [hw]; ring
    rw [this]
    nlinarith [mul_nonneg hK (by linarith : 0 ≤ t), mul_nonneg hw0 (by linarith : 0 ≤ s - t / 2)]
  have h3 : w ^ m * Real.exp (-(t / 2 * w)) ≤ (m.factorial : ℝ) * (2 / t) ^ m := by
    have := Real.pow_div_factorial_le_exp (t / 2 * w) (by positivity) m
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have h4 : (t / 2 * w) ^ m * Real.exp (-(t / 2 * w)) ≤ m.factorial := by
      have := (div_le_iff₀ hf).1 this
      calc (t / 2 * w) ^ m * Real.exp (-(t / 2 * w))
          ≤ (Real.exp (t / 2 * w) * m.factorial) * Real.exp (-(t / 2 * w)) :=
            mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        _ = m.factorial := by
            rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; simp
    have e : w ^ m * Real.exp (-(t / 2 * w)) = (2 / t) ^ m * ((t / 2 * w) ^ m * Real.exp (-(t / 2 * w))) := by
      rw [← mul_assoc, ← mul_pow]
      have : 2 / t * (t / 2 * w) = w := by field_simp
      rw [this]
    rw [e]
    nlinarith [pow_pos (show (0 : ℝ) < 2 / t by positivity) m]
  calc |g| ^ m * Real.exp (-(s * g)) ≤ w ^ m * (Real.exp (4 * K * t) * Real.exp (-(t / 2 * w))) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = Real.exp (4 * K * t) * (w ^ m * Real.exp (-(t / 2 * w))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le


lemma integrable_expMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG : Measurable G) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ω, -K ≤ G ω) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => G ω ^ k * Real.exp (-(t * G ω))) P := by
  obtain ⟨C, hC0, hC⟩ := moment_bound hK0 ht k
  refine Integrable.of_bound ((hG.pow_const k).mul (Real.measurable_exp.comp
    (measurable_const.mul hG).neg)).aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  exact hC (G ω) (hK ω) t (by linarith) (by linarith)

lemma hasDerivAt_expInt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {G : Ω → ℝ} (hG : Measurable G) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ω, -K ≤ G ω) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ ω, G ω ^ k * Real.exp (-(s * G ω)) ∂P)
      (-∫ ω, G ω ^ (k + 1) * Real.exp (-(t * G ω)) ∂P) t := by
  obtain ⟨C, hC0, hC⟩ := moment_bound hK0 ht (k + 1)
  have hmeas : ∀ s : ℝ, Measurable fun ω => G ω ^ k * Real.exp (-(s * G ω)) := fun s =>
    (hG.pow_const k).mul (Real.measurable_exp.comp (measurable_const.mul hG).neg)
  have hmeas' : ∀ s : ℝ, Measurable fun ω => -(G ω ^ (k + 1) * Real.exp (-(s * G ω))) := fun s =>
    ((hG.pow_const (k + 1)).mul (Real.measurable_exp.comp (measurable_const.mul hG).neg)).neg
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P) (𝕜 := ℝ)
    (F := fun s ω => G ω ^ k * Real.exp (-(s * G ω)))
    (F' := fun s ω => -(G ω ^ (k + 1) * Real.exp (-(s * G ω))))
    (bound := fun _ => C) (x₀ := t) (s := Metric.ball t (t / 2)) (Metric.ball_mem_nhds t (by linarith))
    (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
    (integrable_expMoment P hG hK0 hK k ht) (hmeas' t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω s hs => by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
      exact hC (G ω) (hK ω) s (by linarith) (by linarith))
    (integrable_const C)
    (Filter.Eventually.of_forall fun ω s hs => by
      have h1 : HasDerivAt (fun s : ℝ => -(s * G ω)) (-G ω) s := by
        have := ((hasDerivAt_id s).mul_const (G ω)).neg
        convert this using 1 <;> first | (funext y; simp) | simp
      have h2 := (h1.exp).const_mul (G ω ^ k)
      convert h2 using 1
      ring)
  have h := this.2
  rw [integral_neg] at h
  exact h


section LogPartition

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : Ω → ℝ)

/-- Moments `∫ G^k e^{-s G}`. -/
def expZ (k : ℕ) (s : ℝ) : ℝ := ∫ ω, G ω ^ k * Real.exp (-(s * G ω)) ∂P

def logZ (s : ℝ) : ℝ := Real.log (expZ P G 0 s)

def mFun (s : ℝ) : ℝ := -(expZ P G 1 s) / expZ P G 0 s

def vFun (s : ℝ) : ℝ := expZ P G 2 s / expZ P G 0 s - (expZ P G 1 s / expZ P G 0 s) ^ 2

variable [IsProbabilityMeasure P]

lemma expZ_zero_pos (hG : Measurable G) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ω, -K ≤ G ω) {t : ℝ} (ht : 0 < t) :
    0 < expZ P G 0 t := by
  unfold expZ
  have hi := integrable_expMoment P hG hK0 hK 0 ht
  simp only [pow_zero, one_mul] at hi ⊢
  exact (integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) hi).2 (by
    have : Function.support (fun ω => Real.exp (-(t * G ω))) = Set.univ :=
      Set.eq_univ_of_forall fun ω => (Real.exp_pos _).ne'
    rw [this]; simp)

lemma hasDerivAt_logZ (hG : Measurable G) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ω, -K ≤ G ω) {t : ℝ}
    (ht : 0 < t) : HasDerivAt (logZ P G) (mFun P G t) t := by
  have h0 := hasDerivAt_expInt P hG hK0 hK 0 ht
  have hp := expZ_zero_pos P G hG hK0 hK ht
  have h1 : HasDerivAt (expZ P G 0) (-expZ P G 1 t) t := h0
  have := h1.log hp.ne'
  unfold mFun logZ
  convert this using 1

lemma hasDerivAt_mFun (hG : Measurable G) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ω, -K ≤ G ω) {t : ℝ}
    (ht : 0 < t) : HasDerivAt (mFun P G) (vFun P G t) t := by
  have hp := expZ_zero_pos P G hG hK0 hK ht
  have h0 : HasDerivAt (expZ P G 0) (-expZ P G 1 t) t := hasDerivAt_expInt P hG hK0 hK 0 ht
  have h1 : HasDerivAt (expZ P G 1) (-expZ P G 2 t) t := hasDerivAt_expInt P hG hK0 hK 1 ht
  have := (h1.neg).div h0 hp.ne'
  unfold mFun vFun
  convert this using 1
  simp only [Pi.neg_apply]
  field_simp



lemma continuousWithinAt_expZ (hG : Measurable G) (hGi : Integrable G P) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ ω, -K ≤ G ω) {k : ℕ} (hk : k ≤ 1) :
    ContinuousWithinAt (expZ P G k) (Set.Ici 0) 0 := by
  have hint : Integrable (fun ω => (|G ω| + 1) * Real.exp K) P :=
    ((hGi.abs.add (integrable_const 1)).mul_const _)
  have hmeas : ∀ s : ℝ, Measurable fun ω => G ω ^ k * Real.exp (-(s * G ω)) := fun s =>
    (hG.pow_const k).mul (Real.measurable_exp.comp (measurable_const.mul hG).neg)
  unfold expZ
  refine continuousWithinAt_of_dominated (bound := fun ω => (|G ω| + 1) * Real.exp K)
    (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable) ?_ hint
    (Filter.Eventually.of_forall fun ω => ?_)
  · have : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ici 0), s < 1 :=
      (nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
    filter_upwards [this, self_mem_nhdsWithin] with s hs hs0
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-(s * G ω)) ≤ Real.exp K := by
      refine Real.exp_le_exp.2 ?_
      have := hK ω
      have hs0' : 0 ≤ s := hs0
      nlinarith
    have h2 : |G ω| ^ k ≤ |G ω| + 1 := by
      interval_cases k
      · simp
      · simp
    exact mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
  · refine Continuous.continuousWithinAt ?_
    fun_prop



lemma expZ_zero_zero : expZ P G 0 0 = 1 := by
  unfold expZ; simp

lemma expZ_one_zero : expZ P G 1 0 = ∫ ω, G ω ∂P := by
  unfold expZ; simp

/-- Upper bound for the log-partition function from a bound on the variance along the path. -/
theorem logZ_upper (hG : Measurable G) (hGi : Integrable G P) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ ω, -K ≤ G ω) {β : ℝ} (hβ : 0 < β) {V W : ℝ → ℝ}
    (hv : ∀ t ∈ Set.Ioc 0 β, vFun P G t ≤ V t) (hV0 : ∀ t ∈ Set.Ioc 0 β, 0 ≤ V t)
    (hW : ∀ t, 0 < t → HasDerivAt W (V t) t) (hWc : ContinuousWithinAt W (Set.Ici 0) 0) (hW0 : W 0 = 0) :
    logZ P G β ≤ β * (-(∫ ω, G ω ∂P) + W β) := by
  have h0 := continuousWithinAt_expZ P G hG hGi hK0 hK (k := 0) (by norm_num)
  have h1 := continuousWithinAt_expZ P G hG hGi hK0 hK (k := 1) le_rfl
  have hz : expZ P G 0 0 = 1 := expZ_zero_zero P G
  have hψc : ContinuousWithinAt (logZ P G) (Set.Ici 0) 0 := by
    unfold logZ
    refine ContinuousWithinAt.log h0 ?_
    rw [hz]; norm_num
  have hmc : ContinuousWithinAt (mFun P G) (Set.Ici 0) 0 := by
    unfold mFun
    refine ContinuousWithinAt.div h1.neg h0 ?_
    rw [hz]; norm_num
  have := ode_bound (ψ := logZ P G) (m := mFun P G) (v := vFun P G) (V := V) (W := W) hβ
    (fun t ht => hasDerivAt_logZ P G hG hK0 hK ht) (fun t ht => hasDerivAt_mFun P G hG hK0 hK ht)
    hv hV0 hW hWc hW0 hψc hmc
  have e1 : logZ P G 0 = 0 := by unfold logZ; rw [hz]; simp
  have e2 : mFun P G 0 = -(∫ ω, G ω ∂P) := by
    unfold mFun; rw [hz, expZ_one_zero]; simp
  rw [e1, e2] at this
  linarith

end LogPartition

end HRS.WeakRef

end WM_O

section WM_P
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ}

/-- `ψ₂(L)`: the order of `∫ min(w, L)²`. -/
def psi2 (d : ℕ) (s : ℝ) (L : ℝ) : ℝ :=
  if s < (d : ℝ) / 2 then 1
  else if s = (d : ℝ) / 2 then Real.log (Real.exp 1 * L)
  else L ^ (2 - (d : ℝ) / s)

lemma mul_deltaN_eq_psi2 (s : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * deltaN d s N = psi2 d s N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold deltaN psi2
  split_ifs with h1 h2
  · field_simp
  · field_simp
  · have : (2 : ℝ) - (d : ℝ) / s = 1 + (1 - (d : ℝ) / s) := by ring
    rw [this, Real.rpow_add hNpos, Real.rpow_one]

open HRS.KernelAux in
theorem kernel_levels_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ L : ℝ, 1 ≤ L →
      ∫⁻ z : Torus d, ENNReal.ofReal ((min (periodicRiesz d s z + cstar) L) ^ 2)
        ≤ ENNReal.ofReal (C₂ * psi2 d s L) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ0 := sigmaOf_pos hd hs0
  have hσd := sigmaOf_lt hd hsd
  obtain ⟨B, hB1, hB⟩ := riesz_envelope hd hs0 hsd cstar
  set w : Torus d → ℝ := fun z => periodicRiesz d s z + cstar with hwdef
  have hwB : ∀ y ∈ Box d, y ≠ 0 → w (boxPt y) ≤ B * (1 + ‖y‖ ^ (-(sigmaOf d s))) := hB
  have hw0 : ∀ y ∈ Box d, y ≠ 0 → 0 ≤ w (boxPt y) := fun y hy hy0 => by
    have := hw (boxPt y) (fun h => hy0 (boxPt_eq_zero hy h))
    simp only [hwdef]; linarith
  rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
  · have h2σ : 2 * sigmaOf d s < d := (two_sigmaOf_lt_iff hd hs0).2 h
    obtain ⟨C, hC, hlev⟩ := lev2a hd hσ0 hσd hB1 hwB hw0 h2σ
    refine ⟨C, hC, fun L hL => ?_⟩
    have : psi2 d s L = 1 := by unfold psi2; rw [if_pos h]
    rw [this, mul_one]
    exact hlev L hL
  · have hσ : sigmaOf d s = s := sigmaOf_eq hd (by rw [h])
    have h2σ : 2 * sigmaOf d s = d := by rw [hσ, h]; ring
    obtain ⟨C, hC, hlev⟩ := lev2b hd hσ0 hσd hB1 hwB hw0 h2σ
    refine ⟨C, hC, fun L hL => ?_⟩
    have : psi2 d s L = Real.log (Real.exp 1 * L) := by
      unfold psi2; rw [if_neg (not_lt.2 h.ge), if_pos h]
    rw [this]
    exact hlev L hL
  · have hσ : sigmaOf d s = s := sigmaOf_eq hd h.le
    have h2σ : (d : ℝ) < 2 * sigmaOf d s := by rw [hσ]; linarith
    obtain ⟨C, hC, hlev⟩ := lev2c hd hσ0 hσd hB1 hwB hw0 h2σ
    refine ⟨C, hC, fun L hL => ?_⟩
    have : psi2 d s L = L ^ (2 - (d : ℝ) / sigmaOf d s) := by
      unfold psi2; rw [if_neg (not_lt.2 h.le), if_neg h.ne', hσ]
    rw [this]
    exact hlev L hL


/-- Real-level row bounds of a kernel dominated by the Riesz envelope. -/
theorem row_bounds_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (cstar : ℝ)
    (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) (A Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧
      ∀ (ρ : Torus d → ℝ) [IsProbabilityMeasure (withDensityReal ρ)], (∀ x, ρ x ≤ Λ₀) →
        ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, 0 ≤ q x y) →
        (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) → ∀ x : Torus d,
          (∀ L : ℝ, 0 < L → ∫ y, max (q x y - L) 0 ∂(withDensityReal ρ)
              ≤ Ca * L ^ (1 - (d : ℝ) / sigmaOf d s)) ∧
          (∀ L : ℝ, 1 ≤ L → ∫ y, (min (q x y) L) ^ 2 ∂(withDensityReal ρ) ≤ Cb * psi2 d s L) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hlev1, -⟩ := kernel_levels hd hs0 hsd cstar hw
  obtain ⟨C₂', hC₂', hlev2⟩ := kernel_levels_real hd hs0 hsd cstar hw
  set Ā : ℝ := max A 1 with hĀ
  have hĀ1 : 1 ≤ Ā := le_max_right _ _
  have hĀ0 : 0 < Ā := by linarith
  have hAĀ : A ≤ Ā := le_max_left _ _
  set e : ℝ := 1 - (d : ℝ) / sigmaOf d s with he
  refine ⟨Λ₀ * Ā * C₁ * Ā ^ (-e), Λ₀ * Ā ^ 2 * C₂', by positivity, by positivity, ?_⟩
  intro ρ _ hρ q hqm hq0 hqA x
  set μ := withDensityReal ρ with hμ
  set w : Torus d → ℝ := fun z => periodicRiesz d s z + cstar with hwdef
  have hqx : Measurable (q x) := hqm.comp (measurable_const.prodMk measurable_id)
  have hae := ae_ne_withDensityReal hd ρ x
  have hpt : ∀ y, y ≠ x → q x y ≤ Ā * w (x - y) ∧ 0 ≤ w (x - y) := by
    intro y hy
    have h1 := hw (x - y) (sub_ne_zero.2 (Ne.symm hy))
    have h2 := hqA x y
    have h0 : 0 ≤ w (x - y) := by simp only [hwdef]; linarith
    refine ⟨h2.trans ?_, h0⟩
    exact mul_le_mul_of_nonneg_right hAĀ h0
  constructor
  · intro L hL
    have hnn : ∀ y, 0 ≤ max (q x y - L) 0 := fun y => le_max_right _ _
    have hm : Measurable fun y => max (q x y - L) 0 := (hqx.sub_const _).max measurable_const
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hm.aestronglyMeasurable]
    have hle : ∫⁻ y, ENNReal.ofReal (max (q x y - L) 0) ∂μ
        ≤ ENNReal.ofReal (Λ₀ * Ā * C₁ * (L / Ā) ^ e) := by
      calc ∫⁻ y, ENNReal.ofReal (max (q x y - L) 0) ∂μ
          ≤ ∫⁻ y, (ENNReal.ofReal Ā * ENNReal.ofReal (max (w (x - y) - L / Ā) 0)) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae] with y hy
            obtain ⟨h1, h0⟩ := hpt y hy
            rw [← ENNReal.ofReal_mul hĀ0.le]
            refine ENNReal.ofReal_le_ofReal (max_le ?_ (mul_nonneg hĀ0.le (le_max_right _ _)))
            have : Ā * (w (x - y) - L / Ā) ≤ Ā * max (w (x - y) - L / Ā) 0 :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) hĀ0.le
            have e2 : Ā * (w (x - y) - L / Ā) = Ā * w (x - y) - L := by field_simp
            linarith
        _ ≤ ENNReal.ofReal Λ₀ * ∫⁻ z, (ENNReal.ofReal Ā * ENNReal.ofReal (max (w z - L / Ā) 0)) :=
            KernelAux2.lintegral_conv_le ρ Λ₀ hρ
              (fun z => ENNReal.ofReal Ā * ENNReal.ofReal (max (w z - L / Ā) 0)) x
        _ = ENNReal.ofReal Λ₀ * (ENNReal.ofReal Ā * ∫⁻ z, ENNReal.ofReal (max (w z - L / Ā) 0)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal Λ₀ * (ENNReal.ofReal Ā * ENNReal.ofReal (C₁ * (L / Ā) ^ e)) := by
            gcongr
            exact hlev1 _ (by positivity)
        _ = _ := by
            rw [← ENNReal.ofReal_mul hĀ0.le, ← ENNReal.ofReal_mul hΛ₀]
            congr 1; ring
    have hbd : Λ₀ * Ā * C₁ * (L / Ā) ^ e = Λ₀ * Ā * C₁ * Ā ^ (-e) * L ^ e := by
      rw [Real.div_rpow hL.le hĀ0.le, Real.rpow_neg hĀ0.le, div_eq_mul_inv]; ring
    have hpos : 0 ≤ Λ₀ * Ā * C₁ * (L / Ā) ^ e := by positivity
    calc (∫⁻ y, ENNReal.ofReal (max (q x y - L) 0) ∂μ).toReal
        ≤ (ENNReal.ofReal (Λ₀ * Ā * C₁ * (L / Ā) ^ e)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = Λ₀ * Ā * C₁ * (L / Ā) ^ e := ENNReal.toReal_ofReal hpos
      _ = _ := hbd
  · intro L hL
    have hNpos : (0 : ℝ) < L := by linarith
    have hnn : ∀ y, 0 ≤ (min (q x y) L) ^ 2 := fun y => sq_nonneg _
    have hm : Measurable fun y => (min (q x y) L) ^ 2 := (hqx.min measurable_const).pow_const 2
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hm.aestronglyMeasurable]
    have hle : ∫⁻ y, ENNReal.ofReal ((min (q x y) L) ^ 2) ∂μ
        ≤ ENNReal.ofReal (Λ₀ * Ā ^ 2 * (C₂' * psi2 d s L)) := by
      calc ∫⁻ y, ENNReal.ofReal ((min (q x y) L) ^ 2) ∂μ
          ≤ ∫⁻ y, (ENNReal.ofReal (Ā ^ 2) * ENNReal.ofReal ((min (w (x - y)) L) ^ 2)) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae] with y hy
            obtain ⟨h1, h0⟩ := hpt y hy
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hq0' := hq0 x y
            have h2 : min (q x y) L ≤ Ā * min (w (x - y)) L := by
              rw [mul_min_of_nonneg _ _ hĀ0.le]
              exact le_min ((min_le_left _ _).trans h1)
                ((min_le_right _ _).trans (le_mul_of_one_le_left hNpos.le hĀ1))
            have h3 : 0 ≤ min (q x y) L := le_min hq0' hNpos.le
            have := pow_le_pow_left₀ h3 h2 2
            calc (min (q x y) L) ^ 2 ≤ (Ā * min (w (x - y)) L) ^ 2 := this
              _ = Ā ^ 2 * (min (w (x - y)) L) ^ 2 := by ring
        _ ≤ ENNReal.ofReal Λ₀ * ∫⁻ z, (ENNReal.ofReal (Ā ^ 2) * ENNReal.ofReal ((min (w z) L) ^ 2)) :=
            KernelAux2.lintegral_conv_le ρ Λ₀ hρ
              (fun z => ENNReal.ofReal (Ā ^ 2) * ENNReal.ofReal ((min (w z) L) ^ 2)) x
        _ = ENNReal.ofReal Λ₀ * (ENNReal.ofReal (Ā ^ 2) * ∫⁻ z, ENNReal.ofReal ((min (w z) L) ^ 2)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal Λ₀ * (ENNReal.ofReal (Ā ^ 2) * ENNReal.ofReal (C₂' * psi2 d s L)) := by
            gcongr
            exact hlev2 L hL
        _ = _ := by
            rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hΛ₀]
            congr 1; ring
    have hdel : 0 ≤ psi2 d s L := by
      unfold psi2
      split_ifs with h1 h2
      · norm_num
      · have := Real.log_nonneg (show (1 : ℝ) ≤ Real.exp 1 * L by
          have := Real.add_one_le_exp (1 : ℝ); nlinarith [Real.exp_pos 1])
        exact this
      · exact Real.rpow_nonneg hNpos.le _
    have hpos : 0 ≤ Λ₀ * Ā ^ 2 * (C₂' * psi2 d s L) := by positivity
    calc (∫⁻ y, ENNReal.ofReal ((min (q x y) L) ^ 2) ∂μ).toReal
        ≤ (ENNReal.ofReal (Λ₀ * Ā ^ 2 * (C₂' * psi2 d s L))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = Λ₀ * Ā ^ 2 * (C₂' * psi2 d s L) := ENNReal.toReal_ofReal hpos
      _ = Λ₀ * Ā ^ 2 * C₂' * psi2 d s L := by ring

end HRS.WeakRef

end WM_P

section WM_Q
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- Difference of the fields of two close measures: truncation at level `L`. -/
theorem theta_abstract {q : E → E → ℝ} (hqm : Measurable (Function.uncurry q))
    (hq0 : ∀ x y, 0 ≤ q x y) (hqi : ∀ x, Integrable (q x) μ) {L a₂ D ε₀ : ℝ} (hL : 0 ≤ L)
    (hrow2 : ∀ x, ∫ y, max (q x y - L) 0 ∂μ ≤ a₂) (hD : 0 ≤ D)
    (x : E) (ν₁ ν₂ : Measure E) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : ν₁ ≤ ENNReal.ofReal D • μ) (h₂ : ν₂ ≤ ENNReal.ofReal D • μ)
    (hTV : ∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A| ≤ ε₀) :
    |∫ y, q x y ∂ν₁ - ∫ y, q x y ∂ν₂| ≤ ε₀ * L + 2 * (D * a₂) := by
  have hqx : Measurable (q x) := hqm.comp (measurable_const.prodMk measurable_id)
  have hmin : Measurable fun y => min (q x y) L := hqx.min measurable_const
  have hmax : Measurable fun y => max (q x y - L) 0 := (hqx.sub_const L).max measurable_const
  have hmaxi : Integrable (fun y => max (q x y - L) 0) μ :=
    Integrable.mono' (hqi x) hmax.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [hq0 x y]) (hq0 x y))
  have hmini : ∀ ν : Measure E, IsProbabilityMeasure ν → Integrable (fun y => min (q x y) L) ν :=
    fun ν _ => intg_bdd hmin (C := L) fun y => by
      rw [abs_of_nonneg (le_min (hq0 x y) hL)]; exact min_le_right _ _
  have hsplit : ∀ (ν : Measure E) [IsProbabilityMeasure ν] (D' : ℝ), 0 ≤ D' → ν ≤ ENNReal.ofReal D' • μ →
      ∫ y, q x y ∂ν = ∫ y, min (q x y) L ∂ν + ∫ y, max (q x y - L) 0 ∂ν ∧
      0 ≤ ∫ y, max (q x y - L) 0 ∂ν ∧ ∫ y, max (q x y - L) 0 ∂ν ≤ D' * a₂ := by
    intro ν _ D' hD' hν
    have hi := integral_le_of_le_smul hD' hν (fun y => le_max_right _ _) hmaxi
    refine ⟨?_, integral_nonneg fun y => le_max_right _ _, ?_⟩
    · rw [← integral_add (hmini ν inferInstance) hi.1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      rcases le_total (q x y) L with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    · exact hi.2.trans (mul_le_mul_of_nonneg_left (hrow2 x) hD')
  obtain ⟨e₁, n₁, u₁⟩ := hsplit ν₁ D hD h₁
  obtain ⟨e₂, n₂, u₂⟩ := hsplit ν₂ D hD h₂
  have hosc : ∀ z z', |min (q x z) L - min (q x z') L| ≤ L := fun z z' => by
    rw [abs_le]
    have a1 := le_min (hq0 x z) hL
    have a2 := le_min (hq0 x z') hL
    have b1 := min_le_right (q x z) L
    have b2 := min_le_right (q x z') L
    constructor <;> linarith
  have hmain := abs_integral_sub_le_of_tv ν₁ ν₂ hL hTV hmin hosc
  rw [e₁, e₂]
  have : ∫ y, min (q x y) L ∂ν₁ + ∫ y, max (q x y - L) 0 ∂ν₁
      - (∫ y, min (q x y) L ∂ν₂ + ∫ y, max (q x y - L) 0 ∂ν₂)
      = (∫ y, min (q x y) L ∂ν₁ - ∫ y, min (q x y) L ∂ν₂)
        + (∫ y, max (q x y - L) 0 ∂ν₁ - ∫ y, max (q x y - L) 0 ∂ν₂) := by ring
  rw [this]
  calc |(∫ y, min (q x y) L ∂ν₁ - ∫ y, min (q x y) L ∂ν₂)
        + (∫ y, max (q x y - L) 0 ∂ν₁ - ∫ y, max (q x y - L) 0 ∂ν₂)|
      ≤ |∫ y, min (q x y) L ∂ν₁ - ∫ y, min (q x y) L ∂ν₂|
        + |∫ y, max (q x y - L) 0 ∂ν₁ - ∫ y, max (q x y - L) 0 ∂ν₂| := abs_add_le _ _
    _ ≤ ε₀ * L + 2 * (D * a₂) := by
        have h3 : |∫ y, max (q x y - L) 0 ∂ν₁ - ∫ y, max (q x y - L) 0 ∂ν₂| ≤ 2 * (D * a₂) := by
          rw [abs_le]; constructor <;> linarith
        linarith

end HRS.WeakRef.Abs

end WM_Q

section WM_R
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

/-- The energy `G = N F_N^q(·, μ)`. -/
def enG (q : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (N : ℕ) (X : Config d N) : ℝ :=
  N * modulatedEnergy q X μ

lemma WeakKernel.measurable_energy (h : WeakKernel μ a q) (N : ℕ) :
    Measurable (fun X : Config d N => modulatedEnergy q X μ) := by
  unfold modulatedEnergy
  have h1 : Measurable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => by
      have := h.meas.comp (f := fun X : Config d N => (X i, X j))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact this
  have h2 : Measurable (fun X : Config d N => ∑ i, ∫ y, q (X i) y ∂μ) :=
    Finset.measurable_sum _ fun i _ => h.measurable_rowInt.comp (measurable_pi_apply i)
  exact (((h1.const_mul _).sub (h2.const_mul _)).add_const _)

lemma WeakKernel.measurable_enG (h : WeakKernel μ a q) (N : ℕ) : Measurable (enG q μ N) :=
  (h.measurable_energy N).const_mul _

lemma WeakKernel.enG_ge (h : WeakKernel μ a q) (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N) (X : Config d N) :
    -((N : ℝ) * a) ≤ enG q μ N X := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold enG modulatedEnergy
  have h1 : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => h.nonneg _ _
  have h2 : ∑ i, ∫ y, q (X i) y ∂μ ≤ N * a := by
    have : ∀ i, ∫ y, q (X i) y ∂μ ≤ a := fun i => h.rowInt_le ha (X i)
    calc ∑ i, ∫ y, q (X i) y ∂μ ≤ ∑ _i : Fin N, a := Finset.sum_le_sum fun i _ => this i
      _ = N * a := by simp
  have h3 : 0 ≤ ∫ x, ∫ y, q x y ∂μ ∂μ :=
    integral_nonneg fun x => integral_nonneg fun y => h.nonneg _ _
  have h4 : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j) := by positivity
  have h5 : 1 / (N : ℝ) * ∑ i, ∫ y, q (X i) y ∂μ ≤ a := by
    calc 1 / (N : ℝ) * ∑ i, ∫ y, q (X i) y ∂μ ≤ 1 / (N : ℝ) * (N * a) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = a := by field_simp
  have : -a ≤ 1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)
      - 1 / (N : ℝ) * ∑ i, ∫ y, q (X i) y ∂μ + 1 / 2 * ∫ x, ∫ y, q x y ∂μ ∂μ := by linarith
  calc -((N : ℝ) * a) = N * (-a) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hN'.le

lemma WeakKernel.integral_enG (h : WeakKernel μ a q) {N : ℕ} (hN : 1 ≤ N) :
    ∫ X, enG q μ N X ∂(Measure.pi fun _ : Fin N => μ)
      = -(1 / 2) * ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) := by
  unfold enG
  rw [integral_const_mul, h.integral_energy hN]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

lemma WeakKernel.integrable_enG (h : WeakKernel μ a q) (N : ℕ) :
    Integrable (enG q μ N) (Measure.pi fun _ : Fin N => μ) :=
  (h.integrable_energy N).const_mul _

lemma WeakKernel.prod_le (h : WeakKernel μ a q) (ha : 0 ≤ a) :
    ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) ≤ a := by
  rw [integral_prod _ h.integrable_prod]
  calc ∫ x, ∫ y, q (x, y).1 (x, y).2 ∂μ ∂μ ≤ ∫ _x, a ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => integral_nonneg fun y => h.nonneg _ _)
          (integrable_const _) (Filter.Eventually.of_forall fun x => h.rowInt_le ha x)
    _ = a := by simp

lemma WeakKernel.prod_nonneg (h : WeakKernel μ a q) :
    0 ≤ ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) :=
  integral_nonneg fun p => h.nonneg _ _

lemma WeakKernel.pairPartition_eq (h : WeakKernel μ a q) (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) {N : ℕ}
    (hN : 0 < N) :
    pairPartition q N t μ
      = ENNReal.ofReal (expZ (Measure.pi fun _ : Fin N => μ) (enG q μ N) 0 t) := by
  have hK0 : 0 ≤ (N : ℝ) * a := by positivity
  have hi := integrable_expMoment (Measure.pi fun _ : Fin N => μ) (h.measurable_enG N) hK0
    (h.enG_ge ha hN) 0 ht
  unfold expZ pairPartition
  simp only [pow_zero, one_mul] at hi ⊢
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  refine lintegral_congr fun X => ?_
  unfold pairWeight enG
  congr 2
  ring

end HRS.WeakRef

end WM_R

section WM_S
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

lemma WeakKernel.integral_gibbs (h : WeakKernel μ a q) (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) {N : ℕ}
    (hN : 0 < N) (g : Config d N → ℝ) :
    ∫ X, g X ∂(pairGibbsLaw q N t μ)
      = ∫ X, (Real.exp (-(t * enG q μ N X)) / expZ (Measure.pi fun _ : Fin N => μ) (enG q μ N) 0 t) * g X
          ∂(Measure.pi fun _ : Fin N => μ) := by
  set Pm : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hPm
  set Z := expZ Pm (enG q μ N) 0 t with hZ
  have hK0 : 0 ≤ (N : ℝ) * a := by positivity
  have hZpos : 0 < Z := expZ_zero_pos Pm (enG q μ N) (h.measurable_enG N) hK0 (h.enG_ge ha hN) ht
  have hpp := h.pairPartition_eq ha ht hN
  unfold pairGibbsLaw
  rw [integral_withDensity_eq_integral_toReal_smul]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [smul_eq_mul]
    congr 1
    rw [hpp, ENNReal.toReal_div, ENNReal.toReal_ofReal hZpos.le]
    unfold pairWeight
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    simp only [enG]
    congr 3
    ring
  · exact (h.measurable_pairWeight N t).div_const _
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [hpp]
    refine ENNReal.div_lt_top ENNReal.ofReal_ne_top ?_
    exact (ENNReal.ofReal_pos.2 hZpos).ne'

lemma WeakKernel.vFun_eq (h : WeakKernel μ a q) (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) {N : ℕ}
    (hN : 0 < N) :
    vFun (Measure.pi fun _ : Fin N => μ) (enG q μ N) t
      = variance (enG q μ N) (pairGibbsLaw q N t μ) := by
  set Pm : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hPm
  set G := enG q μ N with hG
  set Z := expZ Pm G 0 t with hZ
  have hK0 : 0 ≤ (N : ℝ) * a := by positivity
  have hGm := h.measurable_enG N
  have hZpos : 0 < Z := expZ_zero_pos Pm G hGm hK0 (h.enG_ge ha hN) ht
  have hI := fun k => integrable_expMoment Pm hGm hK0 (h.enG_ge ha hN) k ht
  set E1 := expZ Pm G 1 t with hE1
  set E2 := expZ Pm G 2 t with hE2
  set m : ℝ := E1 / Z with hm
  have key := h.integral_gibbs ha ht hN G
  rw [← hG, ← hPm, ← hZ] at key
  have hmean : ∫ X, G X ∂(pairGibbsLaw q N t μ) = m := by
    rw [key]
    have : ∀ X, Real.exp (-(t * G X)) / Z * G X = (1 / Z) * (G X ^ 1 * Real.exp (-(t * G X))) := by
      intro X; ring
    simp_rw [this]
    rw [integral_const_mul]
    show 1 / Z * E1 = _
    rw [hm]; ring
  have key2 := h.integral_gibbs ha ht hN (fun X => (G X - m) ^ 2)
  rw [← hG, ← hPm, ← hZ] at key2
  rw [variance_eq_integral hGm.aemeasurable, hmean, key2]
  have e : ∀ X, Real.exp (-(t * G X)) / Z * (G X - m) ^ 2
      = (1 / Z) * (G X ^ 2 * Real.exp (-(t * G X))) - (2 * m / Z) * (G X ^ 1 * Real.exp (-(t * G X)))
        + (m ^ 2 / Z) * (G X ^ 0 * Real.exp (-(t * G X))) := by
    intro X; ring
  simp_rw [e]
  have i2 : Integrable (fun X => 1 / Z * (G X ^ 2 * Real.exp (-(t * G X)))) Pm := (hI 2).const_mul _
  have i1 : Integrable (fun X => 2 * m / Z * (G X ^ 1 * Real.exp (-(t * G X)))) Pm := (hI 1).const_mul _
  have i0 : Integrable (fun X => m ^ 2 / Z * (G X ^ 0 * Real.exp (-(t * G X)))) Pm := (hI 0).const_mul _
  have i21 : Integrable (fun X => 1 / Z * (G X ^ 2 * Real.exp (-(t * G X)))
      - 2 * m / Z * (G X ^ 1 * Real.exp (-(t * G X)))) Pm := i2.sub i1
  rw [integral_add i21 i0, integral_sub i2 i1, integral_const_mul, integral_const_mul,
    integral_const_mul]
  show E2 / Z - (E1 / Z) ^ 2 = 1 / Z * E2 - 2 * m / Z * E1 + m ^ 2 / Z * Z
  rw [← hm]
  have hE : E1 = m * Z := by rw [hm]; field_simp
  field_simp
  linear_combination (2 * m) * hE

end HRS.WeakRef

end WM_S

section WM_T
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}

theorem WeakKernel.pairPartition_upper (h : WeakKernel μ a q) (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N)
    {β : ℝ} (hβ : 0 < β) {V W : ℝ → ℝ}
    (hv : ∀ t ∈ Ioc 0 β, variance (enG q μ N) (pairGibbsLaw q N t μ) ≤ V t)
    (hV0 : ∀ t ∈ Ioc 0 β, 0 ≤ V t)
    (hW : ∀ t, 0 < t → HasDerivAt W (V t) t) (hWc : ContinuousWithinAt W (Ici 0) 0) (hW0 : W 0 = 0) :
    pairPartition q N β μ ≤ ENNReal.ofReal (Real.exp (β * (a / 2 + W β))) := by
  set Pm : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hPm
  have hK0 : 0 ≤ (N : ℝ) * a := by positivity
  have hlog := logZ_upper Pm (enG q μ N) (h.measurable_enG N) (h.integrable_enG N) hK0
    (h.enG_ge ha hN) hβ (V := V) (W := W)
    (fun t ht => by rw [h.vFun_eq ha ht.1 hN]; exact hv t ht) hV0 hW hWc hW0
  have hZpos : 0 < expZ Pm (enG q μ N) 0 β :=
    expZ_zero_pos Pm (enG q μ N) (h.measurable_enG N) hK0 (h.enG_ge ha hN) hβ
  rw [h.pairPartition_eq ha hβ hN]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : expZ Pm (enG q μ N) 0 β = Real.exp (logZ Pm (enG q μ N) β) := by
    unfold logZ; rw [Real.exp_log hZpos]
  rw [hexp]
  refine Real.exp_le_exp.2 (hlog.trans ?_)
  rw [h.integral_enG hN]
  have := h.prod_le ha
  have h0 := h.prod_nonneg
  have : β * (-(-(1 / 2) * ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ)) + W β)
      ≤ β * (a / 2 + W β) := by
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    linarith
  exact this

end HRS.WeakRef

end WM_T

section WM_U
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ}

lemma one_le_log_eL {L : ℝ} (hL : 1 ≤ L) : 1 ≤ Real.log (Real.exp 1 * L) := by
  have hLp : 0 < L := by linarith
  rw [Real.log_mul (Real.exp_pos 1).ne' hLp.ne', Real.log_exp]
  have := Real.log_nonneg hL
  linarith

lemma psi2_ge_one (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {L : ℝ} (hL : 1 ≤ L) : 1 ≤ psi2 d s L := by
  have hLp : 0 < L := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold psi2
  split_ifs with h1 h2
  · exact le_rfl
  · exact one_le_log_eL hL
  · push Not at h1
    have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne h1 (Ne.symm h2)
    have hs : 0 < s := by linarith
    have : 0 ≤ 2 - (d : ℝ) / s := by
      have : (d : ℝ) / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith
      linarith
    exact Real.one_le_rpow hL this

lemma deltaN_le_one (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : 1 ≤ N) : deltaN d s N ≤ 1 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold deltaN
  split_ifs with h1 h2
  · exact inv_le_one_of_one_le₀ hN'
  · rw [inv_mul_le_iff₀ hNpos, mul_one, Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
    have := Real.log_le_sub_one_of_pos hNpos
    linarith
  · push Not at h1
    have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne h1 (Ne.symm h2)
    have hs : 0 < s := by linarith
    have : 1 - (d : ℝ) / s ≤ 0 := by
      have : 1 ≤ (d : ℝ) / s := by
        rw [le_div_iff₀ hs]
        linarith
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hN' this


/-- `N^{2σ/d - 1} ≤ ψ₂(N)`, in the form used for the field-difference term. -/
lemma sq_rpow_le_psi2 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {N : ℝ} (hN : 1 ≤ N) :
    N * (N ^ (sigmaOf d s / d - 1)) ^ 2 ≤ psi2 d s N := by
  have hNp : 0 < N := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ0 := sigmaOf_pos hd hs0
  have e : N * (N ^ (sigmaOf d s / d - 1)) ^ 2 = N ^ (2 * sigmaOf d s / d - 1) := by
    have h1 : (N ^ (sigmaOf d s / d - 1)) ^ 2 = N ^ ((sigmaOf d s / d - 1) * 2) := by
      rw [Real.rpow_mul hNp.le]; norm_cast
    rw [h1]
    calc N * N ^ ((sigmaOf d s / d - 1) * 2) = N ^ (1 : ℝ) * N ^ ((sigmaOf d s / d - 1) * 2) := by
          rw [Real.rpow_one]
      _ = N ^ (1 + (sigmaOf d s / d - 1) * 2) := (Real.rpow_add hNp _ _).symm
      _ = _ := by congr 1; ring
  rw [e]
  unfold psi2
  split_ifs with h1 h2
  · have h2σ : 2 * sigmaOf d s < d := (two_sigmaOf_lt_iff hd hs0).2 h1
    have : 2 * sigmaOf d s / d - 1 ≤ 0 := by
      have : 2 * sigmaOf d s / d ≤ 1 := by rw [div_le_iff₀ hd0]; linarith
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hN this
  · have hσ : sigmaOf d s = s := sigmaOf_eq hd (by rw [h2])
    have : 2 * sigmaOf d s / d - 1 = 0 := by rw [hσ, h2]; field_simp; ring
    rw [this, Real.rpow_zero]
    exact one_le_log_eL hN
  · push Not at h1
    have hσ : sigmaOf d s = s := sigmaOf_eq hd h1
    rw [hσ]
    have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne h1 (Ne.symm h2)
    have hs : 0 < s := by linarith
    refine Real.rpow_le_rpow_of_exponent_le hN ?_
    -- 2 s/d - 1 ≤ 2 - d/s
    have key : 2 * s / d - 1 ≤ 2 - (d : ℝ) / s := by
      have e2 : 2 * s / d - 1 - (2 - (d : ℝ) / s) = (2 * s - d) * (s - d) / (d * s) := by
        field_simp
      have : (2 * s - d) * (s - d) / (d * s) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
          (by positivity)
      linarith
    exact key

end HRS.WeakRef

end WM_U

section WM_V
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ}

lemma exists_W_lt {s : ℝ} (h : s < (d : ℝ) / 2) {P : ℝ} (hP : 1 ≤ P) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ, 1 ≤ N → ∃ W : ℝ → ℝ,
      (∀ t, 0 < t → HasDerivAt W (psi2 d s (2 * N * P / t)) t) ∧
      ContinuousWithinAt W (Ici 0) 0 ∧ W 0 = 0 ∧
      ∀ β, 0 < β → β ≤ P → W β ≤ Cw * psi2 d s N := by
  refine ⟨P, by linarith, fun N hN => ⟨fun t => t, fun t ht => ?_, continuous_id.continuousWithinAt, rfl, ?_⟩⟩
  · have : psi2 d s (2 * N * P / t) = 1 := by unfold psi2; rw [if_pos h]
    rw [this]; exact hasDerivAt_id t
  · intro β hβ hβP
    have : psi2 d s N = 1 := by unfold psi2; rw [if_pos h]
    rw [this]; linarith

lemma exists_W_eq {s : ℝ} (h : s = (d : ℝ) / 2) {P βm : ℝ} (hP : 1 ≤ P) (hβm : 0 < βm) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ, 1 ≤ N → ∃ W : ℝ → ℝ,
      (∀ t, 0 < t → HasDerivAt W (psi2 d s (2 * N * P / t)) t) ∧
      ContinuousWithinAt W (Ici 0) 0 ∧ W 0 = 0 ∧
      ∀ β, βm ≤ β → β ≤ P → W β ≤ Cw * psi2 d s N := by
  set K0 : ℝ := 2 + Real.log (2 * P) + |Real.log βm| with hK0
  have hlogP : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
  have hK01 : 1 ≤ K0 := by have := abs_nonneg (Real.log βm); rw [hK0]; linarith
  refine ⟨P * K0, by positivity, fun N hN => ?_⟩
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hP0 : 0 < P := by linarith
  set c : ℝ := 2 * N * P with hc
  have hcp : 0 < c := by positivity
  have hpsi : ∀ t : ℝ, 0 < t → psi2 d s (c / t) = 1 + Real.log c - Real.log t := by
    intro t ht
    unfold psi2
    rw [if_neg (by rw [h]; exact lt_irrefl _), if_pos h, Real.log_mul (Real.exp_pos 1).ne' (by positivity),
      Real.log_exp, Real.log_div hcp.ne' ht.ne']
    ring
  refine ⟨fun t => t * (2 + Real.log c - Real.log t), fun t ht => ?_, ?_, ?_, ?_⟩
  · rw [hpsi t ht]
    have h1 : HasDerivAt (fun t : ℝ => 2 + Real.log c - Real.log t) (-(t⁻¹)) t := by
      have := (Real.hasDerivAt_log ht.ne').const_sub (2 + Real.log c)
      simpa using this
    have := (hasDerivAt_id t).mul h1
    refine (this : HasDerivAt (fun t : ℝ => t * (2 + Real.log c - Real.log t)) _ t).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  · have h1 : Continuous fun t : ℝ => t * (2 + Real.log c) - t * Real.log t :=
      (continuous_id.mul continuous_const).sub Real.continuous_mul_log
    refine h1.continuousWithinAt.congr (fun t _ => by ring) (by simp)
  · simp
  · intro β hβ hβP
    have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ
    have hlogβ : -Real.log β ≤ |Real.log βm| := by
      have : Real.log βm ≤ Real.log β := Real.log_le_log hβm hβ
      have h2 := neg_abs_le (Real.log βm)
      linarith
    have hlogc : Real.log c = Real.log (2 * P) + Real.log N := by
      rw [hc, mul_right_comm, Real.log_mul (by positivity) hNp.ne']
    have hψN : psi2 d s N = 1 + Real.log N := by
      unfold psi2
      rw [if_neg (by rw [h]; exact lt_irrefl _), if_pos h, Real.log_mul (Real.exp_pos 1).ne' hNp.ne', Real.log_exp]
    have hlN : 0 ≤ Real.log N := Real.log_nonneg hN'
    set B : ℝ := K0 + Real.log N with hB
    have hB0 : 0 ≤ B := by positivity
    have hbr : 2 + Real.log c - Real.log β ≤ B := by
      rw [hlogc, hB, hK0]; linarith
    calc β * (2 + Real.log c - Real.log β) ≤ β * B := mul_le_mul_of_nonneg_left hbr hβ0.le
      _ ≤ P * B := mul_le_mul_of_nonneg_right hβP hB0
      _ ≤ P * K0 * psi2 d s N := by
          rw [hψN, hB]
          have : K0 + Real.log N ≤ K0 * (1 + Real.log N) := by nlinarith
          nlinarith

lemma exists_W_gt {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {P : ℝ} (hP : 1 ≤ P) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ, 1 ≤ N → ∃ W : ℝ → ℝ,
      (∀ t, 0 < t → HasDerivAt W (psi2 d s (2 * N * P / t)) t) ∧
      ContinuousWithinAt W (Ici 0) 0 ∧ W 0 = 0 ∧
      ∀ β, 0 < β → β ≤ P → W β ≤ Cw * psi2 d s N := by
  have hd0 : (0 : ℝ) < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rcases this.lt_or_eq with h | h
    · exact h
    · rw [← h] at hs1 hsd; linarith
  have hs : 0 < s := by linarith
  set k : ℝ := 2 - (d : ℝ) / s with hk
  have hk0 : 0 < k := by
    have : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hs]; linarith
    linarith
  have hk1 : k < 1 := by
    have : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs]; linarith
    linarith
  have hP0 : 0 < P := by linarith
  refine ⟨(2 * P) ^ k * P ^ (1 - k) / (1 - k), by positivity, fun N hN => ?_⟩
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  set c : ℝ := 2 * N * P with hc
  have hcp : 0 < c := by positivity
  have hpsi : ∀ t : ℝ, 0 < t → psi2 d s (c / t) = c ^ k * t ^ (-k) := by
    intro t ht
    unfold psi2
    rw [if_neg (by push Not; exact hs1.le), if_neg hs1.ne', Real.div_rpow hcp.le ht.le, Real.rpow_neg ht.le,
      div_eq_mul_inv]
  have h1k : 0 < 1 - k := by linarith
  refine ⟨fun t => c ^ k / (1 - k) * t ^ (1 - k), fun t ht => ?_, ?_, ?_, ?_⟩
  · rw [hpsi t ht]
    have := (Real.hasDerivAt_rpow_const (x := t) (p := 1 - k) (Or.inl ht.ne')).const_mul (c ^ k / (1 - k))
    convert this using 1
    have : 1 - k - 1 = -k := by ring
    rw [this]
    field_simp
  · have : Continuous fun t : ℝ => c ^ k / (1 - k) * t ^ (1 - k) :=
      continuous_const.mul (Real.continuous_rpow_const h1k.le)
    exact this.continuousWithinAt
  · simp only [Real.zero_rpow h1k.ne', mul_zero]
  · intro β hβ hβP
    have hψN : psi2 d s N = N ^ k := by
      unfold psi2
      rw [if_neg (by push Not; exact hs1.le), if_neg hs1.ne']
    rw [hψN]
    have h2 : β ^ (1 - k) ≤ P ^ (1 - k) := Real.rpow_le_rpow hβ.le hβP h1k.le
    have h3 : c ^ k = (2 * P) ^ k * N ^ k := by
      rw [hc, mul_right_comm, Real.mul_rpow (by positivity) hNp.le]
    calc c ^ k / (1 - k) * β ^ (1 - k) ≤ c ^ k / (1 - k) * P ^ (1 - k) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 * P) ^ k * P ^ (1 - k) / (1 - k) * N ^ k := by rw [h3]; ring

end HRS.WeakRef

end WM_V

section WM_W
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef.Abs
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- The marginal of the full pinned law is dominated by `e^{M+M'+κ₀γ} μ`. -/
theorem pinned_marginal_le_const (V : WeakPotential μ) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) {n : ℕ} (hn : 0 < n)
    (i : Fin n) :
    (pinnedLaw V (κ₀ / n) n (fun e : Empty => e.elim)).map (fun y => y i)
      ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + κ₀ * V.γ)) • μ := by
  have hlam : 0 ≤ κ₀ / n := div_nonneg hκ₀ (Nat.cast_nonneg n)
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have := marginal_le_field V hψ hlam (n := n) (Λ := V.M' + κ₀ * V.γ)
    (by
      simp only [Fintype.card_empty, Nat.cast_zero, mul_zero, zero_mul, add_zero]
      have : κ₀ / n * n * V.γ = κ₀ * V.γ := by field_simp
      linarith)
    (fun _ => 0) (fun _ => le_rfl) (fun z => by simpa using hψ.le z) i
  have e : (fun z : E => ENNReal.ofReal (Real.exp (V.M + (V.M' + κ₀ * V.γ)) * Real.exp (-(0 : ℝ))))
      = fun _ : E => ENNReal.ofReal (Real.exp (V.M + V.M' + κ₀ * V.γ)) := by
    funext z; rw [neg_zero, Real.exp_zero, mul_one, add_assoc]
  rw [e, withDensity_const] at this
  exact this

/-- Clamping a density bounded by `D`. -/
theorem clamp_density {ν : Measure E} {f : E → ℝ≥0∞} (hf : Measurable f) (hν : ν = μ.withDensity f)
    {D : ℝ} (hD : 0 ≤ D) (hle : ν ≤ ENNReal.ofReal D • μ) :
    ∃ g : E → ℝ, Measurable g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ D) ∧
      ν = μ.withDensity (fun y => ENNReal.ofReal (g y)) ∧
      ∫ y, (g y - 1) ^ 2 ∂μ = ∫ y, ((f y).toReal - 1) ^ 2 ∂μ := by
  have hae : f ≤ᵐ[μ] fun _ => ENNReal.ofReal D := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf fun s hs _ => ?_
    rw [← withDensity_apply _ hs, ← hν, setLIntegral_const]
    have := hle s
    simpa [mul_comm] using this
  set g : E → ℝ := fun y => max 0 (min (f y).toReal D) with hg
  have hfm : Measurable fun y => (f y).toReal := hf.ennreal_toReal
  have hgm : Measurable g := measurable_const.max (hfm.min measurable_const)
  have hgeq : ∀ᵐ y ∂μ, g y = (f y).toReal := by
    filter_upwards [hae] with y hy
    have hlt : f y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
    have : (f y).toReal ≤ D := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
      rwa [ENNReal.toReal_ofReal hD] at this
    simp only [hg]
    rw [min_eq_left this, max_eq_right ENNReal.toReal_nonneg]
  refine ⟨g, hgm, fun y => ⟨le_max_left _ _, max_le hD (min_le_right _ _)⟩, ?_, ?_⟩
  · rw [hν]
    refine withDensity_congr_ae ?_
    filter_upwards [hgeq, hae] with y hy hy2
    rw [hy, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy2)]
  · refine integral_congr_ae ?_
    filter_upwards [hgeq] with y hy
    rw [hy]

end HRS.WeakRef.Abs

end WM_W

section WM_X
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

lemma sq_exp_le_min {x lam L : ℝ} (hx : 0 ≤ x) (hlam : 0 < lam) (hL : 2 ≤ lam * L) :
    x ^ 2 * Real.exp (-(lam * x)) ≤ (min x L) ^ 2 := by
  have hL0 : 0 ≤ L := by
    by_contra h
    push Not at h
    nlinarith
  rcases le_total x L with h | h
  · rw [min_eq_left h]
    have : Real.exp (-(lam * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [sq_nonneg x]
  · rw [min_eq_right h]
    have h1 : (lam * x) ^ 2 / 2 ≤ Real.exp (lam * x) := by
      have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ lam * x by positivity)
      nlinarith [sq_nonneg (lam * x)]
    have h2 : x ^ 2 * Real.exp (-(lam * x)) ≤ 2 / lam ^ 2 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      have : 2 / lam ^ 2 * Real.exp (lam * x) ≥ 2 / lam ^ 2 * ((lam * x) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have e : 2 / lam ^ 2 * ((lam * x) ^ 2 / 2) = x ^ 2 := by field_simp
      linarith
    have h3 : 2 / lam ^ 2 ≤ L ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith

lemma var_alg {Nr m D E a Qb Thb εf Cb pL c₁ pN Cm δ : ℝ} (hNr : Nr = m + 1) (hm : 0 ≤ m)
    (hD0 : 0 ≤ D) (hDE : D ≤ E) (hQb0 : 0 ≤ Qb) (hQb : Qb ≤ Cb * pL) (hCb : 0 ≤ Cb)
    (hTh : Nr * Thb ^ 2 ≤ c₁ * pN) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hNδ : Nr * δ = pN) (hpN : 1 ≤ pN) (hεf : εf = Cm * δ) (hc₁ : 0 ≤ c₁) (hCm : 0 ≤ Cm) :
    2 * (m + 1) * (4 * m * D / Nr ^ 2 * Qb + 6 * Thb ^ 2 + 6 * a ^ 2 / Nr ^ 2 + 6 * D * a ^ 2 * εf ^ 2)
      ≤ 8 * E * Cb * pL + (12 * c₁ + 12 + 12 * E * Cm ^ 2) * pN := by
  have hNr1 : 1 ≤ Nr := by linarith
  have hNrp : 0 < Nr := by linarith
  have hE0 : 0 ≤ E := hD0.trans hDE
  rw [← hNr]
  have hmN : m ≤ Nr := by linarith
  have t1 : 2 * Nr * (4 * m * D / Nr ^ 2 * Qb) ≤ 8 * E * (Cb * pL) := by
    have : 2 * Nr * (4 * m * D / Nr ^ 2 * Qb) = 8 * D * Qb * (m / Nr) := by field_simp; ring
    rw [this]
    have hr : m / Nr ≤ 1 := (div_le_one hNrp).2 hmN
    have hr0 : 0 ≤ m / Nr := by positivity
    calc 8 * D * Qb * (m / Nr) ≤ 8 * D * Qb * 1 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 8 * D * Qb := by ring
      _ ≤ 8 * E * (Cb * pL) := by
          have := mul_le_mul hDE hQb hQb0 hE0
          nlinarith
  have t2 : 2 * Nr * (6 * Thb ^ 2) ≤ 12 * (c₁ * pN) := by nlinarith
  have t3 : 2 * Nr * (6 * a ^ 2 / Nr ^ 2) ≤ 12 * pN := by
    have : 2 * Nr * (6 * a ^ 2 / Nr ^ 2) = 12 * a ^ 2 / Nr := by field_simp; ring
    rw [this, div_le_iff₀ hNrp]
    have : a ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have t4 : 2 * Nr * (6 * D * a ^ 2 * εf ^ 2) ≤ 12 * E * Cm ^ 2 * pN := by
    rw [hεf, mul_pow]
    have h1 : a ^ 2 ≤ 1 := by nlinarith
    have h2 : δ ^ 2 ≤ δ := by nlinarith
    have h3 : D * a ^ 2 ≤ E := by nlinarith
    have : 2 * Nr * (6 * D * a ^ 2 * (Cm ^ 2 * δ ^ 2)) = 12 * (D * a ^ 2) * Cm ^ 2 * (Nr * δ ^ 2) := by ring
    rw [this]
    have h4 : Nr * δ ^ 2 ≤ pN := by rw [← hNδ]; nlinarith
    have h5 : 0 ≤ D * a ^ 2 := by positivity
    have h6 : 12 * (D * a ^ 2) * Cm ^ 2 ≤ 12 * E * Cm ^ 2 := by nlinarith [sq_nonneg Cm]
    exact mul_le_mul h6 h4 (by positivity) (by positivity)
  have e : 2 * Nr * (4 * m * D / Nr ^ 2 * Qb + 6 * Thb ^ 2 + 6 * a ^ 2 / Nr ^ 2 + 6 * D * a ^ 2 * εf ^ 2)
      = 2 * Nr * (4 * m * D / Nr ^ 2 * Qb) + 2 * Nr * (6 * Thb ^ 2) + 2 * Nr * (6 * a ^ 2 / Nr ^ 2)
        + 2 * Nr * (6 * D * a ^ 2 * εf ^ 2) := by ring
  rw [e]
  nlinarith

end HRS.WeakRef

end WM_X

section WM_Y
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef
open HRS.External

variable {d : ℕ}

set_option maxHeartbeats 800000 in
theorem variance_at (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Torus d → Torus d → ℝ}
    (hK : WeakKernel μ a q) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {Ca Cb Cm P E : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCm : 0 ≤ Cm) (hP : 1 ≤ P)
    (hE : E = Real.exp (2 * P))
    (hr1 : ∀ x, ∀ L : ℝ, 0 < L → ∫ y, max (q x y - L) 0 ∂μ ≤ Ca * L ^ (1 - (d : ℝ) / sigmaOf d s))
    (hr2 : ∀ x, ∀ L : ℝ, 1 ≤ L → ∫ y, (min (q x y) L) ^ 2 ∂μ ≤ Cb * psi2 d s L)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : 0 < t) (htP : t ≤ P) (hta : t * a ≤ 1 / (16 * E))
    (hmarg : ∃ f : Torus d → ℝ≥0∞,
      (pairGibbsLaw q N t μ).map (fun X => X ⟨0, by omega⟩) = μ.withDensity f ∧ Measurable f ∧
        ∫ x, ((f x).toReal - 1) ^ 2 ∂μ ≤ (Cm * deltaN d s N) ^ 2) :
    variance (enG q μ N) (pairGibbsLaw q N t μ)
      ≤ 8 * E * Cb * psi2 d s (2 * N * P / t)
        + (12 * (1 + 2 * E * Ca) ^ 2 + 12 + 12 * E * Cm ^ 2) * psi2 d s N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ0 := sigmaOf_pos hd hs0
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by linarith)
  have hE0 : 0 < E := by linarith
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN1R : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  set V := mkV hK ha0 ht.le with hV
  have hVM : V.M = t * a := rfl
  have hVM' : V.M' = 0 := rfl
  have hVγ : V.γ = a := rfl
  have hVq : V.q = q := rfl
  set D : ℝ := Real.exp (V.M + V.M' + t * V.γ) with hDdef
  have hta0 : 0 ≤ t * a := mul_nonneg ht.le ha0
  have hDe : D = Real.exp (t * a + t * a) := by
    simp only [hDdef, hVM, hVM', hVγ]; congr 1; ring
  have htaP : t * a ≤ P := by
    have : 1 / (16 * E) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hDE : D ≤ E := by
    rw [hDe, hE]; exact Real.exp_le_exp.2 (by linarith)
  have hD1 : 1 ≤ D := by rw [hDe]; exact Real.one_le_exp (by linarith)
  have hD0 : 0 ≤ D := by linarith
  have hκ : weakKappa V t ≤ 1 / 2 := by
    have : weakKappa V t = 4 * D * (t * a) := by
      simp only [weakKappa, hDdef, hVγ]
    rw [this]
    have h1 : D * (t * a) ≤ E * (1 / (16 * E)) := mul_le_mul hDE hta hta0 hE0.le
    have h2 : E * (1 / (16 * E)) = 1 / 16 := by field_simp
    linarith
  have hκ0 : 0 ≤ weakKappa V t := weakKappa_nonneg V ht.le
  rw [pairGibbsLaw_eq_pinnedLaw hK ha0 ht.le (Nat.succ_pos n)] at hmarg ⊢
  obtain ⟨f, hfmap, hfm, hfint⟩ := hmarg
  have hle := Abs.pinned_marginal_le_const V ht.le (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩
  obtain ⟨g, hgm, hg, hgπ, hgf⟩ := Abs.clamp_density hfm hfmap hD0 hle
  -- the energy and the centred version
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  set I₂ : ℝ := ∫ p : Torus d × Torus d, q p.1 p.2 ∂(μ.prod μ) with hI₂
  have hI₂' : ∫ x, ∫ y, q x y ∂μ ∂μ = I₂ := by
    rw [hI₂, integral_prod _ hK.integrable_prod]
  set G : Config d (n + 1) → ℝ := fun X => enG q μ (n + 1) X - Nr / 2 * I₂ with hGdef
  have hG : ∀ X, G X = (1 / Nr) * pairEnergy V X - ∑ k, ∫ y, V.q (X k) y ∂μ := by
    intro X
    simp only [hGdef, enG, modulatedEnergy, pairEnergy, hVq, hI₂']
    rw [← hNr]
    field_simp
    ring
  -- Qb
  set L : ℝ := 2 * Nr * P / t with hL
  have hLge : 2 * Nr ≤ L := by
    rw [hL, le_div_iff₀ ht]
    nlinarith
  have hL1 : 1 ≤ L := by linarith
  have hQb : ∀ x, ∫ z, V.q x z ^ 2 * Real.exp (-((t / Nr) * V.q z x)) ∂μ ≤ Cb * psi2 d s L := by
    intro x
    refine le_trans ?_ (hr2 x L hL1)
    have hqx : Measurable (q x) := hK.measurable_left x
    have hmin : Measurable fun y => (min (q x y) L) ^ 2 := (hqx.min measurable_const).pow_const 2
    have hint : Integrable (fun y => (min (q x y) L) ^ 2) μ :=
      Abs.intg_bdd hmin (C := L ^ 2) fun y => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h0 : 0 ≤ min (q x y) L := le_min (hK.nonneg x y) (by linarith)
        exact pow_le_pow_left₀ h0 (min_le_right _ _) 2
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_) hint
      (Filter.Eventually.of_forall fun z => ?_)
    · exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    · simp only [hVq]
      rw [hK.symm z x]
      refine sq_exp_le_min (hK.nonneg x z) (by positivity) ?_
      have : t / Nr * L = 2 * P := by rw [hL]; field_simp
      rw [this]; linarith
  -- Thb
  set σ := sigmaOf d s with hσ
  set Lp : ℝ := Nr ^ (σ / d) with hLp
  have hLp0 : 0 < Lp := Real.rpow_pos_of_pos hNR _
  have hexp1 : Lp / Nr = Nr ^ (σ / d - 1) := by
    rw [hLp, Real.rpow_sub hNR, Real.rpow_one]
  have hexp2 : Lp ^ (1 - (d : ℝ) / σ) = Nr ^ (σ / d - 1) := by
    rw [hLp, ← Real.rpow_mul hNR.le]
    congr 1
    field_simp
  have hThb : ∀ (x : Torus d) (ν₁ ν₂ : Measure (Torus d)), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      ν₁ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + t * V.γ)) • μ →
      ν₂ ≤ ENNReal.ofReal (Real.exp (V.M + V.M' + t * V.γ)) • μ →
      (∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A| ≤ 2 * weakKappa V t / Nr) →
      |∫ z, V.q x z ∂ν₁ - ∫ z, V.q x z ∂ν₂| ≤ (1 + 2 * E * Ca) * Nr ^ (σ / d - 1) := by
    intro x ν₁ ν₂ h1 h2 hν₁ hν₂ hTV
    have := Abs.theta_abstract (μ := μ) (q := q) hK.meas hK.nonneg hK.integrable_row (L := Lp)
      (a₂ := Ca * Lp ^ (1 - (d : ℝ) / σ)) (D := D) (ε₀ := 2 * weakKappa V t / Nr) hLp0.le
      (fun y => hr1 y Lp hLp0) hD0 x ν₁ ν₂ hν₁ hν₂ hTV
    refine this.trans ?_
    rw [hexp2]
    have e1 : 2 * weakKappa V t / Nr * Lp ≤ Nr ^ (σ / d - 1) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hNR]
      have : Nr ^ (σ / d - 1) * Nr = Lp := by
        rw [← hexp1]; field_simp
      rw [this]
      have : 2 * weakKappa V t ≤ 1 := by linarith
      nlinarith
    have e2 : 2 * (D * (Ca * Nr ^ (σ / d - 1))) ≤ 2 * E * Ca * Nr ^ (σ / d - 1) := by
      have h0 : 0 ≤ Nr ^ (σ / d - 1) := Real.rpow_nonneg hNR.le _
      have : D * (Ca * Nr ^ (σ / d - 1)) ≤ E * (Ca * Nr ^ (σ / d - 1)) :=
        mul_le_mul_of_nonneg_right hDE (by positivity)
      nlinarith
    nlinarith
  have hgf' : ∫ y, (g y - 1) ^ 2 ∂μ ≤ (Cm * deltaN d s (n + 1)) ^ 2 := by rw [hgf]; exact hfint
  have hvar := Abs.variance_G_le V ht hn hκ (fun e : Empty => e.elim) (Qb := Cb * psi2 d s L)
    (Thb := (1 + 2 * E * Ca) * Nr ^ (σ / d - 1)) (εf := Cm * deltaN d s (n + 1)) hQb hThb g hgm hg hgπ hgf' G hG
  have hGm : Measurable G := ((hK.measurable_enG (n + 1)).sub_const _)
  have hvc : variance (enG q μ (n + 1)) (pinnedLaw V (t / Nr) (n + 1) (fun e : Empty => e.elim))
      = variance G (pinnedLaw V (t / Nr) (n + 1) (fun e : Empty => e.elim)) := by
    have hP : IsProbabilityMeasure (pinnedLaw V (t / Nr) (n + 1) (fun e : Empty => e.elim)) :=
      isProb_pinnedLaw V (div_nonneg ht.le hNR.le) _ _
    have := variance_add_const hGm.aestronglyMeasurable (Nr / 2 * I₂)
      (μ := pinnedLaw V (t / Nr) (n + 1) (fun e : Empty => e.elim))
    have e : (fun ω => G ω + Nr / 2 * I₂) = enG q μ (n + 1) := by
      funext X; simp only [hGdef]; ring
    rw [e] at this
    exact this
  rw [hvc]
  refine hvar.trans ?_
  -- arithmetic
  have hδ0 := deltaN_nonneg (d := d) s (show 1 ≤ n + 1 by omega)
  have hδ1 := deltaN_le_one hd hs0 hsd (show 1 ≤ n + 1 by omega)
  have hNδ := mul_deltaN_eq_psi2 (d := d) s (show 1 ≤ n + 1 by omega)
  have hpN := psi2_ge_one hd hs0 hN1R
  have hTh : Nr * ((1 + 2 * E * Ca) * Nr ^ (σ / d - 1)) ^ 2 ≤ (1 + 2 * E * Ca) ^ 2 * psi2 d s Nr := by
    have := sq_rpow_le_psi2 hd hs0 hsd hN1R
    rw [mul_pow]
    have h2 : 0 ≤ (1 + 2 * E * Ca) ^ 2 := sq_nonneg _
    calc Nr * ((1 + 2 * E * Ca) ^ 2 * (Nr ^ (σ / d - 1)) ^ 2)
        = (1 + 2 * E * Ca) ^ 2 * (Nr * (Nr ^ (σ / d - 1)) ^ 2) := by ring
      _ ≤ (1 + 2 * E * Ca) ^ 2 * psi2 d s Nr := mul_le_mul_of_nonneg_left this h2
  have hQb0 : 0 ≤ Cb * psi2 d s L := mul_nonneg hCb (by linarith [psi2_ge_one hd hs0 hL1])
  have := var_alg (Nr := Nr) (m := (n : ℝ)) (D := D) (E := E) (a := a) (Qb := Cb * psi2 d s L)
    (Thb := (1 + 2 * E * Ca) * Nr ^ (σ / d - 1)) (εf := Cm * deltaN d s (n + 1)) (Cb := Cb)
    (pL := psi2 d s L) (c₁ := (1 + 2 * E * Ca) ^ 2) (pN := psi2 d s Nr) (Cm := Cm)
    (δ := deltaN d s (n + 1)) (by rw [hNr]; push_cast; ring) (Nat.cast_nonneg n) hD0 hDE hQb0 le_rfl hCb
    hTh ha0 ha1 hδ0 hδ1 hNδ hpN rfl (sq_nonneg _) hCm
  exact this

end HRS.WeakRef

end WM_Y

section WM_Z
open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal BigOperators
set_option linter.unusedSectionVars false

namespace HRS.WeakRef

variable {d : ℕ}

lemma exists_W (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {P βm : ℝ} (hP : 1 ≤ P) (hβm : 0 < βm) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ, 1 ≤ N → ∃ W : ℝ → ℝ,
      (∀ t, 0 < t → HasDerivAt W (psi2 d s (2 * N * P / t)) t) ∧
      ContinuousWithinAt W (Ici 0) 0 ∧ W 0 = 0 ∧
      ∀ β, βm ≤ β → β ≤ P → W β ≤ Cw * psi2 d s N := by
  rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
  · obtain ⟨Cw, hC, H⟩ := exists_W_lt (d := d) h hP
    refine ⟨Cw, hC, fun N hN => ?_⟩
    obtain ⟨W, h1, h2, h3, h4⟩ := H N hN
    exact ⟨W, h1, h2, h3, fun β hβ hβP => h4 β (lt_of_lt_of_le hβm hβ) hβP⟩
  · exact exists_W_eq (d := d) h hP hβm
  · obtain ⟨Cw, hC, H⟩ := exists_W_gt (d := d) h hsd hP
    refine ⟨Cw, hC, fun N hN => ?_⟩
    obtain ⟨W, h1, h2, h3, h4⟩ := H N hN
    exact ⟨W, h1, h2, h3, fun β hβ hβP => h4 β (lt_of_lt_of_le hβm hβ) hβP⟩

end HRS.WeakRef
end WM_Z

namespace HRS

variable {d : ℕ}
set_option maxHeartbeats 1600000 in
/-- Strong form of the marginal bound `N:eq:weak-marginal` (real-valued `L²` integral, with a measurable
bounded density), proved by the cavity formula, the Laplace residual, the `L²` convolution estimate and the
Schur contraction (source lines 6206-6268). -/
theorem weak_marginal_strong (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ [IsProbabilityMeasure (withDensityReal ρ)],
        Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ β ∈ Set.Icc βm βp, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ∃ f : Torus d → ℝ≥0∞,
          (pairGibbsLaw q N (τ * β) (withDensityReal ρ)).map (fun X => X ⟨0, by omega⟩)
            = (withDensityReal ρ).withDensity f ∧ Measurable f ∧ (∃ K : ℝ, ∀ x, (f x).toReal ≤ K) ∧
          ∫ x, ((f x).toReal - 1) ^ 2 ∂(withDensityReal ρ) ≤ (C * deltaN d s N) ^ 2 := by
  set Λ₀ : ℝ := max (Λ 0) 1 with hΛ₀
  have hΛ₀0 : 0 ≤ Λ₀ := by have := le_max_right (Λ 0) 1; linarith
  obtain ⟨Ca, Cb, hCa, hCb, hrows⟩ := WeakRef.row_bounds hd hs0 hsd cstar hw A Λ₀ hΛ₀0
  set P : ℝ := max βp 0 + 1 with hP
  have hP1 : 1 ≤ P := by have := le_max_right βp 0; linarith
  have hP0 : 0 < P := by linarith
  set E : ℝ := Real.exp (2 * P) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  have hE0 : 0 < E := by linarith
  set G₁ : ℝ := 2 * P * E * Ca + P ^ 2 * E * Cb with hG₁
  have hG₁0 : 0 ≤ G₁ := by positivity
  set Kc : ℝ := Real.sqrt (2 * (Cb + Ca ^ 2 * E)) with hKc
  have hKc2 : Kc ^ 2 = 2 * (Cb + Ca ^ 2 * E) := Real.sq_sqrt (by positivity)
  have hKc0 : 0 ≤ Kc := Real.sqrt_nonneg _
  set C₀ : ℝ := 150 * G₁ ^ 2 + 214 * P ^ 2 * Kc ^ 2 + 12 * P ^ 2 with hC₀
  set C : ℝ := Real.sqrt C₀ with hCdef
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hC2 : C ^ 2 = C₀ := Real.sq_sqrt hC₀0
  refine ⟨min 1 (1 / (16 * E * P)), C, lt_min one_pos (by positivity), ?_⟩
  intro ρ hρ hprob hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  have hρle : ∀ x, ρ x ≤ Λ₀ := fun x =>
    (WeakRef.le_cbNorm_zero hsm x).trans ((hcb 0).trans (le_max_left _ _))
  have hK : WeakRef.WeakKernel μ a q := ⟨hqm, hqs, hq0, hrow⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hκ₀ : 0 ≤ τ * β := mul_nonneg hτ.1 hβ0.le
  have hκP : τ * β ≤ P := by
    have h1 : τ * β ≤ 1 * β := mul_le_mul_of_nonneg_right hτ.2 hβ0.le
    have h2 := hβ.2
    have h3 := le_max_left βp 0
    linarith
  have ha1 : a < 1 := lt_of_lt_of_le ha (min_le_left _ _)
  have haE : a < 1 / (16 * E * P) := lt_of_lt_of_le ha (min_le_right _ _)
  have hnN : 0 < N := by omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  set κ₀ : ℝ := τ * β with hκ₀def
  set V := WeakRef.mkV hK ha0 hκ₀ with hV
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hN1R : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hκaE : κ₀ * a ≤ 1 / (16 * E) := by
    have h1 : κ₀ * a ≤ P * a := mul_le_mul_of_nonneg_right hκP ha0
    have h2 : P * a ≤ P * (1 / (16 * E * P)) := mul_le_mul_of_nonneg_left haE.le hP0.le
    have h3 : P * (1 / (16 * E * P)) = 1 / (16 * E) := by field_simp
    linarith
  have hκa0 : 0 ≤ κ₀ * a := mul_nonneg hκ₀ ha0
  set D : ℝ := Real.exp (V.M + V.M' + κ₀ * V.γ) with hDdef
  have hVM : V.M = κ₀ * a := rfl
  have hVM' : V.M' = 0 := rfl
  have hVγ : V.γ = a := rfl
  have hDe : D = Real.exp (κ₀ * a + κ₀ * a) := by
    simp only [hDdef, hVM, hVM', hVγ]; congr 1; ring
  have hDE : D ≤ E := by
    rw [hDe]
    refine Real.exp_le_exp.2 ?_
    have : κ₀ * a ≤ P := by nlinarith
    linarith
  have hD1 : 1 ≤ D := by rw [hDe]; exact Real.one_le_exp (by linarith)
  have hs : κ₀ * V.γ * D ≤ 1 / 4 := by
    rw [hVγ]
    have : κ₀ * a * D ≤ (1 / (16 * E)) * E := mul_le_mul hκaE hDE (by linarith) (by positivity)
    have h2 : (1 / (16 * E)) * E = 1 / 16 := by field_simp
    linarith
  have hs2 : 214 * (κ₀ * V.γ) ^ 2 ≤ 1 := by
    rw [hVγ]
    have h1 : κ₀ * a ≤ 1 / 16 := by
      have : 1 / (16 * E) ≤ 1 / 16 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    have h2 : (κ₀ * a) ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ hκa0 h1 2
    nlinarith
  have hκ : External.weakKappa V κ₀ ≤ 1 / 2 := by
    have : External.weakKappa V κ₀ = 4 * D * (κ₀ * a) := by
      simp only [External.weakKappa, hDdef, hVγ]
    rw [this]
    have h1 : D * (κ₀ * a) ≤ E * (1 / (16 * E)) := mul_le_mul hDE hκaE hκa0 hE0.le
    have h2 : E * (1 / (16 * E)) = 1 / 16 := by field_simp
    linarith
  set δ : ℝ := deltaN d s (n + 1) with hδdef
  have hδ0 : 0 ≤ δ := deltaN_nonneg s (by omega)
  have hδ1 : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ δ := WeakRef.inv_le_deltaN hd hs0 hsd (by omega)
  have hrowsx := fun x => hrows ρ hρle q hqm hq0 hqA (n + 1) hN x
  have hT1 : ∀ x, ∫ y, max (q x y - ((n + 1 : ℕ) : ℝ)) 0 ∂μ ≤ Ca * δ := fun x => (hrowsx x).1
  have hT2 : ∀ x, ∫ y, (min (q x y) ((n + 1 : ℕ) : ℝ)) ^ 2 ∂μ ≤ Cb * (((n + 1 : ℕ) : ℝ) * δ) :=
    fun x => (hrowsx x).2
  have hT10 : ∀ x, 0 ≤ ∫ y, max (q x y - ((n + 1 : ℕ) : ℝ)) 0 ∂μ :=
    fun x => integral_nonneg fun y => le_max_right _ _
  have hT20 : ∀ x, 0 ≤ ∫ y, (min (q x y) ((n + 1 : ℕ) : ℝ)) ^ 2 ∂μ :=
    fun x => integral_nonneg fun y => sq_nonneg _
  have hnN : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hD0 : 0 ≤ D := by linarith
  set εG : ℝ := (2 * κ₀ * D * Ca + κ₀ ^ 2 * D * Cb) * δ with hεG
  have hKA : ∀ x, 2 * ((κ₀ / ((n + 1 : ℕ) : ℝ)) * (n * (D * ∫ z, max (V.q x z - ((n + 1 : ℕ) : ℝ)) 0 ∂μ)))
        + (κ₀ / ((n + 1 : ℕ) : ℝ)) ^ 2 / 2 * (2 * n * (D * ∫ z, (min (V.q x z) ((n + 1 : ℕ) : ℝ)) ^ 2 ∂μ))
        ≤ εG := fun x =>
    WeakRef.ka_alg hκ₀ hD0 (Nat.cast_nonneg n) hNR hnN hδ0 (hT10 x) (hT20 x) (hT1 x) (hT2 x)
  set εc : ℝ := Kc * δ with hεc
  have hKB : ∀ ν₁ ν₂ : Measure (Torus d), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
        ν₁ ≤ ENNReal.ofReal D • μ → ν₂ ≤ ENNReal.ofReal D • μ →
        (∀ A, MeasurableSet A → |ν₁.real A - ν₂.real A| ≤ External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) →
        ∫ x, (∫ y, V.q x y ∂ν₁ - ∫ y, V.q x y ∂ν₂) ^ 2 ∂μ ≤ εc ^ 2 := by
    intro ν₁ ν₂ _ _ h₁ h₂ hTV
    have hκ0 : 0 ≤ External.weakKappa V κ₀ := External.weakKappa_nonneg V hκ₀
    have hcv := WeakRef.Abs.conv_measures (μ := μ) (q := q) hqm hq0 hqs hK.integrable_row
      (N := ((n + 1 : ℕ) : ℝ)) (a₂ := Ca * δ) (b₁ := Cb * (((n + 1 : ℕ) : ℝ) * δ)) (D := D)
      (ε₀ := External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) hNR.le (by positivity)
      (by have := hδ0; positivity) (fun x => hT1 x) (fun x => hT2 x) hD0 ν₁ ν₂ h₁ h₂ hTV
    refine hcv.trans ?_
    have hε0 : 0 ≤ External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ) := div_nonneg hκ0 hNR.le
    have h2ε : 2 * (External.weakKappa V κ₀ / ((n + 1 : ℕ) : ℝ)) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hNR.le
    have := WeakRef.kb_alg hε0 h2ε hN1R hCa hCb hD0 hDE hδ0 hδ1
    have hKcδ : εc ^ 2 = 2 * (Cb + Ca ^ 2 * E) * δ ^ 2 := by rw [hεc, mul_pow, hKc2]
    rw [hKcδ]
    exact this
  obtain ⟨f, hfmap, hfm, ⟨K, hK'⟩, hfint⟩ := WeakRef.Abs.marginal_L2 V hκ₀ hn (fun x => rfl)
    (by show 0 ≤ κ₀ * a; exact hκa0) (le_refl _) hκ hs hs2 hKA hKB
  have hfin := WeakRef.final_alg (Kc := Kc) (a := a) hκ₀ hκP hD0 hDE hCa hCb hδ0 ha0 ha1.le hNR hδ1
  have hCδ : (C * δ) ^ 2 = C₀ * δ ^ 2 := by rw [mul_pow, hC2]
  have hbound : ∫ x, ((f x).toReal - 1) ^ 2 ∂μ ≤ (C * δ) ^ 2 := by
    rw [hVγ] at hfint
    calc ∫ x, ((f x).toReal - 1) ^ 2 ∂μ
        ≤ 150 * εG ^ 2 + 214 * κ₀ ^ 2 * εc ^ 2 + 12 * (κ₀ * a / ((n + 1 : ℕ) : ℝ)) ^ 2 := hfint
      _ ≤ (150 * (2 * P * E * Ca + P ^ 2 * E * Cb) ^ 2 + 214 * P ^ 2 * Kc ^ 2 + 12 * P ^ 2) * δ ^ 2 := hfin
      _ = (C * δ) ^ 2 := by rw [hCδ, hC₀, hG₁]
  have hmap : (pairGibbsLaw q (n + 1) (τ * β) μ).map (fun X => X ⟨0, by omega⟩)
      = μ.withDensity f := by
    rw [WeakRef.pairGibbsLaw_eq_pinnedLaw hK ha0 hκ₀ (Nat.succ_pos n)]
    exact hfmap
  exact ⟨f, hmap, hfm, ⟨K, hK'⟩, hbound⟩

set_option maxHeartbeats 400000 in
/-- Marginal bound `N:eq:weak-marginal` of Lemma 5.6 (source lines 6206-6268), from `weak_marginal_strong`. -/
theorem weak_marginal_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ [IsProbabilityMeasure (withDensityReal ρ)],
        Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ β ∈ Set.Icc βm βp, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ∃ f : Torus d → ℝ≥0∞,
          (pairGibbsLaw q N (τ * β) (withDensityReal ρ)).map (fun X => X ⟨0, by omega⟩)
            = (withDensityReal ρ).withDensity f ∧
          ∫⁻ x, ‖(f x).toReal - 1‖ₑ ^ 2 ∂(withDensityReal ρ)
            ≤ ENNReal.ofReal ((C * deltaN d s N) ^ 2) := by
  obtain ⟨a₀, C, ha₀, h⟩ := weak_marginal_strong hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀ Λ A
  refine ⟨a₀, C, ha₀, ?_⟩
  intro ρ hρ hprob hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  obtain ⟨f, hfmap, hfm, ⟨K, hK'⟩, hbound⟩ := h ρ hρ hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  refine ⟨f, hfmap, ?_⟩
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  have hfm' : Measurable fun x => (f x).toReal := hfm.ennreal_toReal
  have hint : Integrable (fun x => ((f x).toReal - 1) ^ 2) μ := by
    refine Integrable.of_bound ((hfm'.sub_const 1).pow_const 2).aestronglyMeasurable ((max K 0 + 1) ^ 2)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 : 0 ≤ (f x).toReal := ENNReal.toReal_nonneg
    have h1 := hK' x
    have h2 : |(f x).toReal - 1| ≤ max K 0 + 1 := by
      rw [abs_le]; constructor <;> linarith [le_max_left K 0, le_max_right K 0]
    calc ((f x).toReal - 1) ^ 2 = |(f x).toReal - 1| ^ 2 := (sq_abs _).symm
      _ ≤ (max K 0 + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  have e : ∀ x, ‖(f x).toReal - 1‖ₑ ^ 2 = ENNReal.ofReal (((f x).toReal - 1) ^ 2) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbound


/-- Lemma 5.6 `N:lem:weak` (source lines 6156-6172), without the pinned/cavity clause. -/
theorem weak_reference_estimates (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ [IsProbabilityMeasure (withDensityReal ρ)], Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ β ∈ Set.Icc βm βp, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        let μ : Measure (Torus d) := withDensityReal ρ
        let W := pairWeight q N (τ * β) μ
        let R := pairGibbsLaw q N (τ * β) μ
        -- conditional densities bounded by `C μ`
        (∀ (i : Fin N) (x : Config d N), External.siteKernel μ W i x ≤ ENNReal.ofReal C • μ) ∧
        -- interdependence coefficients `≤ C τ β a / N`, with row (and, by symmetry, column) sums `< 1/2`
        (∀ i j : Fin N, i ≠ j → ∀ x y : Config d N, (∀ k, k ≠ j → x k = y k) →
          ∀ S : Set (Torus d), MeasurableSet S →
            |(External.siteKernel μ W i x).real S - (External.siteKernel μ W i y).real S| ≤
              C * τ * β * a / N) ∧
        C * τ * β * a < 1 / 2 ∧
        -- first-marginal bound `N:eq:weak-marginal`
        (∃ f : Torus d → ℝ≥0∞, R.map (fun X => X ⟨0, by omega⟩) = μ.withDensity f ∧
          ∫⁻ x, ‖(f x).toReal - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((C * deltaN d s N) ^ 2)) ∧
        -- Wu's resampling inequality for `ℝ_{N,τ}`, `N:eq:weak-pi`
        (∀ F : Config d N → ℝ, Measurable F →
          ProbabilityTheory.evariance F R ≤
            2 * ∑ i, ∫⁻ x, ProbabilityTheory.evariance (fun z => F (Function.update x i z))
              (External.siteKernel μ W i x) ∂(R : Measure (Config d N))) := by
  obtain ⟨a₁, C₂, ha₁, hmarg⟩ := weak_marginal_aux hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀ Λ A
  set C₁ : ℝ := 4 * Real.exp (2 * βp) with hC₁
  set C : ℝ := max C₁ |C₂| with hC
  have hC₁C : C₁ ≤ C := le_max_left _ _
  have hC₂C : |C₂| ≤ C := le_max_right _ _
  have hC₁pos : 0 < C₁ := by positivity
  have hCpos : 0 < C := lt_of_lt_of_le hC₁pos hC₁C
  set B : ℝ := max βp 0 + 1 with hB
  have hBpos : 0 < B := by have := le_max_right βp 0; linarith
  have hβpB : βp ≤ B := by have := le_max_left βp 0; linarith
  have hCB : 0 < 1 / (4 * C * B) := by positivity
  refine ⟨min (min a₁ 1) (1 / (4 * C * B)), C, lt_min (lt_min ha₁ one_pos) hCB, ?_⟩
  intro ρ hρ hprob hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ τ hτ
  intro μ W R
  have : IsProbabilityMeasure μ := hprob
  have hK : WeakRef.WeakKernel μ a q := ⟨hqm, hqs, hq0, hrow⟩
  have hN0 : 0 < N := by omega
  have ha₁' : a < a₁ := lt_of_lt_of_le ha ((min_le_left _ _).trans (min_le_left _ _))
  have ha1 : a < 1 := lt_of_lt_of_le ha ((min_le_left _ _).trans (min_le_right _ _))
  have haB : a < 1 / (4 * C * B) := lt_of_lt_of_le ha (min_le_right _ _)
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hβ'0 : 0 ≤ τ * β := mul_nonneg hτ.1 hβ0.le
  have hβ'p : τ * β ≤ βp := by
    have : τ * β ≤ 1 * β := mul_le_mul_of_nonneg_right hτ.2 hβ0.le
    linarith [hβ.2]
  have hβ'a : τ * β * a ≤ βp := by
    have : τ * β * a ≤ τ * β * 1 := mul_le_mul_of_nonneg_left ha1.le hβ'0
    linarith
  have hexp : Real.exp (2 * (τ * β * a)) ≤ C := by
    have h1 : Real.exp (2 * (τ * β * a)) ≤ Real.exp (2 * βp) := Real.exp_le_exp.2 (by linarith)
    have : Real.exp (2 * βp) ≤ C₁ := by
      have := Real.exp_pos (2 * βp); linarith
    linarith
  have hsmall : C * τ * β * a < 1 / 2 := by
    have h1 : C * τ * β * a ≤ C * B * a := by
      have : τ * β ≤ B := hβ'p.trans hβpB
      have h2 : C * (τ * β) ≤ C * B := mul_le_mul_of_nonneg_left this hCpos.le
      have := mul_le_mul_of_nonneg_right h2 ha0
      calc C * τ * β * a = C * (τ * β) * a := by ring
        _ ≤ _ := this
    have h2 : C * B * a < C * B * (1 / (4 * C * B)) :=
      mul_lt_mul_of_pos_left haB (by positivity)
    have h3 : C * B * (1 / (4 * C * B)) = 1 / 4 := by field_simp
    linarith
  have hκ0 : 0 ≤ C * τ * β * a := by
    have : 0 ≤ τ * β * a := mul_nonneg hβ'0 ha0
    calc (0 : ℝ) ≤ C * (τ * β * a) := mul_nonneg hCpos.le this
      _ = C * τ * β * a := by ring
  have hcoef : ∀ i j : Fin N, i ≠ j → ∀ x y : Config d N, (∀ k, k ≠ j → x k = y k) →
      ∀ S : Set (Torus d), MeasurableSet S →
        |(External.siteKernel μ W i x).real S - (External.siteKernel μ W i y).real S| ≤
          C * τ * β * a / N := by
    intro i j hij x y hxy S hS
    refine (hK.siteKernel_coeff ha0 hβ'0 hN0 i j hij x y hxy S hS).trans ?_
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    have h1 : 0 ≤ τ * β * a := mul_nonneg hβ'0 ha0
    have h2 : 4 * Real.exp (2 * (τ * β * a)) ≤ C := by
      have := Real.exp_pos (2 * (τ * β * a))
      have h3 : Real.exp (2 * (τ * β * a)) ≤ Real.exp (2 * βp) := Real.exp_le_exp.2 (by linarith)
      linarith
    calc 4 * Real.exp (2 * (τ * β * a)) * (τ * β) * a
        = (4 * Real.exp (2 * (τ * β * a))) * (τ * β * a) := by ring
      _ ≤ C * (τ * β * a) := mul_le_mul_of_nonneg_right h2 h1
      _ = C * τ * β * a := by ring
  refine ⟨fun i x => hK.siteKernel_le ha0 hβ'0 hN0 i x hexp, hcoef, hsmall, ?_, ?_⟩
  · obtain ⟨f, hf1, hf2⟩ := hmarg ρ hρ hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha₁' hrow N hN β hβ τ hτ
    refine ⟨f, hf1, hf2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [mul_pow, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact sq_le_sq.2 (by rwa [abs_of_pos hCpos])
  · intro F hF
    exact hK.wu_clause ha0 hβ'0 hN0 (C * τ * β * a) hκ0 hsmall.le hcoef F hF

set_option maxHeartbeats 800000 in
theorem weak_pressure_upper_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        pairPartition q N β (withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨a₀', Cm, ha₀', hmarg⟩ := weak_marginal_strong hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀ Λ A
  set Λ₀ : ℝ := max (Λ 0) 1 with hΛ₀
  have hΛ₀0 : 0 ≤ Λ₀ := by have := le_max_right (Λ 0) 1; linarith
  obtain ⟨Ca, Cb, hCa, hCb, hrows⟩ := WeakRef.row_bounds_real hd hs0 hsd cstar hw A Λ₀ hΛ₀0
  set P : ℝ := max βp 0 + 1 with hP
  have hP1 : 1 ≤ P := by have := le_max_right βp 0; linarith
  have hP0 : 0 < P := by linarith
  set E : ℝ := Real.exp (2 * P) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  have hE0 : 0 < E := by linarith
  obtain ⟨Cw, hCw0, hWex⟩ := WeakRef.exists_W hd hs0 hsd hP1 hβm
  set Cm' : ℝ := |Cm| with hCm'
  have hCm0 : 0 ≤ Cm' := abs_nonneg _
  set A₁ : ℝ := 8 * E * Cb with hA₁
  set A₂ : ℝ := 12 * (1 + 2 * E * Ca) ^ 2 + 12 + 12 * E * Cm' ^ 2 with hA₂
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨min a₀' (min 1 (1 / (16 * E * P))), P * (1 / 2 + A₁ * Cw + A₂ * P),
    lt_min ha₀' (lt_min one_pos (by positivity)), ?_⟩
  intro ρ hρ hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  haveI hprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  have hK : WeakRef.WeakKernel μ a q := ⟨hqm, hqs, hq0, hrow⟩
  have hρle : ∀ x, ρ x ≤ Λ₀ := fun x =>
    (WeakRef.le_cbNorm_zero hsm x).trans ((hcb 0).trans (le_max_left _ _))
  have hrowsx := fun x => hrows ρ hρle q hqm hq0 hqA x
  have ha₁ : a < a₀' := lt_of_lt_of_le ha (min_le_left _ _)
  have ha1 : a < 1 := lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_left _ _))
  have haE : a < 1 / (16 * E * P) :=
    lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_right _ _))
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hβP : β ≤ P := by have := hβ.2; have := le_max_left βp 0; linarith
  have hN1 : 1 ≤ N := by omega
  obtain ⟨W₁, hW₁d, hW₁c, hW₁0, hW₁b⟩ := hWex N hN1
  have hpsiN := WeakRef.psi2_ge_one hd hs0 (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
  have hNδ := WeakRef.mul_deltaN_eq_psi2 (d := d) s hN1
  set V : ℝ → ℝ := fun t => A₁ * WeakRef.psi2 d s (2 * N * P / t) + A₂ * WeakRef.psi2 d s N with hVdef
  set W : ℝ → ℝ := fun t => A₁ * W₁ t + A₂ * WeakRef.psi2 d s N * t with hWdef
  have hup := hK.pairPartition_upper ha0 (show 0 < N by omega) hβ0 (V := V) (W := W)
    ?_ ?_ ?_ ?_ ?_
  · refine hup.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have hWβ : W β ≤ (A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N := by
      have h1 := hW₁b β hβ.1 hβP
      have h2 : A₂ * WeakRef.psi2 d s N * β ≤ A₂ * P * WeakRef.psi2 d s N := by
        have : 0 ≤ A₂ * WeakRef.psi2 d s N := by positivity
        nlinarith
      simp only [hWdef]
      nlinarith [mul_le_mul_of_nonneg_left h1 hA₁0]
    have hS0 : 0 ≤ (1 / 2 + A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N := by
      have : 0 ≤ 1 / 2 + A₁ * Cw + A₂ * P := by positivity
      exact mul_nonneg this (by linarith)
    have hx : a / 2 + W β ≤ (1 / 2 + A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N := by nlinarith
    calc β * (a / 2 + W β) ≤ β * ((1 / 2 + A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N) :=
          mul_le_mul_of_nonneg_left hx hβ0.le
      _ ≤ P * ((1 / 2 + A₁ * Cw + A₂ * P) * WeakRef.psi2 d s N) := mul_le_mul_of_nonneg_right hβP hS0
      _ = P * (1 / 2 + A₁ * Cw + A₂ * P) * ((N : ℝ) * deltaN d s N) := by rw [hNδ]; ring
      _ = _ := by ring
  · intro t ht
    have htβ : t ≤ β := ht.2
    have htP : t ≤ P := htβ.trans hβP
    have hτ : t / β ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1.le hβ0.le, (div_le_one hβ0).2 htβ⟩
    obtain ⟨f, hf1, hf2, -, hf4⟩ :=
      hmarg ρ hρ hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha₁ hrow N hN β hβ (t / β) hτ
    rw [div_mul_cancel₀ _ hβ0.ne'] at hf1
    have hta : t * a ≤ 1 / (16 * E) := by
      have h1 : t * a ≤ P * a := mul_le_mul_of_nonneg_right htP ha0
      have h2 : P * a ≤ P * (1 / (16 * E * P)) := mul_le_mul_of_nonneg_left haE.le hP0.le
      have h3 : P * (1 / (16 * E * P)) = 1 / (16 * E) := by field_simp
      linarith
    have hf5 : ∫ x, ((f x).toReal - 1) ^ 2 ∂μ ≤ (Cm' * deltaN d s N) ^ 2 := by
      refine hf4.trans (le_of_eq ?_)
      rw [hCm', mul_pow, mul_pow, sq_abs]
    exact WeakRef.variance_at hd hs0 hsd hK ha0 ha1.le hCa hCb hCm0 hP1 hE
      (fun x => (hrowsx x).1) (fun x => (hrowsx x).2) hN ht.1 htP hta ⟨f, hf1, hf2, hf5⟩
  · intro t ht
    have htP : t ≤ P := ht.2.trans hβP
    have hL : (1 : ℝ) ≤ 2 * N * P / t := by
      rw [le_div_iff₀ ht.1]
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      nlinarith
    have := WeakRef.psi2_ge_one hd hs0 hL
    exact add_nonneg (mul_nonneg hA₁0 (by linarith)) (mul_nonneg hA₂0 (by linarith))
  · intro t ht
    have h := ((hW₁d t ht).const_mul A₁).add ((hasDerivAt_id t).const_mul (A₂ * WeakRef.psi2 d s N))
    exact h.congr_deriv (by simp [hVdef])
  · exact (hW₁c.const_mul A₁).add ((continuous_const.mul continuous_id).continuousWithinAt)
  · simp [hWdef, hW₁0]


/-- Upper bound `K ≤ e^{C N δ_N}` of Lemma 5.7 (source lines 6281-6340), proved from `weak_pressure_upper_proof`. -/
theorem weak_pressure_upper_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        pairPartition q N β (withDensityReal ρ) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) :=
  weak_pressure_upper_proof hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀ Λ A

/-- Lemma 5.7 `N:lem:weak-pressure` (source lines 6271-6278): `|log K^q_{N,β}(μ)| ≤ C N δ_N`, uniformly over
kernels with the stated envelope and small row bound. -/
theorem weak_reference_pressure (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (cstar : ℝ) (hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) (A : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
        (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) →
      ∀ q : Torus d → Torus d → ℝ, Measurable (Function.uncurry q) → (∀ x y, q x y = q y x) →
        (∀ x y, 0 ≤ q x y) → (∀ x y, q x y ≤ A * (periodicRiesz d s (x - y) + cstar)) →
      ∀ a : ℝ, 0 ≤ a → a < a₀ →
        (∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal a) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc βm βp,
        ENNReal.ofReal (Real.exp (-(C * N * deltaN d s N))) ≤
            pairPartition q N β (withDensityReal ρ) ∧
          pairPartition q N β (withDensityReal ρ) ≤
            ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) := by
  obtain ⟨a₀, C₀, ha₀, hup⟩ := weak_pressure_upper_aux hd s hs0 hsd cstar hw βm βp hβm c₀ hc₀ Λ A
  refine ⟨a₀, max C₀ 0, ha₀, ?_⟩
  intro ρ hρ hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hK : WeakRef.WeakKernel (withDensityReal ρ) a q := ⟨hqm, hqs, hq0, hrow⟩
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ.1).le
  have hN0 : 0 < N := by omega
  have hδ : 0 ≤ (N : ℝ) * deltaN d s N :=
    mul_nonneg (Nat.cast_nonneg N) (deltaN_nonneg s (by omega))
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ (hK.one_le_partition ha0 hβ0 hN0)
    refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
    have : 0 ≤ max C₀ 0 * ((N : ℝ) * deltaN d s N) := mul_nonneg (le_max_right _ _) hδ
    linarith [show max C₀ 0 * N * deltaN d s N = max C₀ 0 * ((N : ℝ) * deltaN d s N) by ring]
  · refine (hup ρ hρ hsm hlow hcb q hqm hqs hq0 hqA a ha0 ha hrow N hN β hβ).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have : C₀ * ((N : ℝ) * deltaN d s N) ≤ max C₀ 0 * ((N : ℝ) * deltaN d s N) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
    linarith [show max C₀ 0 * N * deltaN d s N = max C₀ 0 * ((N : ℝ) * deltaN d s N) by ring,
      show C₀ * N * deltaN d s N = C₀ * ((N : ℝ) * deltaN d s N) by ring]

end HRS
