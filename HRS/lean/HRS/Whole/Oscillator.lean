import HRS.Whole.Hermite

/-!
# Whole-space foundations II: oscillator spaces `Σ^m`, their duals `B_m`, path spaces

Source: HRS whole-space supplement.
* `W:eq:euc-oscillator-space` (source lines 287-300):
  `E_m = {f : ∑_j λ_j^m |⟨f,h_j⟩|² < ∞}`, `B_m = E_m'`, `φ_j = λ_j^{-m/2} h_j`;
  "`B_m` and `𝓑_m` are used interchangeably; this is a weighted negative Sobolev topology;
  the quantitative path metric is the full supremum norm on `𝓧_T = C([0,T]; B_m)`".
* `H:eq:oscillator-space` (lines 353-360):
  `Σ^m = {f : 𝓗^{m/2} f ∈ L²(ℝ^d)}`, `B_m = (Σ^m)'`, `‖u‖²_{B_m} = ∑_j λ_j^{-m} |u(h_j)|²`,
  `‖f‖_{Σ^m} = ‖𝓗^{m/2} f‖₂`; "all the path estimates below use `C([0,T]; B_m)` with the
  supremum norm".
* Zero mass (lines 217-220): "All fluctuation distributions have zero total mass when that
  functional is defined in the chosen weighted dual" (`SOURCE_QUESTIONS.md` Q2,
  `docs/ISSUES.md` S1).

## Representation decisions

* `Σ^m` on functions: `MemOsc m f` / `oscNorm m f` use the Hermite-coefficient form
  `∑_α λ_α^m ⟨f,h_α⟩²`, which is the source's own definition `W:eq:euc-oscillator-space`;
  the equivalent operator form `‖𝓗^{m/2} f‖₂` of `H:eq:oscillator-space` is recorded, for
  even `m = 2k` and Schwartz `f`, in `oscNorm_even_eq` (`𝓗^k` as the iterated differential
  operator `oscillatorOp^[k]`).
* `OscSpace d m` (the sequence model of `Σ^m`) and `OscDual d m` (`B_m`) are both *defined*
  as the real Hilbert space `lp (fun _ : MultiIndex d => ℝ) 2` (project convention, cf.
  `HRS.NegSobolev`), with the dictionaries
  `OscSpace.coord f α = λ_α^{m/2} ⟨f,h_α⟩` and `OscDual.coord u α = λ_α^{-m/2} u(h_α)`.
  Hence `‖u‖_{OscDual} = (∑ λ_α^{-m} u(h_α)²)^{1/2}` is literally `‖u‖_{B_m}`.
  The source's `B_m = (Σ^m)'` is **not lost**: `OscDual.toDual` is a genuine isometric linear
  equivalence `OscDual d m ≃ₗᵢ[ℝ] StrongDual ℝ (OscSpace d m)` (Mathlib's Riesz map), and the
  theorems `OscDual.toDual_apply`, `OscDual.toDual_ofFun`, `OscSpace.norm_ofFun`,
  `OscSpace.toLp_injective`, `OscSpace.range_toLp` identify `OscSpace d m` with the function
  space `Σ^m` and `toDual u` with the pairing `u(f) = ∑_α u(h_α)⟨f,h_α⟩`.
  Different `m` are different types (`def`, not `abbrev`).
* Embeddings of finite signed measures (`OscDual.ofMeasureDiff`) and functions use a case
  split on `Memℓp` (never the bad branch for `m > d`: `OscDual.memℓp_of_bounded`, which needs
  Cramér's uniform bound on Hermite functions and `summable_oscEigenvalue_rpow_iff`).
* **Zero mass is not a functional on `OscDual d m`.**  The constant `1` is not in `L²`,
  hence not in any `Σ^m`, so testing against `1` is not continuous on `B_m`.  Following the
  source ("when that functional is defined"), `OscDual.HasMass u c` says that the pairing
  `u(χ(·/R))` converges to `c` as `R → ∞` for *every* smooth compactly supported cutoff `χ`
  equal to `1` near the origin; `HasZeroMass u := HasMass u 0`.  Theorem
  `OscDual.hasMass_ofMeasureDiff` identifies the subclass actually used by the source
  (differences of finite measures, in particular `μ_N - μ`, `μ_N - m_N`): there the mass is
  `μ(ℝ^d) - ν(ℝ^d)`, and it is zero for differences of probability measures.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### Hermite coefficients and `Σ^m` on functions -/

/-- Hermite coefficient `⟨f, h_α⟩ = ∫ f h_α dx` of a function. -/
def hermiteCoeff (f : Euc d → ℝ) (α : MultiIndex d) : ℝ := ∫ x, f x * hermiteFunD α x

/-- Hermite coefficient `μ(h_α) = ∫ h_α dμ` of a finite measure. -/
def measureHermiteCoeff (μ : Measure (Euc d)) (α : MultiIndex d) : ℝ := ∫ x, hermiteFunD α x ∂μ

/-- Membership in `Σ^m = E_m`: `f ∈ L²` with `∑_α λ_α^m ⟨f,h_α⟩² < ∞`
(`W:eq:euc-oscillator-space`, line 290). -/
def MemOsc (m : ℝ) (f : Euc d → ℝ) : Prop :=
  MemLp f 2 (volume : Measure (Euc d)) ∧
    Summable fun α : MultiIndex d => oscEigenvalue d α ^ m * hermiteCoeff f α ^ 2

/-- The `Σ^m` norm `‖f‖_{Σ^m} = (∑_α λ_α^m ⟨f,h_α⟩²)^{1/2} = ‖𝓗^{m/2} f‖₂` (lines 290, 357). -/
def oscNorm (m : ℝ) (f : Euc d → ℝ) : ℝ :=
  Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ m * hermiteCoeff f α ^ 2)

/-- `L²_0(μ) = {f ∈ L²(μ) : μ(f) = 0}` (source line 5294 region). -/
def MemL2Zero (μ : Measure (Euc d)) (f : Euc d → ℝ) : Prop :=
  MemLp f 2 μ ∧ ∫ x, f x ∂μ = 0

/-! ### The sequence model `OscSpace d m` of `Σ^m` -/

/-- `Σ^m` realised as `ℓ²(ℕ^d)` through the weighted coefficients `λ_α^{m/2} ⟨f,h_α⟩`. -/
def OscSpace (d : ℕ) (_m : ℝ) : Type := lp (fun _ : MultiIndex d => ℝ) 2

namespace OscSpace

variable {m : ℝ}

instance : NormedAddCommGroup (OscSpace d m) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : MultiIndex d => ℝ) 2))

instance : InnerProductSpace ℝ (OscSpace d m) :=
  inferInstanceAs (InnerProductSpace ℝ (lp (fun _ : MultiIndex d => ℝ) 2))

instance : CompleteSpace (OscSpace d m) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : MultiIndex d => ℝ) 2))

/-- The weighted coordinate `λ_α^{m/2} ⟨f,h_α⟩`. -/
def coord (f : OscSpace d m) (α : MultiIndex d) : ℝ :=
  (show lp (fun _ : MultiIndex d => ℝ) 2 from f) α

/-- The unweighted Hermite coefficient `⟨f,h_α⟩`. -/
def hermiteCoeff (f : OscSpace d m) (α : MultiIndex d) : ℝ :=
  oscEigenvalue d α ^ (-(m / 2)) * coord f α

open Classical in
/-- The element of `Σ^m` represented by a function `f` (`0` if `f ∉ Σ^m`). -/
def ofFun (m : ℝ) (f : Euc d → ℝ) : OscSpace d m :=
  if h : Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (m / 2) * Whole.hermiteCoeff f α) 2 then
    (⟨fun α => oscEigenvalue d α ^ (m / 2) * Whole.hermiteCoeff f α, h⟩ :
      lp (fun _ : MultiIndex d => ℝ) 2)
  else 0

/-- The function (class) `∑_α ⟨f,h_α⟩ h_α ∈ L²(ℝ^d)` represented by `f ∈ Σ^m`
(`L²`-convergent Hermite series; `tsum`). -/
def toLp (f : OscSpace d m) : Lp ℝ 2 (volume : Measure (Euc d)) :=
  ∑' α : MultiIndex d, hermiteCoeff f α • hermiteLpD α

end OscSpace

/-! ### The dual `B_m = (Σ^m)'` -/

/-- `B_m = (Σ^m)'`, realised as `ℓ²(ℕ^d)` through the weighted coefficients
`λ_α^{-m/2} u(h_α)`, so that `‖u‖ = (∑_α λ_α^{-m} |u(h_α)|²)^{1/2} = ‖u‖_{B_m}`
(`H:eq:oscillator-space`, line 356). -/
def OscDual (d : ℕ) (_m : ℝ) : Type := lp (fun _ : MultiIndex d => ℝ) 2

namespace OscDual

variable {m : ℝ}

instance : NormedAddCommGroup (OscDual d m) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : MultiIndex d => ℝ) 2))

instance : InnerProductSpace ℝ (OscDual d m) :=
  inferInstanceAs (InnerProductSpace ℝ (lp (fun _ : MultiIndex d => ℝ) 2))

instance : CompleteSpace (OscDual d m) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : MultiIndex d => ℝ) 2))

instance : MeasurableSpace (OscDual d m) := borel _

instance : BorelSpace (OscDual d m) := ⟨rfl⟩

/-- The weighted coordinate `λ_α^{-m/2} u(h_α) = u(φ_α)` (`φ_α = λ_α^{-m/2} h_α`, line 290). -/
def coord (u : OscDual d m) (α : MultiIndex d) : ℝ :=
  (show lp (fun _ : MultiIndex d => ℝ) 2 from u) α

/-- The unweighted value `u(h_α)`. -/
def hermiteCoeff (u : OscDual d m) (α : MultiIndex d) : ℝ :=
  oscEigenvalue d α ^ (m / 2) * coord u α

open Classical in
/-- The element of `B_m` with prescribed values `c α = u(h_α)`; `0` if the weighted sequence
is not square-summable. -/
def ofSeq (m : ℝ) (c : MultiIndex d → ℝ) : OscDual d m :=
  if h : Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (-(m / 2)) * c α) 2 then
    (⟨fun α => oscEigenvalue d α ^ (-(m / 2)) * c α, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2)
  else 0

/-- The pairing `u(φ) = ∑_α u(h_α) ⟨φ,h_α⟩` of `u ∈ B_m` with a test function
(`tsum`; the value whenever the series converges, in particular for `φ ∈ Σ^m`). -/
def eval (u : OscDual d m) (φ : Euc d → ℝ) : ℝ :=
  ∑' α : MultiIndex d, hermiteCoeff u α * Whole.hermiteCoeff φ α

/-- The embedding of a finite signed measure `μ - ν` into `B_m`. -/
def ofMeasureDiff (m : ℝ) (μ ν : Measure (Euc d)) : OscDual d m :=
  ofSeq m fun α => measureHermiteCoeff μ α - measureHermiteCoeff ν α

/-- The embedding of a single finite measure into `B_m`. -/
def ofMeasure (m : ℝ) (μ : Measure (Euc d)) : OscDual d m :=
  ofSeq m fun α => measureHermiteCoeff μ α

/-- The embedding of a function (via `f dx`) into `B_m`. -/
def ofFun (m : ℝ) (f : Euc d → ℝ) : OscDual d m := ofSeq m fun α => Whole.hermiteCoeff f α

/-- The embedding `B_m ↪ B_{m'}` for `m ≤ m'` (identity on the values `u(h_α)`). -/
def embed (m' : ℝ) (u : OscDual d m) : OscDual d m' := ofSeq m' (hermiteCoeff u)

/-- **The duality `B_m = (Σ^m)'`** (`H:eq:oscillator-space`, line 355): the isometric linear
equivalence of `B_m` with the topological dual of `Σ^m` (Mathlib's Riesz representation
`InnerProductSpace.toDual` for the common `ℓ²` model).  `OscDual.toDual_apply` identifies it
with the pairing `u(f) = ∑_α u(h_α)⟨f,h_α⟩`. -/
def toDual : OscDual d m ≃ₗᵢ[ℝ] StrongDual ℝ (OscSpace d m) :=
  InnerProductSpace.toDual ℝ (lp (fun _ : MultiIndex d => ℝ) 2)

/-! #### Zero mass on the subclass where it is defined (source lines 217-220) -/

/-- A smooth compactly supported cutoff equal to `1` near the origin. -/
structure IsCutoff (χ : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  compactSupport : HasCompactSupport χ
  one_near_zero : ∀ᶠ x in 𝓝 (0 : Euc d), χ x = 1

/-- The dilation `χ(·/R)`. -/
def dilate (R : ℝ) (χ : Euc d → ℝ) : Euc d → ℝ := fun x => χ (R⁻¹ • x)

/-- "`u` has total mass `c`": for every cutoff `χ`, `u(χ(·/R)) → c` as `R → ∞`.  This is the
mass functional *on the subclass where it is defined* (source lines 217-220); it is not a
continuous functional on all of `B_m`, since `1 ∉ Σ^m`. -/
def HasMass (u : OscDual d m) (c : ℝ) : Prop :=
  ∀ χ : Euc d → ℝ, IsCutoff χ → Tendsto (fun R : ℝ => eval u (dilate R χ)) atTop (𝓝 c)

/-- Zero total mass, where defined. -/
def HasZeroMass (u : OscDual d m) : Prop := HasMass u 0

end OscDual

/-! ### Path space `𝓧_T = C([0,T]; B_m)` with the supremum norm (lines 296-297, 358-360) -/

/-- `𝓧_T = C([0,T]; B_m)`; Mathlib's `ContinuousMap` norm on a compact domain is the sup norm. -/
def OscPath (d : ℕ) (m T : ℝ) : Type := C(Set.Icc (0 : ℝ) T, OscDual d m)

namespace OscPath

variable {m T : ℝ}

instance : NormedAddCommGroup (OscPath d m T) :=
  inferInstanceAs (NormedAddCommGroup C(Set.Icc (0 : ℝ) T, OscDual d m))

instance : NormedSpace ℝ (OscPath d m T) :=
  inferInstanceAs (NormedSpace ℝ C(Set.Icc (0 : ℝ) T, OscDual d m))

instance : MeasurableSpace (OscPath d m T) := borel _

instance : BorelSpace (OscPath d m T) := ⟨rfl⟩

/-- Evaluation at time `t ∈ [0,T]`. -/
def at' (w : OscPath d m T) (t : Set.Icc (0 : ℝ) T) : OscDual d m :=
  (show C(Set.Icc (0 : ℝ) T, OscDual d m) from w) t

/-- The shifted window `w^{a+·}` on `[0,T]` of a path defined on all of `ℝ`
(used for the uniform-in-`a` conclusions, Theorem `H:thm:whole-space`(ii)). -/
def window (a : ℝ) (w : ℝ → OscDual d m) (hw : Continuous w) : OscPath d m T :=
  (⟨fun t => w (a + t), by fun_prop⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m))

/-- `‖w‖_{𝓧_T} = sup_{0≤t≤T} ‖w^t‖_{B_m}`. -/
theorem norm_eq_iSup (w : OscPath d m T) (hT : 0 ≤ T) :
    ‖w‖ = ⨆ t : Set.Icc (0 : ℝ) T, ‖at' w t‖ := by
  exact ContinuousMap.norm_eq_iSup_norm w

end OscPath

/-! ### Facts about the representation (work package SFOUND-01) -/

section Facts

variable {m : ℝ}

/-! #### Helper lemmas (not part of the specification) -/

theorem oscEv_pos (α : MultiIndex d) : 0 < oscEigenvalue d α := by
  unfold oscEigenvalue
  have : (0:ℝ) ≤ (α.degree : ℝ) := Nat.cast_nonneg _
  have : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  linarith

theorem oscEv_one_le (α : MultiIndex d) : 1 ≤ oscEigenvalue d α := by
  unfold oscEigenvalue
  have : (0:ℝ) ≤ (α.degree : ℝ) := Nat.cast_nonneg _
  have : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  linarith

theorem memℓp_two_iff {ι : Type*} {f : ι → ℝ} : Memℓp f 2 ↔ Summable fun i => f i ^ 2 := by
  rw [memℓp_gen_iff (by simp)]
  simp [Real.norm_eq_abs, sq_abs]

theorem lp_two_norm_eq {ι : Type*} (x : lp (fun _ : ι => ℝ) 2) :
    ‖x‖ = Real.sqrt (∑' i, (x i) ^ 2) := by
  have := lp.norm_eq_tsum_rpow (p := 2) (E := fun _ : ι => ℝ) (by simp) x
  rw [this, Real.sqrt_eq_rpow]
  simp [Real.norm_eq_abs, sq_abs]

theorem lp_two_norm_sq {ι : Type*} (x : lp (fun _ : ι => ℝ) 2) :
    ‖x‖ ^ 2 = ∑' i, (x i) ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℝ) (by simp) x
  simpa [Real.norm_eq_abs, sq_abs] using this

theorem lp_two_summable {ι : Type*} (x : lp (fun _ : ι => ℝ) 2) : Summable fun i => (x i) ^ 2 :=
  memℓp_two_iff.1 (lp.memℓp x)

theorem rpow_half_sq (a x : ℝ) (hx : 0 < x) : (x ^ (a / 2)) ^ 2 = x ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring

theorem rpow_neg_half_mul (a x : ℝ) (hx : 0 < x) : x ^ (-(a / 2)) * x ^ (a / 2) = 1 := by
  rw [← Real.rpow_add hx]; simp

theorem hermiteCoeff_oscTestFun (m : ℝ) (α β : MultiIndex d) :
    Whole.hermiteCoeff (oscTestFun m α) β =
      oscEigenvalue d α ^ (-(m / 2)) * (if α = β then 1 else 0) := by
  unfold Whole.hermiteCoeff oscTestFun
  have : ∀ x : Euc d, oscEigenvalue d α ^ (-(m / 2)) * hermiteFunD α x * hermiteFunD β x
      = oscEigenvalue d α ^ (-(m / 2)) * (hermiteFunD α x * hermiteFunD β x) := fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, hermiteFunD_orthonormal]

namespace OscDual

theorem coord_sq_summable' (u : OscDual d m) : Summable fun α : MultiIndex d => coord u α ^ 2 :=
  lp_two_summable (ι := MultiIndex d) u

theorem norm_eq_coord (u : OscDual d m) :
    ‖u‖ = Real.sqrt (∑' α : MultiIndex d, coord u α ^ 2) :=
  lp_two_norm_eq (ι := MultiIndex d) u

theorem hermiteCoeff_sq (u : OscDual d m) (α : MultiIndex d) :
    oscEigenvalue d α ^ (-m) * hermiteCoeff u α ^ 2 = coord u α ^ 2 := by
  unfold hermiteCoeff
  have h := oscEv_pos α
  rw [mul_pow, rpow_half_sq _ _ h, ← mul_assoc, ← Real.rpow_add h]
  simp

theorem coord_eq_mul (u : OscDual d m) (α : MultiIndex d) :
    coord u α = oscEigenvalue d α ^ (-(m / 2)) * hermiteCoeff u α := by
  unfold hermiteCoeff
  have h := oscEv_pos α
  rw [← mul_assoc, rpow_neg_half_mul _ _ h, one_mul]

theorem toDual_apply_coord (u : OscDual d m) (f : OscSpace d m) :
    toDual u f = ∑' α : MultiIndex d, coord u α * OscSpace.coord f α := by
  have : toDual u f = inner ℝ (show lp (fun _ : MultiIndex d => ℝ) 2 from u)
      (show lp (fun _ : MultiIndex d => ℝ) 2 from f) := rfl
  rw [this, lp.inner_eq_tsum]
  refine tsum_congr fun α => ?_
  simp [OscSpace.coord, coord, mul_comm]


theorem coord_smul (c : ℝ) (u : OscDual d m) (α : MultiIndex d) :
    coord (c • u) α = c * coord u α := by
  show ((c • (show lp (fun _ : MultiIndex d => ℝ) 2 from u) : lp (fun _ : MultiIndex d => ℝ) 2)) α = _
  rw [lp.coeFn_smul]; rfl

theorem coord_add (u v : OscDual d m) (α : MultiIndex d) :
    coord (u + v) α = coord u α + coord v α := by
  show (((show lp (fun _ : MultiIndex d => ℝ) 2 from u) +
    (show lp (fun _ : MultiIndex d => ℝ) 2 from v) : lp (fun _ : MultiIndex d => ℝ) 2)) α = _
  rw [lp.coeFn_add]; rfl

theorem hermiteCoeff_smul (c : ℝ) (u : OscDual d m) (α : MultiIndex d) :
    hermiteCoeff (c • u) α = c * hermiteCoeff u α := by
  unfold hermiteCoeff; rw [coord_smul]; ring

theorem hermiteCoeff_add (u v : OscDual d m) (α : MultiIndex d) :
    hermiteCoeff (u + v) α = hermiteCoeff u α + hermiteCoeff v α := by
  unfold hermiteCoeff; rw [coord_add]; ring

theorem ext_hermiteCoeff {u v : OscDual d m} (h : ∀ α, hermiteCoeff u α = hermiteCoeff v α) :
    u = v := by
  refine lp.ext (funext fun α => ?_)
  have := oscEv_pos (d := d) α
  have h2 : oscEigenvalue d α ^ (m / 2) * coord u α = oscEigenvalue d α ^ (m / 2) * coord v α := h α
  exact mul_left_cancel₀ (Real.rpow_pos_of_pos this _).ne' h2

theorem eval_smul (c : ℝ) (u : OscDual d m) (φ : Euc d → ℝ) :
    eval (c • u) φ = c * eval u φ := by
  unfold eval
  rw [← tsum_mul_left]
  exact tsum_congr fun α => by rw [hermiteCoeff_smul]; ring

theorem HasMass.smul {u : OscDual d m} {a : ℝ} (h : HasMass u a) (c : ℝ) :
    HasMass (c • u) (c * a) := by
  intro χ hχ
  simp_rw [eval_smul]
  exact (h χ hχ).const_mul c

end OscDual


theorem hermiteCoeff_const_mul (c : ℝ) (f : Euc d → ℝ) (α : MultiIndex d) :
    hermiteCoeff (fun x => c * f x) α = c * hermiteCoeff f α := by
  unfold hermiteCoeff
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)

theorem oscNorm_const_mul (m c : ℝ) (f : Euc d → ℝ) :
    oscNorm m (fun x => c * f x) = |c| * oscNorm m f := by
  unfold oscNorm
  have : ∀ α : MultiIndex d, oscEigenvalue d α ^ m * hermiteCoeff (fun x => c * f x) α ^ 2 =
      c ^ 2 * (oscEigenvalue d α ^ m * hermiteCoeff f α ^ 2) := by
    intro α; rw [hermiteCoeff_const_mul]; ring
  simp_rw [this]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

namespace OscSpace

theorem coord_eq_mul (x : OscSpace d m) (α : MultiIndex d) :
    coord x α = oscEigenvalue d α ^ (m / 2) * hermiteCoeff x α := by
  unfold hermiteCoeff
  have h := oscEv_pos α
  rw [← mul_assoc, show oscEigenvalue d α ^ (m / 2) * oscEigenvalue d α ^ (-(m / 2)) = 1 from by
    rw [mul_comm]; exact rpow_neg_half_mul _ _ h, one_mul]

theorem norm_eq_coord (x : OscSpace d m) :
    ‖x‖ = Real.sqrt (∑' α : MultiIndex d, coord x α ^ 2) :=
  lp_two_norm_eq (ι := MultiIndex d) x

theorem memℓp_weighted {f : Euc d → ℝ} (hf : MemOsc m f) :
    Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (m / 2) * Whole.hermiteCoeff f α) 2 := by
  rw [memℓp_two_iff]
  refine hf.2.congr fun α => ?_
  rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]

theorem ofFun_eq {f : Euc d → ℝ} (hf : MemOsc m f) :
    ofFun m f = (⟨fun α : MultiIndex d => oscEigenvalue d α ^ (m / 2) * Whole.hermiteCoeff f α,
      memℓp_weighted hf⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := by
  unfold ofFun; exact dif_pos (memℓp_weighted hf)

theorem coord_ofFun_eq {f : Euc d → ℝ} (hf : MemOsc m f) (α : MultiIndex d) :
    coord (ofFun m f) α = oscEigenvalue d α ^ (m / 2) * Whole.hermiteCoeff f α := by
  rw [coord, ofFun_eq hf]

theorem hermiteCoeff_ofFun {f : Euc d → ℝ} (hf : MemOsc m f) (α : MultiIndex d) :
    hermiteCoeff (ofFun m f) α = Whole.hermiteCoeff f α := by
  unfold hermiteCoeff
  have h := oscEv_pos α
  rw [coord_ofFun_eq hf]
  rw [← mul_assoc, rpow_neg_half_mul _ _ h, one_mul]

theorem memℓp_hermiteCoeff (hm : 0 ≤ m) (f : OscSpace d m) :
    Memℓp (fun α : MultiIndex d => hermiteCoeff f α) 2 := by
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_)
    (lp_two_summable (ι := MultiIndex d) f)
  have h := oscEv_pos α
  have h1 : oscEigenvalue d α ^ (-(m / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (oscEv_one_le α) (by linarith)
  have h0 : 0 < oscEigenvalue d α ^ (-(m / 2)) := Real.rpow_pos_of_pos h _
  show (oscEigenvalue d α ^ (-(m / 2)) * coord f α) ^ 2 ≤ coord f α ^ 2
  rw [mul_pow]
  nlinarith [sq_nonneg (coord f α), mul_le_mul_of_nonneg_right (pow_le_one₀ h0.le h1 (n := 2))
    (sq_nonneg (coord f α))]

theorem inner_hermiteLpD_toLp (f : Euc d → ℝ) (hf : MemLp f 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    inner ℝ (hermiteLpD α) (hf.toLp f) = Whole.hermiteCoeff f α := by
  have h1 : hermiteLpD α = (memLp_hermiteFunD α).toLp (hermiteFunD α) := by
    unfold hermiteLpD; exact dif_pos _
  rw [h1, L2.inner_def]
  unfold Whole.hermiteCoeff
  refine integral_congr_ae ?_
  filter_upwards [(memLp_hermiteFunD α).coeFn_toLp, hf.coeFn_toLp] with x h1 h2
  rw [h1, h2]; simp [mul_comm]

theorem hasSum_toLp (b : HilbertBasis (MultiIndex d) ℝ (Lp ℝ 2 (volume : Measure (Euc d))))
    (hb : ∀ α, b α = hermiteLpD α) (hm : 0 ≤ m) (f : OscSpace d m) :
    HasSum (fun α => hermiteCoeff f α • hermiteLpD α)
      (b.repr.symm ⟨fun α => hermiteCoeff f α, memℓp_hermiteCoeff hm f⟩) := by
  have := b.hasSum_repr_symm ⟨fun α => hermiteCoeff f α, memℓp_hermiteCoeff hm f⟩
  simpa [hb] using this

theorem toLp_eq_repr_symm (b : HilbertBasis (MultiIndex d) ℝ (Lp ℝ 2 (volume : Measure (Euc d))))
    (hb : ∀ α, b α = hermiteLpD α) (hm : 0 ≤ m) (f : OscSpace d m) :
    toLp f = b.repr.symm ⟨fun α => hermiteCoeff f α, memℓp_hermiteCoeff hm f⟩ :=
  (hasSum_toLp b hb hm f).tsum_eq

end OscSpace

/-- Polynomial growth `|F x| ≤ C (1 + ‖x‖)^N`. -/
def PolyG {E : Type*} [Norm E] (F : E → ℝ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ N

namespace PolyG

variable {E : Type*} [NormedAddCommGroup E]

theorem const (c : ℝ) : PolyG (fun _ : E => c) :=
  ⟨|c|, 0, fun x => by simp⟩

theorem mul {F G : E → ℝ} (hF : PolyG F) (hG : PolyG G) : PolyG (fun x => F x * G x) := by
  obtain ⟨C, N, hC⟩ := hF
  obtain ⟨D, M, hD⟩ := hG
  refine ⟨C * D, N + M, fun x => ?_⟩
  have h1 : (0:ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  calc |F x * G x| = |F x| * |G x| := abs_mul _ _
    _ ≤ (C * (1 + ‖x‖) ^ N) * (D * (1 + ‖x‖) ^ M) :=
        mul_le_mul (hC x) (hD x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC x))
    _ = (C * D) * (1 + ‖x‖) ^ (N + M) := by rw [pow_add]; ring

theorem add {F G : E → ℝ} (hF : PolyG F) (hG : PolyG G) : PolyG (fun x => F x + G x) := by
  obtain ⟨C, N, hC⟩ := hF
  obtain ⟨D, M, hD⟩ := hG
  refine ⟨|C| + |D|, max N M, fun x => ?_⟩
  have h1 : (1:ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hN : (1 + ‖x‖) ^ N ≤ (1 + ‖x‖) ^ (max N M) := pow_le_pow_right₀ h1 (le_max_left _ _)
  have hM : (1 + ‖x‖) ^ M ≤ (1 + ‖x‖) ^ (max N M) := pow_le_pow_right₀ h1 (le_max_right _ _)
  have ht : (0:ℝ) ≤ (1 + ‖x‖) ^ (max N M) := by positivity
  calc |F x + G x| ≤ |F x| + |G x| := abs_add_le _ _
    _ ≤ C * (1 + ‖x‖) ^ N + D * (1 + ‖x‖) ^ M := add_le_add (hC x) (hD x)
    _ ≤ |C| * (1 + ‖x‖) ^ (max N M) + |D| * (1 + ‖x‖) ^ (max N M) :=
        add_le_add (mul_le_mul (le_abs_self C) hN (by positivity) (abs_nonneg C))
          (mul_le_mul (le_abs_self D) hM (by positivity) (abs_nonneg D))
    _ = (|C| + |D|) * (1 + ‖x‖) ^ (max N M) := by ring

theorem finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {F : ι → E → ℝ}
    (h : ∀ i ∈ s, PolyG (F i)) : PolyG (fun x => ∏ i ∈ s, F i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using const (E := E) 1
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.prod_insert ha]
    exact h1.mul h2

end PolyG

/-- Coordinates of Euclidean vectors. -/
theorem polyG_coord {d : ℕ} {F : ℝ → ℝ} (i : Fin d) (hF : PolyG F) :
    PolyG (fun x : Euc d => F (x i)) := by
  obtain ⟨C, N, hC⟩ := hF
  refine ⟨|C|, N, fun x => ?_⟩
  have h1 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
  have h2 : (1 + ‖x i‖) ^ N ≤ (1 + ‖x‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
  rw [Real.norm_eq_abs] at h1 h2
  show |F (x i)| ≤ |C| * (1 + ‖x‖) ^ N
  calc |F (x i)| ≤ C * (1 + |x i|) ^ N := by simpa [Real.norm_eq_abs] using hC (x i)
    _ ≤ |C| * (1 + ‖x‖) ^ N := by
        have := (le_abs_self C)
        have ht : (0:ℝ) ≤ (1 + |x i|) ^ N := by positivity
        exact mul_le_mul this (by simpa [Real.norm_eq_abs] using h2) ht (abs_nonneg C)

/-- Polynomials are of polynomial growth. -/
theorem polyG_poly (p : Polynomial ℝ) : PolyG (fun y : ℝ => p.eval y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact hp.add hq
  | monomial n a =>
    refine ⟨|a|, n, fun y => ?_⟩
    show |Polynomial.eval y (Polynomial.monomial n a)| ≤ |a| * (1 + ‖y‖) ^ n
    rw [Polynomial.eval_monomial, abs_mul, abs_pow, Real.norm_eq_abs]
    have h1 : |y| ^ n ≤ (1 + |y|) ^ n := pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)

theorem polyG_gauss_mul {F : ℝ → ℝ} (hF : PolyG F) : PolyG (fun y => F y * gauss y) := by
  obtain ⟨C, N, hC⟩ := hF
  refine ⟨C, N, fun y => ?_⟩
  have hg0 : 0 < gauss y := by unfold gauss; exact Real.exp_pos _
  have hg1 : gauss y ≤ 1 := by
    unfold gauss; exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y])
  rw [abs_mul, abs_of_pos hg0]
  exact le_trans (mul_le_of_le_one_right (abs_nonneg _) hg1) (hC y)

/-- One-dimensional facts on `h_n` and its derivatives. -/
theorem hermiteFun_polyG (n : ℕ) : PolyG (hermiteFun n) := by
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly' n
  have : hermiteFun n = fun y => p.eval y * gauss y := funext hp
  rw [this]
  exact polyG_gauss_mul (polyG_poly p)

theorem hermiteFun_deriv_polyG (n : ℕ) : PolyG (deriv (hermiteFun n)) := by
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly' n
  have : hermiteFun n = fun y => p.eval y * gauss y := funext hp
  have hd : deriv (hermiteFun n) = fun z => (Polynomial.derivative p - Polynomial.X * p).eval z * gauss z := by
    funext z
    rw [this]
    exact (hasDerivAt_poly_mul_gauss p z).deriv
  rw [hd]
  exact polyG_gauss_mul (polyG_poly _)

theorem hermiteFun_hasDerivAt_deriv (n : ℕ) (y : ℝ) :
    HasDerivAt (hermiteFun n) (deriv (hermiteFun n) y) y :=
  ((contDiff_hermiteFun n).differentiable (by simp)  y).hasDerivAt

theorem hermiteFun_iteratedDeriv_two_eq (n : ℕ) (y : ℝ) :
    iteratedDeriv 2 (hermiteFun n) y = (y ^ 2 - (2 * (n : ℝ) + 1)) * hermiteFun n y := by
  have h := hermiteFun_ode n y
  linarith

theorem hermiteFun_iteratedDeriv_two_polyG (n : ℕ) :
    PolyG (iteratedDeriv 2 (hermiteFun n)) := by
  have : iteratedDeriv 2 (hermiteFun n) = fun y => (y ^ 2 - (2 * (n : ℝ) + 1)) * hermiteFun n y :=
    funext (hermiteFun_iteratedDeriv_two_eq n)
  rw [this]
  have hp : PolyG (fun y : ℝ => y ^ 2 - (2 * (n : ℝ) + 1)) := by
    have := polyG_poly (Polynomial.X ^ 2 - Polynomial.C (2 * (n : ℝ) + 1))
    simpa using this
  exact PolyG.mul hp (hermiteFun_polyG n)

theorem hermiteFun_deriv_hasDerivAt_two (n : ℕ) (y : ℝ) :
    HasDerivAt (deriv (hermiteFun n)) (iteratedDeriv 2 (hermiteFun n) y) y := by
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly' n
  have hd : deriv (hermiteFun n) = fun z => (Polynomial.derivative p - Polynomial.X * p).eval z * gauss z := by
    funext z
    have : hermiteFun n = fun y => p.eval y * gauss y := funext hp
    rw [this]
    exact (hasDerivAt_poly_mul_gauss p z).deriv
  have h2 : iteratedDeriv 2 (hermiteFun n) y = deriv (deriv (hermiteFun n)) y := by
    show iteratedDeriv (1 + 1) (hermiteFun n) y = _
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, hd]
  have H := hasDerivAt_poly_mul_gauss (Polynomial.derivative p - Polynomial.X * p) y
  rw [H.deriv]
  exact H


theorem pow_bound_aux (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  rcases le_total t 1 with h | h
  · have h1 : (1 + t) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have h2 : (0:ℝ) ≤ t ^ N := pow_nonneg ht N
    calc (1 + t) ^ N ≤ 2 ^ N := h1
      _ ≤ 2 ^ N * (1 + t ^ N) := le_mul_of_one_le_right (by positivity) (by linarith)
  · calc (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * t ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + t ^ N) := mul_le_mul_of_nonneg_left (by linarith [pow_nonneg ht N]) (by positivity)

/-- Schwartz functions integrate against functions of polynomial growth. -/
theorem int_schwartz_mul {d : ℕ} (u : SchwartzMap (Euc d) ℝ) (w : Euc d → ℝ) (hw : Continuous w)
    (hp : PolyG w) : Integrable (fun x => u x * w x) := by
  obtain ⟨C, N, hC⟩ := hp
  have hint : Integrable (fun x : Euc d => ‖u x‖ + ‖x‖ ^ N * ‖u x‖) := by
    have h0 := SchwartzMap.integrable_pow_mul (volume : Measure (Euc d)) u 0
    simp only [pow_zero, one_mul] at h0
    exact h0.add (SchwartzMap.integrable_pow_mul volume u N)
  refine Integrable.mono' (g := fun x : Euc d => |C| * 2 ^ N * (‖u x‖ + ‖x‖ ^ N * ‖u x‖))
    (hint.const_mul _) ((u.continuous.mul hw).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have ht : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hw1 : |w x| ≤ |C| * (1 + ‖x‖) ^ N :=
    le_trans (hC x) (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hw2 : |w x| ≤ |C| * (2 ^ N * (1 + ‖x‖ ^ N)) :=
    hw1.trans (mul_le_mul_of_nonneg_left (pow_bound_aux _ ht N) (abs_nonneg C))
  rw [norm_mul, Real.norm_eq_abs]
  calc ‖u x‖ * |w x| ≤ ‖u x‖ * (|C| * (2 ^ N * (1 + ‖x‖ ^ N))) :=
        mul_le_mul_of_nonneg_left hw2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖u x‖ + ‖x‖ ^ N * ‖u x‖) := by ring

/-- Integration by parts in a fixed direction against a Schwartz function. -/
theorem ibp_schwartz {d : ℕ} (u : SchwartzMap (Euc d) ℝ) (w w' : Euc d → ℝ) (v : Euc d)
    (hw : ∀ x, HasLineDerivAt ℝ w (w' x) x v) (hwc : Continuous w) (hwp : PolyG w)
    (hwc' : Continuous w') (hwp' : PolyG w') :
    ∫ x, lineDeriv ℝ (⇑u) x v * w x = -∫ x, u x * w' x := by
  have hD : ∀ x, lineDeriv ℝ (⇑u) x v = (LineDeriv.lineDerivOp v u) x :=
    fun x => (SchwartzMap.lineDerivOp_apply v u x).symm
  have hu : ∀ x, HasLineDerivAt ℝ (⇑u) (lineDeriv ℝ (⇑u) x v) x v := fun x =>
    ((u.differentiableAt (x := x)).lineDifferentiableAt (v := v)).hasLineDerivAt
  have I1 : Integrable (fun x => lineDeriv ℝ (⇑u) x v * w x) := by
    simp_rw [hD]; exact int_schwartz_mul _ w hwc hwp
  have I2 : Integrable (fun x => u x * w' x) := int_schwartz_mul u w' hwc' hwp'
  have I3 : Integrable (fun x => u x * w x) := int_schwartz_mul u w hwc hwp
  have I4 : Integrable (fun x => u x * w' x) := I2
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) (f := ⇑u) (f' := fun x => lineDeriv ℝ (⇑u) x v)
    (g := w) (g' := w') (v := v) (μ := volume) (by simpa using I1) (by simpa using I4)
    (by simpa using I3) (fun x _ => hu x) (fun x _ => hw x)
  simp only [ContinuousLinearMap.mul_apply'] at key
  linarith

theorem hasLineDerivAt_coord_mul {d : ℕ} (i : Fin d) (Q : Euc d → ℝ)
    (hQ : ∀ (x : Euc d) (t : ℝ), Q (x + t • (EuclideanSpace.single i (1:ℝ) : Euc d)) = Q x)
    (F F' : ℝ → ℝ) (hF : ∀ y, HasDerivAt F (F' y) y) (x : Euc d) :
    HasLineDerivAt ℝ (fun x => Q x * F (x i)) (Q x * F' (x i)) x ((EuclideanSpace.single i (1:ℝ) : Euc d)) := by
  show HasDerivAt (fun t : ℝ => Q (x + t • (EuclideanSpace.single i (1:ℝ) : Euc d)) *
    F ((x + t • (EuclideanSpace.single i (1:ℝ) : Euc d)) i)) _ 0
  have hfun : (fun t : ℝ => Q (x + t • (EuclideanSpace.single i (1:ℝ) : Euc d)) *
      F ((x + t • (EuclideanSpace.single i (1:ℝ) : Euc d)) i)) = fun t => Q x * F (x i + t) := by
    funext t
    rw [hQ x t]
    congr 2
    simp
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => F (x i + t)) (F' (x i)) 0 :=
    HasDerivAt.comp_const_add (x i) 0 (by simpa using hF (x i))
  exact h1.const_mul (Q x)

theorem prod_erase_indep {d : ℕ} (i : Fin d) (F : Fin d → ℝ → ℝ) (x : Euc d) (t : ℝ) :
    (∏ j ∈ Finset.univ.erase i, F j ((x + t • (EuclideanSpace.single i (1:ℝ) : Euc d)) j)) =
      ∏ j ∈ Finset.univ.erase i, F j (x j) := by
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  congr 1
  simp [hji]

theorem schwartz_iter_exists {d : ℕ} (k : ℕ) (f : SchwartzMap (Euc d) ℝ) :
    ∃ F : SchwartzMap (Euc d) ℝ, ⇑F = (oscillatorOp (d := d))^[k] ⇑f := by
  induction k generalizing f with
  | zero => exact ⟨f, rfl⟩
  | succ k ih =>
    let H : SchwartzMap (Euc d) ℝ :=
      f - Laplacian.laplacian f + SchwartzMap.smulLeftCLM ℝ (fun x : Euc d => ‖x‖ ^ 2) f
    have hH : ⇑H = oscillatorOp (d := d) ⇑f := by
      funext x
      simp only [H, add_apply, sub_apply,
        SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_norm_sq (Euc d)),
        SchwartzMap.laplacian_apply, oscillatorOp, smul_eq_mul]
    obtain ⟨G, hG⟩ := ih H
    refine ⟨G, ?_⟩
    rw [hG, hH, Function.iterate_succ_apply]


theorem hermiteFunD_split {d : ℕ} (α : MultiIndex d) (i : Fin d) (x : Euc d) :
    hermiteFunD α x = (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) * hermiteFun (α i) (x i) := by
  unfold hermiteFunD
  exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm

theorem hermiteFunD_line_data {d : ℕ} (α : MultiIndex d) (i : Fin d) :
    (∀ x : Euc d, HasLineDerivAt ℝ (hermiteFunD α)
        ((∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) * deriv (hermiteFun (α i)) (x i)) x
        (EuclideanSpace.single i (1:ℝ) : Euc d)) ∧
    (∀ x : Euc d, HasLineDerivAt ℝ
        (fun x : Euc d => (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
          deriv (hermiteFun (α i)) (x i))
        ((∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) * iteratedDeriv 2 (hermiteFun (α i)) (x i))
        x (EuclideanSpace.single i (1:ℝ) : Euc d)) := by
  constructor
  · intro x
    have hfun : hermiteFunD α = fun y : Euc d =>
        (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (y j)) * hermiteFun (α i) (y i) :=
      funext (hermiteFunD_split α i)
    rw [hfun]
    exact hasLineDerivAt_coord_mul i _
      (fun x t => prod_erase_indep i (fun j => hermiteFun (α j)) x t)
      (hermiteFun (α i)) (deriv (hermiteFun (α i))) (hermiteFun_hasDerivAt_deriv (α i)) x
  · intro x
    exact hasLineDerivAt_coord_mul i _
      (fun x t => prod_erase_indep i (fun j => hermiteFun (α j)) x t)
      (deriv (hermiteFun (α i))) (iteratedDeriv 2 (hermiteFun (α i)))
      (hermiteFun_deriv_hasDerivAt_two (α i)) x

theorem hermiteFunD_regularity {d : ℕ} (α : MultiIndex d) (i : Fin d) :
    Continuous (fun x : Euc d => (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
      deriv (hermiteFun (α i)) (x i)) ∧
    Continuous (fun x : Euc d => (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
      iteratedDeriv 2 (hermiteFun (α i)) (x i)) ∧
    Continuous (hermiteFunD α) ∧
    PolyG (fun x : Euc d => (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
      deriv (hermiteFun (α i)) (x i)) ∧
    PolyG (fun x : Euc d => (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
      iteratedDeriv 2 (hermiteFun (α i)) (x i)) ∧
    PolyG (hermiteFunD α) := by
  have hc : ∀ n, Continuous (hermiteFun n) := fun n => (contDiff_hermiteFun n).continuous
  have hc1 : ∀ n, Continuous (deriv (hermiteFun n)) := fun n => by
    have h := ContDiff.continuous_iteratedDeriv 1 (contDiff_hermiteFun n) (by simp)
    rwa [iteratedDeriv_one] at h
  have hc2 : ∀ n, Continuous (iteratedDeriv 2 (hermiteFun n)) := fun n =>
    ContDiff.continuous_iteratedDeriv 2 (contDiff_hermiteFun n) (by simp)
  have hQc : Continuous (fun x : Euc d => ∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) :=
    continuous_finsetProd _ fun j _ => (hc (α j)).comp (show Continuous (fun x : Euc d => x j) by fun_prop)
  have hQp : PolyG (fun x : Euc d => ∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) :=
    PolyG.finset_prod _ fun j _ => polyG_coord j (hermiteFun_polyG (α j))
  have hxi : Continuous (fun x : Euc d => x i) := by fun_prop
  refine ⟨hQc.mul ((hc1 (α i)).comp hxi), hQc.mul ((hc2 (α i)).comp hxi),
    (contDiff_hermiteFunD α).continuous, PolyG.mul hQp (polyG_coord i (hermiteFun_deriv_polyG (α i))),
    PolyG.mul hQp (polyG_coord i (hermiteFun_iteratedDeriv_two_polyG (α i))), ?_⟩
  exact PolyG.finset_prod Finset.univ (fun j _ => polyG_coord j (hermiteFun_polyG (α j)))


theorem lap_term {d : ℕ} (α : MultiIndex d) (u : SchwartzMap (Euc d) ℝ) (i : Fin d) :
    ∫ x, (LineDeriv.lineDerivOp (EuclideanSpace.single i (1:ℝ) : Euc d)
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1:ℝ) : Euc d) u)) x * hermiteFunD α x =
      ∫ x, u x * ((∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
        iteratedDeriv 2 (hermiteFun (α i)) (x i)) := by
  obtain ⟨hA, hB⟩ := hermiteFunD_line_data α i
  obtain ⟨hD1c, hD2c, hhc, hD1p, hD2p, hhp⟩ := hermiteFunD_regularity α i
  have s1 := ibp_schwartz (LineDeriv.lineDerivOp (EuclideanSpace.single i (1:ℝ) : Euc d) u)
    (hermiteFunD α) _ (EuclideanSpace.single i (1:ℝ) : Euc d) hA hhc hhp hD1c hD1p
  have s2 := ibp_schwartz u _ _ (EuclideanSpace.single i (1:ℝ) : Euc d) hB hD1c hD1p hD2c hD2p
  simp_rw [SchwartzMap.lineDerivOp_apply] at s1 s2 ⊢
  rw [s1, s2, neg_neg]

theorem lapSym_hermite {d : ℕ} (α : MultiIndex d) (u : SchwartzMap (Euc d) ℝ) :
    ∫ x, Laplacian.laplacian (⇑u) x * hermiteFunD α x =
      ∫ x, u x * Laplacian.laplacian (hermiteFunD α) x := by
  have hΔ : ∀ x : Euc d, Laplacian.laplacian (hermiteFunD α) x =
      ∑ i, (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
        iteratedDeriv 2 (hermiteFun (α i)) (x i) :=
    fun x => laplacian_prod_euc (fun i => hermiteFun (α i)) (fun i => contDiff_hermiteFun (α i)) x
  have hS : ∀ x : Euc d, Laplacian.laplacian (⇑u) x =
      ∑ i, (LineDeriv.lineDerivOp (EuclideanSpace.single i (1:ℝ) : Euc d)
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1:ℝ) : Euc d) u)) x := by
    intro x
    rw [← SchwartzMap.laplacian_apply, SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ) u,
      sum_apply]
    simp only [EuclideanSpace.basisFun_apply]
  have hL : ∫ x, Laplacian.laplacian (⇑u) x * hermiteFunD α x =
      ∑ i, ∫ x, (LineDeriv.lineDerivOp (EuclideanSpace.single i (1:ℝ) : Euc d)
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1:ℝ) : Euc d) u)) x * hermiteFunD α x := by
    simp_rw [hS, Finset.sum_mul]
    rw [integral_finsetSum]
    intro i _
    obtain ⟨_, _, hhc, _, _, hhp⟩ := hermiteFunD_regularity α i
    exact int_schwartz_mul _ _ hhc hhp
  have hR : ∫ x, u x * Laplacian.laplacian (hermiteFunD α) x =
      ∑ i, ∫ x, u x * ((∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (x j)) *
        iteratedDeriv 2 (hermiteFun (α i)) (x i)) := by
    simp_rw [hΔ, Finset.mul_sum]
    rw [integral_finsetSum]
    intro i _
    obtain ⟨_, hD2c, _, _, hD2p, _⟩ := hermiteFunD_regularity α i
    exact int_schwartz_mul u _ hD2c hD2p
  rw [hL, hR]
  exact Finset.sum_congr rfl fun i _ => lap_term α u i


theorem hermiteFunD_poly {d : ℕ} (α : MultiIndex d) :
    Continuous (hermiteFunD α) ∧ PolyG (hermiteFunD α) :=
  ⟨(contDiff_hermiteFunD α).continuous,
    PolyG.finset_prod Finset.univ (fun j _ => polyG_coord j (hermiteFun_polyG (α j)))⟩

theorem polyG_norm_sq {d : ℕ} : PolyG (fun x : Euc d => ‖x‖ ^ 2) := by
  refine ⟨1, 2, fun x => ?_⟩
  rw [abs_of_nonneg (by positivity), one_mul]
  nlinarith [norm_nonneg x]

/-- Symmetry of `𝓗` against a Hermite function: `⟨𝓗 u, h_α⟩ = λ_α ⟨u, h_α⟩` for Schwartz `u`. -/
theorem sym_oscillatorOp_hermite {d : ℕ} (α : MultiIndex d) (u : SchwartzMap (Euc d) ℝ) :
    ∫ x, oscillatorOp (⇑u) x * hermiteFunD α x =
      oscEigenvalue d α * ∫ x, u x * hermiteFunD α x := by
  have hΔh : ∀ x : Euc d, Laplacian.laplacian (hermiteFunD α) x =
      (1 - oscEigenvalue d α + ‖x‖ ^ 2) * hermiteFunD α x := by
    intro x
    have h := oscillatorOp_hermiteFunD α x
    unfold oscillatorOp at h
    linear_combination (-1 : ℝ) * h
  obtain ⟨hhc, hhp⟩ := hermiteFunD_poly α
  have I1 : Integrable (fun x => u x * hermiteFunD α x) := int_schwartz_mul u _ hhc hhp
  have hn2c : Continuous (fun x : Euc d => ‖x‖ ^ 2 * hermiteFunD α x) :=
    (continuous_norm.pow 2).mul hhc
  have hn2p : PolyG (fun x : Euc d => ‖x‖ ^ 2 * hermiteFunD α x) := PolyG.mul polyG_norm_sq hhp
  have I2 : Integrable (fun x => u x * (‖x‖ ^ 2 * hermiteFunD α x)) :=
    int_schwartz_mul u _ hn2c hn2p
  have I3 : Integrable (fun x => Laplacian.laplacian (⇑u) x * hermiteFunD α x) := by
    have := int_schwartz_mul (Laplacian.laplacian u) _ hhc hhp
    simpa only [SchwartzMap.laplacian_apply] using this
  have hL := lapSym_hermite α u
  have e1 : ∀ x : Euc d, oscillatorOp (⇑u) x * hermiteFunD α x =
      u x * hermiteFunD α x - Laplacian.laplacian (⇑u) x * hermiteFunD α x +
        u x * (‖x‖ ^ 2 * hermiteFunD α x) := by
    intro x
    unfold oscillatorOp
    ring
  have hLHS : ∫ x, oscillatorOp (⇑u) x * hermiteFunD α x =
      (∫ x, u x * hermiteFunD α x) - (∫ x, Laplacian.laplacian (⇑u) x * hermiteFunD α x) +
        ∫ x, u x * (‖x‖ ^ 2 * hermiteFunD α x) := by
    simp_rw [e1]
    have I12 : Integrable (fun x => u x * hermiteFunD α x - Laplacian.laplacian (⇑u) x * hermiteFunD α x) :=
      I1.sub I3
    rw [integral_add I12 I2, integral_sub I1 I3]
  have e2 : ∀ x : Euc d, u x * Laplacian.laplacian (hermiteFunD α) x =
      (1 - oscEigenvalue d α) * (u x * hermiteFunD α x) + u x * (‖x‖ ^ 2 * hermiteFunD α x) := by
    intro x
    rw [hΔh x]
    ring
  have hR : ∫ x, u x * Laplacian.laplacian (hermiteFunD α) x =
      (1 - oscEigenvalue d α) * (∫ x, u x * hermiteFunD α x) +
        ∫ x, u x * (‖x‖ ^ 2 * hermiteFunD α x) := by
    simp_rw [e2]
    rw [integral_add (I1.const_mul _) I2, integral_const_mul]
  rw [hLHS, hL, hR]
  ring

/-- Hermite coefficients of `𝓗^k f` for Schwartz `f`: `⟨𝓗^k f, h_α⟩ = λ_α^k ⟨f, h_α⟩`. -/
theorem coeff_iter {d : ℕ} (α : MultiIndex d) (k : ℕ) : ∀ f : SchwartzMap (Euc d) ℝ,
    ∫ x, ((oscillatorOp (d := d))^[k] ⇑f) x * hermiteFunD α x =
      oscEigenvalue d α ^ k * ∫ x, f x * hermiteFunD α x := by
  induction k with
  | zero => intro f; simp
  | succ k ih =>
    intro f
    obtain ⟨H, hH⟩ := schwartz_iter_exists 1 f
    rw [Function.iterate_one] at hH
    have hHx : ∀ x, H x = oscillatorOp (⇑f) x := fun x => by rw [hH]
    have e : (oscillatorOp (d := d))^[k + 1] ⇑f = (oscillatorOp (d := d))^[k] ⇑H := by
      rw [Function.iterate_succ_apply, hH]
    rw [e, ih H]
    have hs : ∫ x, H x * hermiteFunD α x = oscEigenvalue d α * ∫ x, f x * hermiteFunD α x := by
      simp_rw [hHx]
      exact sym_oscillatorOp_hermite α f
    rw [hs]
    ring

/-- Parseval in the Hermite basis for `L²` functions (copy of the argument of `oscNorm_zero`). -/
theorem hermite_parseval_aux {d : ℕ} (g : Euc d → ℝ) (hg : MemLp g 2 (volume : Measure (Euc d))) :
    Summable (fun α : MultiIndex d => hermiteCoeff g α ^ 2) ∧
      ∑' α : MultiIndex d, hermiteCoeff g α ^ 2 = ∫ x, g x ^ 2 := by
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  set F := hg.toLp g with hF
  have h1 : ∀ α, (b.repr F : lp (fun _ : MultiIndex d => ℝ) 2) α = hermiteCoeff g α := by
    intro α
    rw [HilbertBasis.repr_apply_apply, hb α, hF, OscSpace.inner_hermiteLpD_toLp g hg α]
  have hsum : Summable (fun α : MultiIndex d => hermiteCoeff g α ^ 2) :=
    (lp_two_summable (ι := MultiIndex d) (b.repr F)).congr fun α => by rw [h1 α]
  refine ⟨hsum, ?_⟩
  have h2 : ‖F‖ ^ 2 = ∫ x, g x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]; simp [sq]
  have h3 : ‖F‖ ^ 2 = ∑' α : MultiIndex d, hermiteCoeff g α ^ 2 := by
    rw [← b.repr.norm_map, lp_two_norm_sq]
    exact tsum_congr fun α => by rw [h1]
  rw [← h3]
  exact h2

/-- `x^{2k} = (x^k)^2` for the real exponent `2k`. -/
theorem rpow_two_mul_nat (x : ℝ) (k : ℕ) : x ^ (2 * (k : ℝ)) = (x ^ k) ^ 2 := by
  rw [show 2 * (k : ℝ) = ((k * 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul]


/-- `Σ^m` membership via the operator: for even `m = 2k` and Schwartz `f`,
`f ∈ Σ^{2k}` and `‖f‖_{Σ^{2k}} = ‖𝓗^k f‖₂` (`H:eq:oscillator-space`, lines 355-357). -/
theorem oscNorm_even_eq (k : ℕ) (f : SchwartzMap (Euc d) ℝ) :
    MemOsc (2 * (k : ℝ)) f ∧
      oscNorm (2 * (k : ℝ)) f = Real.sqrt (∫ x, ((oscillatorOp (d := d))^[k] f x) ^ 2) := by
  obtain ⟨G, hG⟩ := schwartz_iter_exists k f
  have hgmem : MemLp ((oscillatorOp (d := d))^[k] ⇑f) 2 (volume : Measure (Euc d)) := by
    rw [← hG]
    exact G.memLp 2
  have hcoef : ∀ α : MultiIndex d, hermiteCoeff ((oscillatorOp (d := d))^[k] ⇑f) α =
      oscEigenvalue d α ^ k * hermiteCoeff f α := fun α => coeff_iter α k f
  obtain ⟨hsum, hpar⟩ := hermite_parseval_aux _ hgmem
  have hpow : ∀ α : MultiIndex d, oscEigenvalue d α ^ (2 * (k : ℝ)) * hermiteCoeff f α ^ 2 =
      hermiteCoeff ((oscillatorOp (d := d))^[k] ⇑f) α ^ 2 := by
    intro α
    rw [rpow_two_mul_nat, hcoef α]
    ring
  refine ⟨⟨f.memLp 2, hsum.congr fun α => (hpow α).symm⟩, ?_⟩
  unfold oscNorm
  rw [tsum_congr hpow, hpar]

/-- Schwartz functions belong to every `Σ^m` (`C_c^∞ ⊂ 𝓢 ⊂ Σ^m`). -/
theorem memOsc_schwartz (m : ℝ) (f : SchwartzMap (Euc d) ℝ) : MemOsc m f := by
  obtain ⟨hmem, -⟩ := oscNorm_even_eq (d := d) (⌈|m|⌉₊) f
  obtain ⟨hL2, hsum⟩ := hmem
  have hk : m ≤ 2 * ((⌈|m|⌉₊ : ℕ) : ℝ) := by
    have h1 : |m| ≤ ((⌈|m|⌉₊ : ℕ) : ℝ) := Nat.le_ceil |m|
    have h2 : m ≤ |m| := le_abs_self m
    have h3 : (0 : ℝ) ≤ ((⌈|m|⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  refine ⟨hL2, Summable.of_nonneg_of_le (fun α => ?_) (fun α => ?_) hsum⟩
  · exact mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (oscEv_one_le α) hk) (sq_nonneg _)

/-- `oscNorm` is monotone in `m` and `‖f‖_{Σ^0} = ‖f‖_{L²}` (Parseval). -/
theorem oscNorm_zero (f : Euc d → ℝ) (hf : MemLp f 2 (volume : Measure (Euc d))) :
    oscNorm 0 f = Real.sqrt (∫ x, f x ^ 2) := by
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  set F := hf.toLp f with hF
  have h1 : ∀ α, (b.repr F : lp (fun _ : MultiIndex d => ℝ) 2) α = hermiteCoeff f α := by
    intro α
    rw [HilbertBasis.repr_apply_apply, hb α, hF, OscSpace.inner_hermiteLpD_toLp f hf α]
  have h2 : ‖F‖ ^ 2 = ∫ x, f x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]; simp [sq]
  have h3 : ‖F‖ ^ 2 = ∑' α, hermiteCoeff f α ^ 2 := by
    rw [← b.repr.norm_map, lp_two_norm_sq]
    exact tsum_congr fun α => by rw [h1]
  unfold oscNorm
  rw [← h2, h3]
  simp

namespace OscSpace

/-- The sequence model is isometric to `Σ^m` on functions. -/
theorem norm_ofFun (f : Euc d → ℝ) (hf : MemOsc m f) : ‖ofFun m f‖ = oscNorm m f := by
  rw [norm_eq_coord]
  unfold oscNorm
  congr 1
  refine tsum_congr fun α => ?_
  rw [coord_ofFun_eq hf α, mul_pow, rpow_half_sq _ _ (oscEv_pos α)]

theorem coord_ofFun (f : Euc d → ℝ) (hf : MemOsc m f) (α : MultiIndex d) :
    coord (ofFun m f) α = oscEigenvalue d α ^ (m / 2) * Whole.hermiteCoeff f α := by
  rw [coord, ofFun_eq hf]

/-- `toLp ∘ ofFun` recovers the function class, for `f ∈ Σ^m`. -/
theorem toLp_ofFun (f : Euc d → ℝ) (hf : MemOsc m f) : toLp (ofFun m f) = hf.1.toLp f := by
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  have key := b.hasSum_repr (hf.1.toLp f)
  unfold toLp
  refine HasSum.tsum_eq ?_
  convert key using 2 with α
  rw [HilbertBasis.repr_apply_apply, hb α, inner_hermiteLpD_toLp f hf.1 α, hermiteCoeff_ofFun hf]

/-- For `m ≥ 0`, `Σ^m ↪ L²` is injective (the Hermite series of `f ∈ Σ^m` converges in `L²`
and determines `f`). -/
theorem toLp_injective (hm : 0 ≤ m) : Function.Injective (toLp : OscSpace d m → _) := by
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  intro f g hfg
  rw [toLp_eq_repr_symm b hb hm f, toLp_eq_repr_symm b hb hm g] at hfg
  have h1 := b.repr.symm.injective hfg
  have h2 : ∀ α, hermiteCoeff f α = hermiteCoeff g α := fun α => congrFun (congrArg Subtype.val h1) α
  have h3 : ∀ α, coord f α = coord g α := fun α => by rw [coord_eq_mul f α, coord_eq_mul g α, h2 α]
  exact lp.ext (funext h3)

/-- For `m ≥ 0` the range of `toLp` is exactly `Σ^m = {F ∈ L² : ∑ λ_α^m ⟨F,h_α⟩² < ∞}`. -/
theorem range_toLp (hm : 0 ≤ m) (F : Lp ℝ 2 (volume : Measure (Euc d))) :
    (∃ f : OscSpace d m, toLp f = F) ↔
      Summable fun α : MultiIndex d => oscEigenvalue d α ^ m * (inner ℝ F (hermiteLpD α)) ^ 2 := by
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  have hinner : ∀ α, inner ℝ F (hermiteLpD α) = inner ℝ (hermiteLpD α) F := fun α => real_inner_comm _ _
  constructor
  · rintro ⟨f, rfl⟩
    have hrep : ∀ α, inner ℝ (hermiteLpD α) (toLp f) = hermiteCoeff f α := by
      intro α
      rw [← hb α, ← HilbertBasis.repr_apply_apply, toLp_eq_repr_symm b hb hm f]
      simp
    refine (lp_two_summable (ι := MultiIndex d) f).congr fun α => ?_
    rw [hinner, hrep]
    show coord f α ^ 2 = _
    rw [coord_eq_mul f α, mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  · intro hsum
    have hmem : Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (m / 2) * inner ℝ F (hermiteLpD α)) 2 := by
      rw [memℓp_two_iff]
      refine hsum.congr fun α => ?_
      rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
    let f : OscSpace d m := (⟨_, hmem⟩ : lp (fun _ : MultiIndex d => ℝ) 2)
    refine ⟨f, ?_⟩
    rw [toLp_eq_repr_symm b hb hm f]
    have : (⟨fun α => hermiteCoeff f α, memℓp_hermiteCoeff hm f⟩ : lp (fun _ : MultiIndex d => ℝ) 2)
        = b.repr F := by
      apply lp.ext
      funext α
      show hermiteCoeff f α = _
      rw [HilbertBasis.repr_apply_apply, hb α, ← hinner]
      unfold hermiteCoeff
      show oscEigenvalue d α ^ (-(m / 2)) * (oscEigenvalue d α ^ (m / 2) * inner ℝ F (hermiteLpD α)) = _
      rw [← mul_assoc, rpow_neg_half_mul _ _ (oscEv_pos α), one_mul]
    rw [this]; simp

end OscSpace

namespace OscDual

/-- `‖u‖²_{B_m} = ∑_α λ_α^{-m} |u(h_α)|²` (`H:eq:oscillator-space`, line 356). -/
theorem norm_eq (u : OscDual d m) :
    ‖u‖ = Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (-m) * hermiteCoeff u α ^ 2) := by
  rw [norm_eq_coord]; simp_rw [hermiteCoeff_sq]

/-- `u(φ_α) = λ_α^{-m/2} u(h_α)` is the coordinate: the `B_m` norm is the `ℓ²` norm of
`(u(φ_j))_j` (cf. `H:eq:whole-initial-orbit`). -/
theorem eval_oscTestFun (u : OscDual d m) (α : MultiIndex d) :
    eval u (oscTestFun m α) = coord u α := by
  unfold eval
  rw [tsum_eq_single α]
  · rw [hermiteCoeff_oscTestFun, coord_eq_mul u α]; simp [mul_comm]
  · intro β hβ
    rw [hermiteCoeff_oscTestFun]; simp [Ne.symm hβ]

/-- The duality pairing is the Hermite pairing `∑_α u(h_α) ⟨f,h_α⟩` (`B_m = (Σ^m)'`). -/
theorem toDual_apply (u : OscDual d m) (f : OscSpace d m) :
    toDual u f = ∑' α : MultiIndex d, hermiteCoeff u α * OscSpace.hermiteCoeff f α := by
  rw [toDual_apply_coord]
  refine tsum_congr fun α => ?_
  unfold hermiteCoeff OscSpace.hermiteCoeff
  have h := oscEv_pos α
  have : oscEigenvalue d α ^ (m / 2) * coord u α *
      (oscEigenvalue d α ^ (-(m / 2)) * OscSpace.coord f α)
     = (oscEigenvalue d α ^ (-(m / 2)) * oscEigenvalue d α ^ (m / 2)) *
        (coord u α * OscSpace.coord f α) := by ring
  rw [this, rpow_neg_half_mul _ _ h, one_mul]

/-- On functions `f ∈ Σ^m` the duality pairing is `eval`. -/
theorem toDual_ofFun (u : OscDual d m) (f : Euc d → ℝ) (hf : MemOsc m f) :
    toDual u (OscSpace.ofFun m f) = eval u f := by
  unfold eval
  rw [toDual_apply]
  refine tsum_congr fun α => ?_
  rw [OscSpace.hermiteCoeff_ofFun hf]

/-- `|u(f)| ≤ ‖u‖_{B_m} ‖f‖_{Σ^m}`. -/
theorem abs_eval_le (u : OscDual d m) (f : Euc d → ℝ) (hf : MemOsc m f) :
    |eval u f| ≤ ‖u‖ * oscNorm m f := by
  rw [← toDual_ofFun u f hf, ← OscSpace.norm_ofFun f hf]
  calc |toDual u (OscSpace.ofFun m f)| = ‖toDual u (OscSpace.ofFun m f)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖toDual u‖ * ‖OscSpace.ofFun m f‖ := (toDual u).le_opNorm _
    _ = ‖u‖ * ‖OscSpace.ofFun m f‖ := by rw [LinearIsometryEquiv.norm_map]

/-- Bounded value sequences give elements of `B_m` exactly when `m > d`
(from `hermiteFunD_uniform_bound` and `summable_oscEigenvalue_rpow_iff`). -/
theorem memℓp_of_bounded (hm : (d : ℝ) < m) (c : MultiIndex d → ℝ) (hc : ∃ C, ∀ α, |c α| ≤ C) :
    Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (-(m / 2)) * c α) 2 := by
  obtain ⟨C, hC⟩ := hc
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [memℓp_two_iff]; exact Summable.of_finite
  rw [memℓp_two_iff]
  have hsum := (summable_oscEigenvalue_rpow_iff (d := d) hd m).2 hm
  refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) (hsum.mul_left (C ^ 2))
  have h := oscEv_pos α
  rw [mul_pow, show (oscEigenvalue d α ^ (-(m / 2))) ^ 2 = oscEigenvalue d α ^ (-m) from by
    rw [← rpow_half_sq (-m) _ h, neg_div]]
  have : c α ^ 2 ≤ C ^ 2 := by
    have := hC α
    exact sq_le_sq' (by linarith [abs_nonneg (c α), neg_abs_le (c α)]) (le_trans (le_abs_self _) this)
  nlinarith [Real.rpow_pos_of_pos h (-m)]

theorem coord_ofSeq_of_mem (c : MultiIndex d → ℝ)
    (h : Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (-(m / 2)) * c α) 2) (α : MultiIndex d) :
    coord (ofSeq m c) α = oscEigenvalue d α ^ (-(m / 2)) * c α := by
  have : ofSeq m c = (⟨fun α : MultiIndex d => oscEigenvalue d α ^ (-(m / 2)) * c α, h⟩ :
      lp (fun _ : MultiIndex d => ℝ) 2) := by
    unfold ofSeq; exact dif_pos h
  rw [coord, this]

/-- `|μ(h_α)| ≤ C μ(ℝ^d)` with Cramér's constant `C`. -/
theorem abs_measureHermiteCoeff_le (μ : Measure (Euc d)) [IsFiniteMeasure μ] :
    ∃ C : ℝ, ∀ α : MultiIndex d, |measureHermiteCoeff μ α| ≤ C * (μ Set.univ).toReal := by
  obtain ⟨C, hC⟩ := hermiteFunD_uniform_bound (d := d)
  refine ⟨C, fun α => ?_⟩
  unfold measureHermiteCoeff
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := hermiteFunD α) (C := C)
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC α x)
  simpa [Real.norm_eq_abs, Measure.real, mul_comm] using this

/-- `∑_α λ_α^{-m} < ∞` for `m > d` (also for `d = 0`, where the index set is a singleton). -/
theorem summable_oscEv_neg_rpow (hm : (d : ℝ) < m) :
    Summable fun α : MultiIndex d => oscEigenvalue d α ^ (-m) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Summable.of_finite
  · exact (summable_oscEigenvalue_rpow_iff hd m).2 hm

/-- `∑_α |⟨f,h_α⟩| < ∞` for `f ∈ Σ^m` and `m > d`, by `|a| ≤ (λ^{-m} + λ^m a²)/2`. -/
theorem summable_abs_hermiteCoeff (hm : (d : ℝ) < m) {f : Euc d → ℝ} (hf : MemOsc m f) :
    Summable fun α : MultiIndex d => |Whole.hermiteCoeff f α| := by
  refine Summable.of_nonneg_of_le (fun α => abs_nonneg _) (fun α => ?_)
    (((summable_oscEv_neg_rpow hm).add hf.2).div_const 2)
  show |Whole.hermiteCoeff f α| ≤
    (oscEigenvalue d α ^ (-m) + oscEigenvalue d α ^ m * Whole.hermiteCoeff f α ^ 2) / 2
  have h := oscEv_pos α
  have hpq : oscEigenvalue d α ^ (-(m / 2)) * oscEigenvalue d α ^ (m / 2) = 1 :=
    rpow_neg_half_mul _ _ h
  have hp2 : (oscEigenvalue d α ^ (m / 2)) ^ 2 = oscEigenvalue d α ^ m := rpow_half_sq _ _ h
  have hq2 : (oscEigenvalue d α ^ (-(m / 2))) ^ 2 = oscEigenvalue d α ^ (-m) := by
    rw [← rpow_half_sq (-m) _ h, neg_div]
  have expand : (oscEigenvalue d α ^ (-(m / 2))
      - oscEigenvalue d α ^ (m / 2) * |Whole.hermiteCoeff f α|) ^ 2
      = (oscEigenvalue d α ^ (-(m / 2))) ^ 2
        - 2 * |Whole.hermiteCoeff f α| * (oscEigenvalue d α ^ (-(m / 2)) * oscEigenvalue d α ^ (m / 2))
        + (oscEigenvalue d α ^ (m / 2)) ^ 2 * Whole.hermiteCoeff f α ^ 2 := by
    rw [← sq_abs (Whole.hermiteCoeff f α)]; ring
  rw [hpq, hp2, hq2] at expand
  linarith [sq_nonneg (oscEigenvalue d α ^ (-(m / 2))
      - oscEigenvalue d α ^ (m / 2) * |Whole.hermiteCoeff f α|)]

/-- For a finite measure `μ` and absolutely summable Hermite coefficients,
`(μ(h_α) ⟨φ,h_α⟩)_α` is absolutely summable. -/
theorem summable_measureHermiteCoeff_mul (μ : Measure (Euc d)) [IsFiniteMeasure μ]
    {φ : Euc d → ℝ} (hsum : Summable fun α : MultiIndex d => |Whole.hermiteCoeff φ α|) :
    Summable fun α : MultiIndex d => measureHermiteCoeff μ α * Whole.hermiteCoeff φ α := by
  obtain ⟨C, hC⟩ := abs_measureHermiteCoeff_le μ
  refine Summable.of_norm_bounded (hsum.mul_left (C * (μ Set.univ).toReal)) fun α => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC α) (abs_nonneg _)

/-- Multiplying the compactly supported `g` by any function keeps compact support. -/
theorem hasCompactSupport_mul_of {u g : Euc d → ℝ} (hgs : HasCompactSupport g) :
    HasCompactSupport (fun y => u y * g y) :=
  HasCompactSupport.mul_left (f := u) hgs

/-- `⟨f,k⟩_{L²} = ∫ f k` for functions in `L²`. -/
theorem inner_toLp_mul (f k : Euc d → ℝ) (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hk : MemLp k 2 (volume : Measure (Euc d))) :
    inner ℝ (hf.toLp f) (hk.toLp k) = ∫ y, f y * k y := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hk.coeFn_toLp] with y h1 h2
  rw [h1, h2]; simp [mul_comm]

/-- Pointwise Hermite expansion: a continuous `L²` function with absolutely summable Hermite
coefficients equals the everywhere-convergent series `∑_α ⟨φ,h_α⟩ h_α`. -/
theorem hermite_expansion_of_summable {φ : Euc d → ℝ} (hφc : Continuous φ)
    (hφ2 : MemLp φ 2 (volume : Measure (Euc d)))
    (hsum : Summable fun α : MultiIndex d => |Whole.hermiteCoeff φ α|) (x : Euc d) :
    φ x = ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α x := by
  obtain ⟨C, hC⟩ := hermiteFunD_uniform_bound (d := d)
  have hbd : ∀ (α : MultiIndex d) (y : Euc d),
      ‖Whole.hermiteCoeff φ α * hermiteFunD α y‖ ≤ |Whole.hermiteCoeff φ α| * C := by
    intro α y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC α y) (abs_nonneg _)
  have hGc : Continuous fun y : Euc d =>
      ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y :=
    continuous_tsum (f := fun (α : MultiIndex d) (y : Euc d) =>
        Whole.hermiteCoeff φ α * hermiteFunD α y)
      (fun α => (contDiff_hermiteFunD α).continuous.const_mul _) (hsum.mul_right C) hbd
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  have hc : ∀ α : MultiIndex d, inner ℝ (hφ2.toLp φ) (b α) = Whole.hermiteCoeff φ α :=
    fun α => by
      rw [hb α, real_inner_comm]
      exact OscSpace.inner_hermiteLpD_toLp φ hφ2 α
  -- Parseval against smooth compactly supported test functions `g`
  have hpars : ∀ g : Euc d → ℝ, Continuous g → HasCompactSupport g →
      HasSum (fun α : MultiIndex d => Whole.hermiteCoeff φ α * ∫ y, hermiteFunD α y * g y)
        (∫ y, φ y * g y) := by
    intro g hgc hgs
    have hg2 : MemLp g 2 (volume : Measure (Euc d)) := hgc.memLp_of_hasCompactSupport hgs
    have hd : ∀ α : MultiIndex d, inner ℝ (b α) (hg2.toLp g) = ∫ y, hermiteFunD α y * g y :=
      fun α => by
        rw [hb α, hermiteLpD_eq α]
        exact inner_toLp_mul _ _ _ _
    have hip := HilbertBasis.hasSum_inner_mul_inner b (hφ2.toLp φ) (hg2.toLp g)
    rw [inner_toLp_mul φ g hφ2 hg2] at hip
    have hfun : (fun α : MultiIndex d => inner ℝ (hφ2.toLp φ) (b α) * inner ℝ (b α) (hg2.toLp g))
        = fun α : MultiIndex d => Whole.hermiteCoeff φ α * ∫ y, hermiteFunD α y * g y :=
      funext fun α => by rw [hc α, hd α]
    rw [hfun] at hip
    exact hip
  -- The same series integrated against `g` (uniform convergence, dominated by `|a_α| C |g|`)
  have hGpars : ∀ g : Euc d → ℝ, Continuous g → HasCompactSupport g →
      HasSum (fun α : MultiIndex d => Whole.hermiteCoeff φ α * ∫ y, hermiteFunD α y * g y)
        (∫ y, (∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y) * g y) := by
    intro g hgc hgs
    have hgi : Integrable g (volume : Measure (Euc d)) := hgc.integrable_of_hasCompactSupport hgs
    have hF : ∀ α : MultiIndex d,
        Continuous fun y => Whole.hermiteCoeff φ α * hermiteFunD α y * g y :=
      fun α => ((contDiff_hermiteFunD α).continuous.const_mul _).mul hgc
    have hint : ∀ α : MultiIndex d,
        Integrable (fun y => Whole.hermiteCoeff φ α * hermiteFunD α y * g y) volume :=
      fun α => (hF α).integrable_of_hasCompactSupport (hasCompactSupport_mul_of hgs)
    have hnorm : ∀ α : MultiIndex d, ∫ y, ‖Whole.hermiteCoeff φ α * hermiteFunD α y * g y‖
        ≤ |Whole.hermiteCoeff φ α| * C * ∫ y, ‖g y‖ := fun α => by
      rw [← integral_const_mul]
      refine integral_mono (hint α).norm (hgi.norm.const_mul _) fun y => ?_
      show ‖Whole.hermiteCoeff φ α * hermiteFunD α y * g y‖
        ≤ |Whole.hermiteCoeff φ α| * C * ‖g y‖
      have hh : ‖hermiteFunD α y‖ ≤ C := by
        rw [Real.norm_eq_abs]; exact hC α y
      rw [norm_mul, norm_mul, Real.norm_eq_abs (Whole.hermiteCoeff φ α)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (abs_nonneg _))
        (norm_nonneg _)
    have hsumN : Summable fun α : MultiIndex d =>
        ∫ y, ‖Whole.hermiteCoeff φ α * hermiteFunD α y * g y‖ :=
      Summable.of_nonneg_of_le (fun α => integral_nonneg fun y => norm_nonneg _) hnorm
        ((hsum.mul_right C).mul_right (∫ y, ‖g y‖))
    have hH := hasSum_integral_of_summable_integral_norm hint hsumN
    convert hH using 1
    · funext α
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    · congr 1
      funext y
      rw [tsum_mul_right]
  have hφg : ∀ g : Euc d → ℝ, Continuous g → HasCompactSupport g →
      Integrable (fun y => φ y * g y) volume :=
    fun g hgc hgs => (hφc.mul hgc).integrable_of_hasCompactSupport (hasCompactSupport_mul_of hgs)
  have hGg : ∀ g : Euc d → ℝ, Continuous g → HasCompactSupport g →
      Integrable (fun y => (∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y) * g y)
        volume :=
    fun g hgc hgs => (hGc.mul hgc).integrable_of_hasCompactSupport (hasCompactSupport_mul_of hgs)
  -- Fundamental lemma: `φ - G` vanishes a.e., hence everywhere (both continuous)
  have hae : ∀ᵐ y ∂(volume : Measure (Euc d)),
      φ y - ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hφc.sub hGc).locallyIntegrable ?_
    intro g hgdiff hgs
    have hgc : Continuous g := hgdiff.continuous
    have e : ∫ y, φ y * g y
        = ∫ y, (∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y) * g y :=
      (hpars g hgc hgs).unique (hGpars g hgc hgs)
    have hsplit : (fun y => g y • (φ y - ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y))
        = fun y => φ y * g y
          - (∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y) * g y := by
      funext y
      simp only [smul_eq_mul]
      ring
    show ∫ y, g y • (φ y - ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y) = 0
    rw [hsplit, integral_sub (hφg g hgc hgs) (hGg g hgc hgs), e, sub_self]
  have hφG : φ = fun y => ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y := by
    refine (Continuous.ae_eq_iff_eq volume hφc hGc).1 ?_
    filter_upwards [hae] with y hy
    exact sub_eq_zero.1 hy
  exact congrFun hφG x

/-- For a finite measure `μ` and `φ` with absolutely summable Hermite coefficients and pointwise
Hermite expansion: `∫ φ dμ = ∑_α μ(h_α) ⟨φ,h_α⟩` (dominated interchange of sum and integral). -/
theorem integral_eq_tsum_hermite (μ : Measure (Euc d)) [IsFiniteMeasure μ] {φ : Euc d → ℝ}
    (hsum : Summable fun α : MultiIndex d => |Whole.hermiteCoeff φ α|)
    (hexp : ∀ x, φ x = ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α x) :
    ∫ x, φ x ∂μ = ∑' α : MultiIndex d, measureHermiteCoeff μ α * Whole.hermiteCoeff φ α := by
  obtain ⟨C, hC⟩ := hermiteFunD_uniform_bound (d := d)
  have hbd : ∀ (α : MultiIndex d) (y : Euc d),
      ‖Whole.hermiteCoeff φ α * hermiteFunD α y‖ ≤ |Whole.hermiteCoeff φ α| * C := by
    intro α y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC α y) (abs_nonneg _)
  have hint : ∀ α : MultiIndex d,
      Integrable (fun y => Whole.hermiteCoeff φ α * hermiteFunD α y) μ := fun α =>
    (integrable_const (|Whole.hermiteCoeff φ α| * C)).mono'
      ((contDiff_hermiteFunD α).continuous.const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hbd α y)
  have hnorm : ∀ α : MultiIndex d, ∫ y, ‖Whole.hermiteCoeff φ α * hermiteFunD α y‖ ∂μ
      ≤ μ.real Set.univ * (|Whole.hermiteCoeff φ α| * C) := fun α => by
    have := integral_mono (hint α).norm (integrable_const (|Whole.hermiteCoeff φ α| * C))
      (fun y => hbd α y)
    rwa [integral_const, smul_eq_mul] at this
  have hsumN : Summable fun α : MultiIndex d =>
      ∫ y, ‖Whole.hermiteCoeff φ α * hermiteFunD α y‖ ∂μ :=
    Summable.of_nonneg_of_le (fun α => integral_nonneg fun y => norm_nonneg _) hnorm
      ((hsum.mul_right C).mul_left (μ.real Set.univ))
  have hH := hasSum_integral_of_summable_integral_norm hint hsumN
  have h1 : ∫ y, φ y ∂μ = ∫ y, ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α y ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hexp)
  rw [h1, ← hH.tsum_eq]
  refine tsum_congr fun α => ?_
  unfold measureHermiteCoeff
  rw [integral_const_mul, mul_comm]

/-- For `m > d` the embedding of a finite signed measure is the honest weighted sequence. -/
theorem hermiteCoeff_ofMeasureDiff (hm : (d : ℝ) < m) (μ ν : Measure (Euc d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (α : MultiIndex d) :
    hermiteCoeff (ofMeasureDiff m μ ν) α = measureHermiteCoeff μ α - measureHermiteCoeff ν α := by
  obtain ⟨Cμ, hCμ⟩ := abs_measureHermiteCoeff_le μ
  obtain ⟨Cν, hCν⟩ := abs_measureHermiteCoeff_le ν
  have hc : ∃ K : ℝ, ∀ β : MultiIndex d,
      |measureHermiteCoeff μ β - measureHermiteCoeff ν β| ≤ K :=
    ⟨Cμ * (μ Set.univ).toReal + Cν * (ν Set.univ).toReal, fun β =>
      (abs_sub _ _).trans (add_le_add (hCμ β) (hCν β))⟩
  have hmem := memℓp_of_bounded hm (fun β => measureHermiteCoeff μ β - measureHermiteCoeff ν β) hc
  unfold ofMeasureDiff hermiteCoeff
  rw [coord_ofSeq_of_mem _ hmem α]
  have h := rpow_neg_half_mul m _ (oscEv_pos α)
  linear_combination (measureHermiteCoeff μ α - measureHermiteCoeff ν α) * h

/-- For `m > d` and Schwartz tests, the pairing of an embedded signed measure is the integral:
`(μ - ν)(φ) = ∫ φ dμ - ∫ φ dν`. -/
theorem eval_ofMeasureDiff (hm : (d : ℝ) < m) (μ ν : Measure (Euc d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (φ : SchwartzMap (Euc d) ℝ) :
    eval (ofMeasureDiff m μ ν) φ = ∫ x, φ x ∂μ - ∫ x, φ x ∂ν := by
  have hM : MemOsc m φ := memOsc_schwartz m φ
  have hsum := summable_abs_hermiteCoeff hm hM
  have hexp : ∀ x, φ x = ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α x :=
    fun x => hermite_expansion_of_summable φ.continuous hM.1 hsum x
  have hsμ := summable_measureHermiteCoeff_mul μ hsum
  have hsν := summable_measureHermiteCoeff_mul ν hsum
  calc eval (ofMeasureDiff m μ ν) φ
      = ∑' α : MultiIndex d, (measureHermiteCoeff μ α * Whole.hermiteCoeff φ α
          - measureHermiteCoeff ν α * Whole.hermiteCoeff φ α) := by
        unfold eval
        exact tsum_congr fun α => by
          rw [hermiteCoeff_ofMeasureDiff hm μ ν α]; ring
    _ = ∑' α : MultiIndex d, measureHermiteCoeff μ α * Whole.hermiteCoeff φ α
          - ∑' α : MultiIndex d, measureHermiteCoeff ν α * Whole.hermiteCoeff φ α :=
        hsμ.tsum_sub hsν
    _ = ∫ x, φ x ∂μ - ∫ x, φ x ∂ν := by
        rw [integral_eq_tsum_hermite μ hsum hexp, integral_eq_tsum_hermite ν hsum hexp]

/-- Duality `|∫ φ d(μ-ν)| ≤ ‖μ-ν‖_{B_m} ‖φ‖_{Σ^m}` for `m > d` and Schwartz `φ`. -/
theorem abs_integral_sub_le (hm : (d : ℝ) < m) (μ ν : Measure (Euc d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (φ : SchwartzMap (Euc d) ℝ) :
    |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ ‖ofMeasureDiff m μ ν‖ * oscNorm m φ := by
  rw [← eval_ofMeasureDiff hm μ ν φ]
  exact abs_eval_le _ _ (memOsc_schwartz m φ)

/-- `B_m ↪ B_{m'}` is a contraction for `m ≤ m'`. -/
theorem norm_embed_le (m' : ℝ) (hmm' : m ≤ m') (u : OscDual d m) : ‖embed m' u‖ ≤ ‖u‖ := by
  have hb : ∀ α, |oscEigenvalue d α ^ (-(m' / 2)) * hermiteCoeff u α| ≤ |coord u α| := by
    intro α
    have h := oscEv_pos α
    have : oscEigenvalue d α ^ (-(m' / 2)) * hermiteCoeff u α =
        oscEigenvalue d α ^ ((m - m') / 2) * coord u α := by
      rw [coord_eq_mul u α, ← mul_assoc, ← Real.rpow_add h]; congr 2; ring
    rw [this, abs_mul, abs_of_pos (Real.rpow_pos_of_pos h _)]
    have : oscEigenvalue d α ^ ((m - m') / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (oscEv_one_le α) (by linarith)
    nlinarith [abs_nonneg (coord u α)]
  have hmem : Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (-(m' / 2)) * hermiteCoeff u α) 2 := by
    rw [memℓp_two_iff]
    refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) (coord_sq_summable' u)
    rw [← sq_abs, ← sq_abs (coord u α)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb α) 2
  rw [norm_eq_coord, norm_eq_coord]
  apply Real.sqrt_le_sqrt
  refine (coord_sq_summable' (embed m' u)).tsum_le_tsum (fun α => ?_) (coord_sq_summable' u)
  rw [← sq_abs, ← sq_abs (coord u α)]
  have : coord (embed m' u) α = oscEigenvalue d α ^ (-(m' / 2)) * hermiteCoeff u α :=
    coord_ofSeq_of_mem _ hmem α
  rw [this]
  exact pow_le_pow_left₀ (abs_nonneg _) (hb α) 2

/-- The mass, where defined, is unique (cutoffs exist). -/
theorem hasMass_unique (u : OscDual d m) {c c' : ℝ} (h : HasMass u c) (h' : HasMass u c') :
    c = c' := by
  obtain ⟨χ, hχ⟩ : ∃ χ : Euc d → ℝ, IsCutoff χ := by
    let b : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
    refine ⟨b, ⟨b.contDiff, b.hasCompactSupport, ?_⟩⟩
    filter_upwards [Metric.closedBall_mem_nhds (0 : Euc d) one_pos] with x hx
    exact b.one_of_mem_closedBall hx
  exact tendsto_nhds_unique (h χ hχ) (h' χ hχ)

/-- The mass functional on a dilated cutoff: `∫ χ(·/R) dμ → μ(ℝ^d)` for a finite measure `μ`. -/
theorem tendsto_integral_dilate (μ : Measure (Euc d)) [IsFiniteMeasure μ] {χ : Euc d → ℝ}
    (hχ : IsCutoff χ) :
    Tendsto (fun R : ℝ => ∫ x, dilate R χ x ∂μ) atTop (𝓝 (μ Set.univ).toReal) := by
  obtain ⟨K, hK⟩ := hχ.smooth.continuous.bounded_above_of_compact_support hχ.compactSupport
  have hχ0 : χ 0 = 1 := hχ.one_near_zero.self_of_nhds
  have hlim : ∀ x : Euc d, Tendsto (fun R : ℝ => dilate R χ x) atTop (𝓝 1) := by
    intro x
    have h1 : Tendsto (fun R : ℝ => R⁻¹ • x) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const x
    have h2 := (hχ.smooth.continuous.tendsto (0 : Euc d)).comp h1
    rw [hχ0] at h2
    exact h2
  have hcont : ∀ R : ℝ, Continuous (dilate R χ) := fun R =>
    hχ.smooth.continuous.comp (continuous_const_smul R⁻¹)
  have key := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun (R : ℝ) (x : Euc d) => dilate R χ x) (f := fun _ => (1 : ℝ)) (fun _ => K)
    (Filter.Eventually.of_forall fun R => (hcont R).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => hK (R⁻¹ • x))
    (integrable_const K) (Filter.Eventually.of_forall fun x => hlim x)
  simpa [integral_const, Measure.real] using key

/-- The subclass used by the source: embedded differences of finite measures have mass
`μ(ℝ^d) - ν(ℝ^d)` (for `m > d`). -/
theorem hasMass_ofMeasureDiff (hm : (d : ℝ) < m) (μ ν : Measure (Euc d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    HasMass (ofMeasureDiff m μ ν) ((μ Set.univ).toReal - (ν Set.univ).toReal) := by
  intro χ hχ
  have hμ := tendsto_integral_dilate μ hχ
  have hν := tendsto_integral_dilate ν hχ
  refine Tendsto.congr' ?_ (hμ.sub hν)
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hcs : HasCompactSupport (dilate R χ) :=
    hχ.compactSupport.comp_smul (inv_ne_zero hR.ne')
  have hsm : ContDiff ℝ ∞ (dilate R χ) := hχ.smooth.comp (contDiff_id.const_smul R⁻¹)
  exact (eval_ofMeasureDiff hm μ ν (hcs.toSchwartzMap hsm)).symm

/-- Differences of probability measures (e.g. `μ_N - μ`, `μ_N - m_N`) have zero mass. -/
theorem hasZeroMass_ofMeasureDiff (hm : (d : ℝ) < m) (μ ν : Measure (Euc d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    HasZeroMass (ofMeasureDiff m μ ν) := by
  have h := hasMass_ofMeasureDiff hm μ ν
  have h0 : (μ Set.univ).toReal - (ν Set.univ).toReal = 0 := by simp
  rw [h0] at h
  exact h

end OscDual

end Facts

end HRS.Whole
