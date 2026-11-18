import HRS.Uniform.Q45Fnl6

/-!
# COMP-28, part 1: statement check, chain plan, and the window/plain-evolution base layer
(packet COMP-28, Proposition 3.28 `comparison_smooth`, `comparison_wasserstein`; namespace `HRS.Uniform.Comp28`)

## STATEMENT CHECK (2026-10-17)

**`comparison_smooth`** (Comparison.lean:353).  TRUE as stated; no junk-value problem found.
* `V 0 0 = 1` and `‖V 0 0‖ ≤ K` force `K ≥ 1` unless `H` is trivial, so the constants `K e^{-ca}`, `K²/2` are the honest
  Gaussian-interpolation constants (`Lip(Φ) ≤ 1`, `‖D²Φ‖ ≤ 1` on the `C_b²` unit ball: `cbNorm 2 ≤ 1` is the *sum*).
  They are SHARP, hence the proved 3.21 `smooth_path_comparison_proof` (constant `detConst(T,K)²`, unweighted
  `∫_0^T`, window `a = 0`) does NOT imply it: a window `a > 0` needs the per-block weights `w_a(r) = e^{-c(a-r)_+}`.
* `a + T = 0` (so `a = T = 0`) is the degenerate point window; `T = 0 < a` is a genuine point window.
* All quantities are `ℝ≥0∞`-valued lintegrals (`ofReal` of nonnegative terms), so no Bochner junk; `Sg r ω - Cb r` is
  a.e. a difference of trace-class forms (`sigma_traceClass`, `IsDetCovDensity.traceClass`), so `traceNormForm` is the honest norm.
* The law of `windowPath a T X` is a push-forward (not the junk measure `0`): `Z t, Zb t, R t` measurable and a.s. continuous,
  `V(·,0)x` continuous (strong continuity), see `Comp28.aemeasurable_windowPath_a`.

**`comparison_wasserstein`** (Comparison.lean:394).  TRUE as stated (the TeX proof applies); points checked:
* `C` is chosen after `(K,c,T,Cmax,p)` and before `a`, the spaces and the processes: uniform in the window start, as required.
* `MaxWindows V T Cmax` quantifies over all windows `a' ≥ 0` of ONE evolution `V` that is only an evolution on `[0, a+T]`; beyond
  `a+T` it constrains the junk values of `V`.  This only strengthens a hypothesis (the statement is weaker, harmless); only the
  window `a' = a` is used.  `MaxWindows.{u}` quantifies over `Type u` sample spaces, and `hilbert_polar_coupling` returns its
  enlargement in `Type uΩ`, so the enlargement is admissible (this is why `Ω : Type u`).
* SPEC FLAG 2 (uniqueness in law): `G` is only an `ℱ`-martingale with deterministic covariation; `hilbert_polar_coupling` returns a
  different Gaussian martingale `G' = ∫ Sb dB` on the enlargement.  Independence of `G` from `ℱ_0` and Gaussianity are NOT
  hypotheses but are consequences of Lévy's characterisation (finite-dimensional coordinates, `HRS/Stochastic/DDS.lean`
  `levy_characterization`); the identification `law(X₀', Zb-path) = law(X₀'∘π, convolution of G')` is exactly the
  glue of `gf_law_identification_proof` (GFB4Aux1-10), which is written for `NegSobolev` and has `Indep` as a hypothesis,
  so it must be re-derived abstractly (plan W1-W2).  The continuity of the convolution of `G'` (needed by `MaxWindows`, which
  takes a continuous `Z`) is transported through this law identification.
* The Itô-isometry history bound needs the POINTWISE (in `r,ω`) polar structure (`IsSqrtOfForm S, Sb`, Powers-Størmer
  `‖S - Sb‖²_{𝔖₂} ≤ ‖Σ - Σ̄‖₁`), not only the final-time `L²` bound given by the last conjunct of `hilbert_polar_coupling`.
No hypothesis needs to be added; nothing was found false.  (Risk: `Cmax < 0` makes `MaxWindows` contradictory, vacuous case.)

## CHAIN PLAN

Notation: `T' = a + T`, `wt r = exp(-c max(a-r,0))` (nondecreasing, `≤ 1`, equal to `1` on `[a,∞)`).
Smooth part (new code `HRS.Uniform.Comp28`, in the Q45 grid/Lindeberg pipeline; the Q45 files carry `S.MaxHyp`
(generator/`deriv`) which a plain evolution cannot satisfy, but the closure of `smooth_pos_final` uses only `cont_E` and the
norm bound, so the S-dependent lemmas are re-proved for `plainData V` with an explicit weighted bound):
* S1 (Aux1, this file, ~150 lines): `plainData V : EvolData H H`, the window restriction `resWin a T : PathSp (a+T) →L PathSp T`
  (`‖resWin‖ ≤ 1`), `windowPath a T = resWin ∘ windowPath 0 (a+T)` a.e., measurability, `‖res(hatPath v)‖` from the window nodes only.
* S2 (Aux2, ~130): `finite_comparison_w` = `Q45.finite_comparison` with a block-dependent constant `Kf k`; conclusion
  `½ E∫ Kf(blk σ)² ‖Σ-Cb‖`.  Same proof, only `hAρ`/`hpt`/`hν_int` made blockwise.
* S3 (Aux3, ~250): `pathMap_block_bound_w` (`‖res(pathMap(..block k..))‖ ≤ K e^{cT'/g} wt(r_k) ‖x‖`) and
  `path_grid_comparison_w` (grid comparison for `Φ ∘ resWin`: `½K²e^{2cT'/g} E∫ wt²‖Σ-Cb‖`, using `rr(blk σ) ≤ σ`, `wt` monotone).
* S4 (Aux4, ~250): `vpathW` (initial path from continuity only), `core_limit_w`, `clt_core_w`: for `Φ` in the window ball,
  `|∫Φ(res(vpath+Z)) - ∫Φ(res(vpath+Zb))| ≤ ½K² E∫wt²‖Σ-Cb‖` (the factor `e^{2cT'/g} → 1` absorbed in the `ε`-argument).
* S5 (Aux5, ~350): assembly `smooth_pos_w` (X→Y₁ remainder, Y₁→Y₂ initial `K e^{-ca}`, Y₂→Y₃ CLT), the lintegral/real bridge for the
  weighted discrepancy, the degenerate case `a = T = 0`; `Comp28Final.lean`: `comparison_smooth_proof`.
Wasserstein part (after smooth):
* W1 (~700): abstract law identification (Lévy for `ℱ`-martingale `G` with deterministic covariation ⇒ jointly Gaussian,
  independent of `ℱ_0`; same law as the polar `G'`), `(X₀', Zb)` window law = `(X₀'∘π, ∫V dG')` window law.
* W2 (~500): `IsStochConv` for the difference martingale started at `a` (cocycle splitting
  `∫_a^t V(t,r)dD = Z_D(t) - V(t,a) Z_D(a)`), continuity transfer, `IsHilbertMartingaleWithCovariation` for `D = M∘π - G'`.
* W3 (~500): history bound `E‖Z_D(a)‖² ≤ K² E∫_0^a wt² tr(Sd)` (isometry for Riemann sums + continuity of `wt`),
  pointwise Powers-Størmer `tr(Sd) ≤ ‖Σ - Σ̄‖₁`.
* W4 (~400): `MaxWindows` for the window part, Minkowski in `L^p`, `p = 1,2`, `wassersteinE_le` through the coupling; `C_T` explicit.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.LindebergAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The plain evolution on `H`, as an `EvolData H H` with `j = id` (the domain/generator fields are dummies: the pipeline lemmas
re-proved in this packet use only `VE`, `j`, strong continuity and an explicit norm bound). -/
def plainData (V : ℝ → ℝ → H →L[ℝ] H) : EvolData H H where
  j := ContinuousLinearMap.id ℝ H
  VH := V
  VE := V
  D := ⊤
  A := fun _ => 0

@[simp] lemma plainData_VE (V : ℝ → ℝ → H →L[ℝ] H) : (plainData V).VE = V := rfl
@[simp] lemma plainData_j (V : ℝ → ℝ → H →L[ℝ] H) : (plainData V).j = ContinuousLinearMap.id ℝ H := rfl

/-- The weight `w_a(r) = exp(-c (a-r)_+)`. -/
def wt (c a r : ℝ) : ℝ := Real.exp (-c * max (a - r) 0)

lemma wt_pos (c a r : ℝ) : 0 < wt c a r := Real.exp_pos _

lemma wt_le_one {c : ℝ} (hc : 0 ≤ c) (a r : ℝ) : wt c a r ≤ 1 := by
  unfold wt
  rw [Real.exp_le_one_iff]
  have : 0 ≤ max (a - r) 0 := le_max_right _ _
  nlinarith

lemma wt_mono {c : ℝ} (hc : 0 ≤ c) (a : ℝ) : Monotone (wt c a) := by
  intro r s hrs
  unfold wt
  rw [Real.exp_le_exp]
  have : max (a - s) 0 ≤ max (a - r) 0 := max_le_max (by linarith) le_rfl
  nlinarith

lemma wt_continuous (c a : ℝ) : Continuous (wt c a) := by
  unfold wt; fun_prop

lemma wt_of_ge {c a r : ℝ} (h : a ≤ r) : wt c a r = 1 := by
  unfold wt
  rw [max_eq_right (by linarith)]
  simp

section Window

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The window restriction `z ↦ (s ↦ z(a+s))`, `C([0,a+T]) → C([0,T])`. -/
def resWin (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) : PathSp (a + T) E →L[ℝ] PathSp T E :=
  LinearMap.mkContinuous
    { toFun := fun z => (⟨fun s => pcm z ⟨a + (s : ℝ), by constructor <;> linarith [s.2.1, s.2.2]⟩,
        (pcm z).continuous.comp (by fun_prop)⟩ : C(Set.Icc (0 : ℝ) T, E))
      map_add' := fun z z' => rfl
      map_smul' := fun r z => rfl } 1
    (fun z => by
      rw [one_mul]
      refine norm_pcm_le _ (norm_nonneg _) fun s => ?_
      exact norm_pcm_apply_le z _)

lemma pcm_resWin {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (z : PathSp (a + T) E) (s : Set.Icc (0 : ℝ) T) :
    pcm (resWin a T ha hT z) s = pcm z ⟨a + (s : ℝ), by constructor <;> linarith [s.2.1, s.2.2]⟩ := rfl

lemma norm_resWin_le {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    ‖(resWin a T ha hT : PathSp (a + T) E →L[ℝ] PathSp T E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Where `Y(·,ω)` is continuous on `[0,a+T]`, its window path is the restriction of its full path. -/
lemma pcm_windowPath_a {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (Y : ℝ → Ω → E) {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) (s : Set.Icc (0 : ℝ) T) :
    pcm (windowPath a T Y ω) s = Y (a + (s : ℝ)) ω := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y (a + (t : ℝ)) ω := by
    have h1 : ContinuousOn (fun t : ℝ => Y (a + t) ω) (Set.Icc 0 T) :=
      hω.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact continuousOn_iff_continuous_restrict.1 h1
  have h : windowPath a T Y ω = (⟨fun t => Y (a + (t : ℝ)) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
    unfold windowPath
    exact dif_pos hc
  rw [h]
  rfl

lemma windowPath_eq_resWin {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (Y : ℝ → Ω → E) {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    windowPath a T Y ω = resWin a T ha hT (windowPath 0 (a + T) Y ω) := by
  refine pcm_ext fun s => ?_
  rw [pcm_windowPath_a ha hT Y hω, pcm_resWin]
  rw [pcm_windowPath Y hω]

end Window

end HRS.Uniform.Comp28
