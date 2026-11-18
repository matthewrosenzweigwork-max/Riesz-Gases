import HRS.PDE.TorusFPSpec

/-!
# Packet D3 (specification): free-energy identities and inequalities for the torus Fokker–Planck equation

Setting (design decision of `docs/PROOF_QUEUE.md`, "2026-10-16 D3 / MOV design decision").  Fixed drift `-∇U`,
`L = κΔ - ∇U·∇ = d1_gen κ (d1_gradDrift U)`, `G = e^{-U/κ}`, and a time-dependent one-body *tilt* `ψ^t` of the
reference: `q^t = G e^{ψ^t}/Z_t = d1_gibbsMeasure κ (U - κ ψ^t)`.

Core computation (classical positive data, `u = w G/Z`, `ℓ = log w`):
`d/dt [H(u|G) - ∫uψ] = -κ∫u|∇(ℓ-ψ)|² + ∫u (Lψ + κ|∇ψ|² - ∂_tψ)`.
(Derivation: `d/dt H(u|G) = -κ∫u|∇ℓ|²`, `d/dt∫uψ = ∫u(Lψ+∂_tψ)`, and `∫u∇ℓ·∇ψ = -κ⁻¹∫uLψ` by G-self-adjointness.)
Since `H(u|q^t) = H(u|G) - ∫uψ + log Z̃_t`, `Z̃_t = ∫e^{ψ^t}dG̃`, `d/dt log Z̃_t = E_{q^t}∂_tψ`, the moving-reference
form has the extra source `E_{q^t}∂_tψ`.  Normalisation check: `d1_fisherInfo κ U P = ∫|∇log(dP/dG)|²dP` (sup over `ζ` of
`2ζ·v - |ζ|²` is `|v|²`), so the dissipation is `κ · d1_fisherInfo`, as in `d1_fp_entropy`.

Status: every `SPEC (sorried)` statement is a specification only, awaiting independent review.  Proved here:
`d3_tiltPot_zero`, `d3_source_zero`, and `d3_fp_entropy_of_moving` (from `d3_entropy_moving`).
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS
variable {n : ℕ}

/-! ### Definitions -/

/-- The tilted potential: `d1_gibbsMeasure κ (d3_tiltPot κ U ψ) = G e^{ψ}/Z` since `-(U - κψ)/κ = -U/κ + ψ`. -/
def d3_tiltPot (κ : ℝ) (U ψ : Torus n → ℝ) : Torus n → ℝ := fun x => U x - κ * ψ x

/-- The source `Lψ + κ‖∇ψ‖² - ∂_tψ` of the free-energy identity (`ψ : ℝ → Torus n → ℝ` the tilt path, `ψt` its
time derivative), `L = d1_gen κ (d1_gradDrift U)`. -/
def d3_source (κ : ℝ) (U : Torus n → ℝ) (ψ ψt : ℝ → Torus n → ℝ) (r : ℝ) (x : Torus n) : ℝ :=
  d1_gen κ (d1_gradDrift U) (ψ r) x + κ * ‖Torus.grad (ψ r) x‖ ^ 2 - ψt r x

/-- The tilt path `ψ ≡ 0` reproduces the untilted potential. -/
theorem d3_tiltPot_zero (κ : ℝ) (U : Torus n → ℝ) : d3_tiltPot κ U (fun _ => 0) = U := by
  funext x; simp [d3_tiltPot]

/-- The source vanishes for `ψ ≡ 0`. -/
theorem d3_source_zero (κ : ℝ) (U : Torus n → ℝ) (r : ℝ) (x : Torus n) :
    d3_source κ U (fun _ => fun _ => 0) (fun _ => fun _ => 0) r x = 0 := by
  have h : Torus.lift (fun _ : Torus n => (0 : ℝ)) = fun _ => 0 := rfl
  have hb : ∀ y : Euc n, bilinearIteratedFDerivTwo ℝ (fun _ : Euc n => (0 : ℝ)) y = 0 := by
    intro y; ext u v; simp [bilinearIteratedFDerivTwo]
  have hl : (TensorProduct.lift (0 : Euc n →ₗ[ℝ] Euc n →ₗ[ℝ] ℝ)) = 0 := by
    apply TensorProduct.ext'; intro a b; simp
  simp [d3_source, d1_gen, Torus.laplacian, Torus.grad, h, Laplacian.laplacian, gradient,
    tensorIteratedFDerivTwo, hb, hl]

/-- Positive classical `C^{1,2}([0,T])` solutions of the *forward* equation for the density `w = u/G`,
`∂_t w = L w`, `L = d1_gen κ (d1_gradDrift U)` (the Doob transform of `∂_t u = κΔu + div(u∇U)`).  Regularity as
`IsC12Test T w (L w)` plus strict positivity on `[0,T] × 𝕋^n`. -/
structure D3Classical (κ : ℝ) (U : Torus n → ℝ) (T : ℝ) (w : ℝ → Torus n → ℝ) : Prop where
  c12 : IsC12Test T w (fun r x => d1_gen κ (d1_gradDrift U) (w r) x)
  pos : ∀ r ∈ Set.Icc 0 T, ∀ x, 0 < w r x

/-! ### Classical layer (D3-a) -/

/-- **SPEC (sorried).** Existence of a positive classical solution from smooth positive data `w0`.
TeX: no line (M treats this as standard; cf. N:eq:entropy-differential L6455, B.15 Step 2 L12167-12200 where
smoothness/positivity of `u_t/G` is used).  Route: `f(s) := d1_backward_classical` with terminal datum `w0` at `T`,
time-reversed `w r := f (T - r)` (`D1BackwardSolution` -> `D3Classical`); positivity from `d1_backward_nonneg`
(`TorusFPExistAux2`) applied to the *strictly* positive datum plus a strict version: `w r = E w0(X_r) ≥ (min w0)·1`
by the comparison `f - (min w0)` (the constant `min w0` solves the equation, `L 1 = 0`) and `d1_backward_nonneg`.
Size: ~120 lines. -/
theorem d3_classical_exists (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {w0 : Torus n → ℝ} (hw0 : Torus.IsSmooth w0) (hpos : ∀ x, 0 < w0 x) :
    ∃ w : ℝ → Torus n → ℝ, D3Classical κ U T w ∧ w 0 = w0 := by
  sorry

/-- **SPEC (sorried).** `G`-self-adjointness of `L` turns a classical positive solution into a weak solution:
`s ↦ (d1_gibbsMeasure κ U).withDensity (ofReal ∘ w s)` is a `D1WeakSolution`.
TeX: B.15 Step 2 (L12167-12200) uses exactly this identification `u = w G`.  Route: for test `f, ft`,
`d/ds ∫ f_s w_s dP = ∫ (ft + L f_s) w_s dP` using `∫ (f L w - w L f) dP = 0` (`d1c_ibp`, `TorusFPCompareAux1`,
NOT sufficient alone: `d1c_ibp` for `φ = f w` only gives the symmetric part `∫(fLw + wLf)G = -2κ∫∇f·∇w G`;
one needs the weighted Green identity `∫ f (Lw) G = -κ∫∇f·∇w G`, i.e. the torus divergence theorem `∫ div V = 0`
for the `C¹` field `V = f G ∇w`, the lemma underlying `d1c_ibp` in `TorusFPCompareAux1`), differentiation under the integral (compact torus, continuity from
`IsC12Test`), narrow continuity from joint continuity.  Size: ~250 lines. -/
theorem d3_classical_isWeak (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w) :
    D1WeakSolution κ (d1_gradDrift U) T
      (fun s => (d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w s x)) := by
  sorry

/-- **SPEC (sorried).** For a smooth positive density `w` w.r.t. `d1_gibbsMeasure κ U` and a `C²` tilt `ψ`, the
relative Fisher information w.r.t. the tilted reference is `∫ ‖∇(log w - ψ)‖² dμ`, `μ = P.withDensity w`.
TeX: B:eq:selected-fisher-variational (L12205-12209).  Hypotheses are `C²` only (classical solutions are only
`C([0,T];C²)`, no smoothing theorem is available).  Route: `≥` by testing `ζ = ∇(log w - ψ)`, which is only `C¹`,
so the sup over smooth fields needs a `C¹`-approximation of `ζ` (the integrand contains `div ζ`, `C⁰` does not suffice), `≤` by IBP + Cauchy–Schwarz (pointwise `2ζ·v - |ζ|² ≤ |v|²`).
Size: ~150 lines. -/
theorem d3_fisher_classical {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {w ψ : Torus n → ℝ} (hw : Torus.IsCk 2 w) (hwpos : ∀ x, 0 < w x) (hψ : Torus.IsCk 2 ψ) :
    d1_fisherInfo κ (d3_tiltPot κ U ψ)
        ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x))
      = ENNReal.ofReal (∫ x, ‖Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x‖ ^ 2
          ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x))) := by
  sorry

/-- **SPEC (sorried): exact free-energy identity, classical positive data.**  With `P = d1_gibbsMeasure κ U`,
`μ_s = P.withDensity (w s)` (a probability measure, `∫ w 0 dP = 1`) and a tilt `ψ ∈ IsC12Test T ψ ψt`:
`H(μ_t|P) - ∫ψ_t dμ_t + κ ∫_0^t ∫‖∇(log w_r - ψ_r)‖² dμ_r dr
   = H(μ_0|P) - ∫ψ_0 dμ_0 + ∫_0^t ∫ (Lψ_r + κ‖∇ψ_r‖² - ∂_rψ_r) dμ_r dr`.
TeX: N:eq:entropy-differential L6455 (differential form, `ψ`-version), B.15 Step 2 L12167-12200 (`ψ = 0`).
Route: (i) `r ↦ ∫ w log w dP` and `r ↦ ∫ψ_r w_r dP` are C¹ on `(0,T)` and continuous on `[0,T]` (differentiate under
the integral, compact torus, `D3Classical.c12`); (ii) derivatives by IBP (`d1c_ibp` for `L(w log w)`, `L(ψw)`) and the
algebra displayed in the file header; (iii) fundamental theorem of calculus on `[ε,t]`, `ε → 0`.
`relEntropy.toReal = ∫ w log w dP` for probability `μ` (`InformationTheory.klDiv` for `μ ≪ P`).  Size: ~450 lines. -/
theorem d3_tilted_identity_classical (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w)
    (hmass : ∫ x, w 0 x ∂(d1_gibbsMeasure κ U) = 1) {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) :
    ∀ t ∈ Set.Icc 0 T,
      (relEntropy ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w t x))
          (d1_gibbsMeasure κ U)).toReal
        - ∫ x, ψ t x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w t x))
        + κ * ∫ r in Set.Icc 0 t, ∫ x, ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2
            ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x))
      = (relEntropy ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x))
          (d1_gibbsMeasure κ U)).toReal
        - ∫ x, ψ 0 x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x))
        + ∫ r in Set.Icc 0 t, ∫ x, d3_source κ U ψ ψt r x
            ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) := by
  sorry

/-! ### Measure layer (D3-b) -/

/-- **SPEC (sorried): measure-valued free-energy inequality** (reference `G`, tilt as a bounded perturbation).
For any `D1WeakSolution μ` with probability initial datum of finite relative entropy w.r.t. `G`, and `ψ` with
`IsC12Test T ψ ψt`: for all `t ∈ [0,T]` the entropy `H(μ_t|G)` and `∫_0^t 𝓘_{q^r}(μ_r)dr` are finite and
`(H(μ_t|G) - ∫ψ_t dμ_t) + κ ∫_0^t 𝓘_{q^r}(μ_r)dr ≤ (H(μ_0|G) - ∫ψ_0 dμ_0) + ∫_0^t ∫ source dμ_r dr`,
`𝓘_{q^r} = d1_fisherInfo κ (d3_tiltPot κ U (ψ r))`.
The finiteness conjuncts make the `.toReal`s meaningful (`⊤.toReal = 0`).  The source integrand is jointly
continuous on `[0,T] × 𝕋^n` (`IsC12Test`), hence bounded, and `r ↦ ∫ source dμ_r` is continuous (narrow continuity
of the family `μ_r` is uniform on compact sets of test functions), so all real integrals are non-junk; `r ↦ d1_fisherInfo … (μ r)` is a sup of narrowly continuous functionals,
hence lsc, hence measurable, so the `∫⁻` is meaningful.
TeX: N:eq:entropy-differential L6455; B.15 Step 2 L12167-12200; MOV (ISSUES) item 4 (integrated form).
Route: smooth positive approximants `w0^k → μ_0` (entropy-recovering, `H(μ_0^k|G) → H(μ_0|G)`), `d3_classical_exists`
+ `d3_classical_isWeak` + `d3_tilted_identity_classical` + `d3_fisher_classical` for each `k`, duality stability
(`d1_fp_unique`/`d1_fp_comparison`: `μ^k_t → μ_t` narrowly), lower semicontinuity of `H(·|G)` and `𝓘`
(`d1_fisherInfo` is a sup of narrowly continuous functionals), Fatou in `r`.  Size: ~800 lines (the bulk of D3-b). -/
theorem d3_tilted_inequality (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ U) ≠ ⊤)
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ U) ≠ ⊤ ∧
      ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r) < ⊤ ∧
      ((relEntropy (μ t) (d1_gibbsMeasure κ U)).toReal - ∫ x, ψ t x ∂(μ t))
        + κ * (∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r)).toReal
      ≤ ((relEntropy (μ 0) (d1_gibbsMeasure κ U)).toReal - ∫ x, ψ 0 x ∂(μ 0))
        + ∫ r in Set.Icc 0 t, ∫ x, d3_source κ U ψ ψt r x ∂(μ r) := by
  sorry

/-- **SPEC (sorried): entropy relative to the moving reference** `q^r = d1_gibbsMeasure κ (U - κ ψ^r)`.
`H(μ_t|q^t) + κ∫_0^t𝓘_{q^r}(μ_r)dr ≤ H(μ_0|q^0) + ∫_0^t ∫ (source_r + E_{q^r}∂_rψ_r) dμ_r dr`;
(`μ_r` is a probability measure for all `r ∈ [0,T]` by `d1_isProbabilityMeasure`, so integrating the `x`-constant
`E_{q^r}∂_rψ_r` against `μ_r` is just that constant; MOV consumes this form.)  The extra `E_{q^r}∂_rψ_r` (constant in `x`) is `d/dr log Z̃_r`, `Z̃_r = ∫ e^{ψ^r} dP`, where
`H(μ|q^r) = H(μ|G) - ∫ψ^r dμ + log Z̃_r`.
TeX: N:eq:entropy-differential L6455 (moving reference); the extra term is the one the MOV items 3/5 need
(ISSUES MOV).  Route: `d3_tilted_inequality` + `log Z̃_t - log Z̃_0 = ∫_0^t E_{q^r}ψt dr`
(differentiate `log ∫ e^{ψ^r}dP`; `ψ ∈ IsC12Test`, bounded).  The conclusions include finiteness; the hypothesis is
finiteness of `H(μ_0|q^0)` (equivalent to that of `H(μ_0|G)` since `ψ^0` is bounded).  Size: ~200 lines
given `d3_tilted_inequality`. -/
theorem d3_entropy_moving (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt)
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ 0))) ≠ ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ t))) ≠ ⊤ ∧
      ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r) < ⊤ ∧
      (relEntropy (μ t) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ t)))).toReal
        + κ * (∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r)).toReal
      ≤ (relEntropy (μ 0) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ 0)))).toReal
        + ∫ r in Set.Icc 0 t, ∫ x, (d3_source κ U ψ ψt r x
            + ∫ y, ψt r y ∂(d1_gibbsMeasure κ (d3_tiltPot κ U (ψ r)))) ∂(μ r) := by
  sorry

/-! ### The corollary `d1_fp_entropy` -/

/-- `d1_fp_entropy` (the `ψ = 0` case of `d3_entropy_moving`), proved from it.  The two forms agree: with
`ψ ≡ 0`, `q^r = d1_gibbsMeasure κ U` and the source vanishes. -/
theorem d3_fp_entropy_of_moving (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ U) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ U) +
        ENNReal.ofReal κ * ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ U (μ r)
      ≤ relEntropy (μ 0) (d1_gibbsMeasure κ U) := by
  intro t ht
  have hC : IsC12Test T (fun _ : ℝ => fun _ : Torus n => (0 : ℝ)) (fun _ _ => 0) :=
    d1_isC12Test_const ((show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Torus.lift (fun _ : Torus n => (0 : ℝ))) from d1_isSmooth_const 0).of_le (by norm_num))
  have hf0 : relEntropy (μ 0) (d1_gibbsMeasure κ (d3_tiltPot κ U (fun _ : Torus n => (0 : ℝ)))) ≠ ⊤ := by
    rw [d3_tiltPot_zero]; exact hfin.ne
  obtain ⟨h1, h2, h3⟩ := d3_entropy_moving hn hκ hU hT hμ hC hf0 t ht
  simp only [d3_tiltPot_zero, d3_source_zero, integral_zero, add_zero] at h1 h2 h3
  have hA : relEntropy (μ 0) (d1_gibbsMeasure κ U) ≠ ⊤ := hfin.ne
  have hlhs : relEntropy (μ t) (d1_gibbsMeasure κ U) +
      ENNReal.ofReal κ * ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ U (μ r) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨h1, ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2.ne⟩
  rw [← ENNReal.toReal_le_toReal hlhs hA, ENNReal.toReal_add h1 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ.le]
  simpa using h3

end HRS
