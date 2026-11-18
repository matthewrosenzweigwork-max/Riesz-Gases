import HRS.Energy.Commutator.EnergyH

/-!
# Route H, packet H4: Kato-Ponce commutator estimate for the Bessel kernels (the hard block)

Source: `[HCRS] §3` (Prop. 3.1, Cor. 3.2, Lemmas 3.5-3.7), `a = d+1`; `[Li19] Thm 1.9`
(Kato-Ponce commutator with `L^p` norms); `[Gra14]` for the Mikhlin multiplier theorem.

**What is proved (statement `bessel_commutator_scale`).**  For every scale `t > 0`, smooth `h`,
`f = ⟨t∇⟩^{d+1} h`, a Lipschitz field `v` with `‖∇v‖_∞ ≤ L` and `‖|∇|^{(d+1)/2} v‖_{L^{2d/(d-1)}} ≤ F`:
`|∫ f v·∇h| ≤ C (L + F) ∫ h f`, with `C` independent of `t`.  Since
`∬ (v(x)-v(y))·∇φ_t(x-y) f f = 2 ∫ f v·∇(φ_t*f)`, this is the per-scale commutator estimate
`[HCRS (3.8)-(3.12)]` after the change of variables `t`; both `L` and `F` scale like `t¹`
(`‖|∇|^{a/2}v_t‖_{L^{2d/(a-2)}} = t ‖|∇|^{a/2}v‖_{L^{2d/(a-2)}}`), which is why the *single*
critical exponent `a = d+1` is used and `a < d+2` is automatic.

**Route (HCRS).**  (i) `α = a = 2m + r`, `m = ⌈(d+1)/2⌉-1`, `r ∈ {1,2}` (`r = 2` for `d` odd: then
`⟨∇⟩^α = (1-Δ)^{(d+1)/2}` is a **local** operator and the whole argument is Leibniz + Hölder +
Sobolev on the torus; `r = 1` for `d` even: one nonlocal factor `⟨∇⟩`).
(ii) Induction on `m`: base case `m = 0` (`α = r ≤ 2`): the stress-tensor identity for the extension
`F = e^{-z⟨∇⟩}h` (`r = 1`, no weight, `[HCRS Lemma 3.6]` with `s = 1`) resp. the classical identity
for `1-Δ` (`r = 2`); this is the same computation as `Stress.lean` (S3.1) with `l = 1` and
Lipschitz-only.  Step `m → m+1`: `⟨∇⟩^{α+2} = (1-Δ)⟨∇⟩^α`, integrate by parts and use the fractional
Leibniz rule `Lemma 3.5`: `‖⟨∇⟩^{r/2} ∂_β(fg)‖_{L²} ≲ ‖g‖_{H^{|β|+r/2}} Ã_{f,|β|,r}` (Li's commutator
`‖⟨∇⟩^{r/2}(fg) - f⟨∇⟩^{r/2}g‖_{L²} ≲ ‖⟨∇⟩^{r/2-1}∇f‖_{L^{p_1}}‖g‖_{L^{p_2}}`, `1/p_1+1/p_2 = 1/2`,
only needed for `d` even).  (iii) All `L^p` norms of derivatives of `v` are reduced to the single
top-order one `‖|∇|^{(d+1)/2} v‖_{L^{2d/(d-1)}}` by Sobolev embedding and Gagliardo-Nirenberg
interpolation (`[HCRS (3.26)-(3.31)]`).

**Torus differences / missing Mathlib.**  (1) *No Mathlib support*: Sobolev embedding
`Ḣ^σ(T^d) ⊂ L^{2d/(d-2σ)}` (`sobolev_critical_torus`, sharp, mean-zero `h`), Gagliardo-Nirenberg
interpolation for `|∇|^j`, Mikhlin multiplier bounds on `L^p(T^d)`; there is no Hardy-Littlewood
maximal function in the pinned Mathlib (checked), so the critical embedding must be proved by hand
(integer order: Mathlib's Gagliardo-Nirenberg-Sobolev `eLpNorm_le_eLpNorm_fderiv_of_eq` plus a
cut-off/periodisation; half-integer order for `d` even: via the Poisson extension of `[HCRS Lemma
3.6]`, which turns `⟨∇⟩^{1/2}` into a *local* trace problem).  (2) *Uniformity in `t`*: on `ℝ^d` the
scale `t` is removed by dilation; on `T^d` the dilated torus has period `1/t`.  For `t ≤ 1` the
period is `≥ 1` and the inhomogeneous Sobolev/GN constants are uniform; for `t ≥ 1` the symbol
`⟨2πtk⟩^{-a}` is comparable to `t^{-a}(2π|k|)^{-a}` on `k ≠ 0` and the estimate is that of the
homogeneous operator on mean-zero functions (the same proof, with the mass `t^{-1} ≤ 1`
as a parameter of `(μ² - Δ)^{a/2}`): the statement below asserts uniformity for **all** `t > 0`;
this is the part of the torus adaptation that is not in the literature (HCRS Rem. 1.3) and the
main risk of the route.  (3) The test functions are smooth `h`; the extension to `h = φ_t*(μ_N-μ)`
(Dirac masses) is `gEta_commutator` below (Fejér/mollifier approximation, `g_η` bounded).

`d ≥ 3` (the regime `s < d-2` is empty for `d ≤ 2`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- The Bessel-type multiplier `⟨t∇⟩^β` on smooth functions: `ĥ(k) ↦ (1 + 4π²t²|k|²)^{β/2} ĥ(k)`
(absolutely summable against the rapidly decaying `ĥ`). -/
def besselOpPow (d : ℕ) (t β : ℝ) (h : Torus d → ℝ) (x : Torus d) : ℝ :=
  (∑' k : Lattice d, (((1 + 4 * Real.pi ^ 2 * t ^ 2 * Lattice.enorm k ^ 2) ^ (β / 2) : ℝ) : ℂ) *
    KernelGrad.coeffOf h k * Torus.mode k x).re

/-- The Bessel operator `⟨t∇⟩^{d+1}` (the inverse of the torus symbol `besselSym`). -/
def besselOp (d : ℕ) (t : ℝ) (h : Torus d → ℝ) (x : Torus d) : ℝ := besselOpPow d t (besselA d) h x

/-- **KP-1 (critical Sobolev embedding on the torus, mean-zero functions).**  Sharp exponent:
`‖h‖_{L^{2d/(d-2σ)}} ≤ C ‖h‖_{Ḣ^σ}`, `0 < σ < d/2`.  Used with `σ = (d-1)/2`, `q = 2d`. -/
theorem sobolev_critical_torus (hd : 1 ≤ d) {σ : ℝ} (hσ0 : 0 < σ) (hσd : σ < (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Torus d → ℝ, Torus.IsSmooth h → ∫ x, h x = 0 →
      eLpNorm h (ENNReal.ofReal (2 * d / ((d : ℝ) - 2 * σ))) volume ≤
        ENNReal.ofReal (C * homSobolev σ h) := by
  sorry

/-- **KP-0 (base cases of the induction, `[HCRS (3.58)]`).**  `r = 2` is `stress_regular` with
`l = t^{-2}` (`⟨t∇⟩² = 1 - t²Δ`); `r = 1` is the stress-energy identity for the *non-degenerate*
Poisson extension `F(x,z) = e^{-z⟨t∇⟩} h` on `T^d × (0,∞)` (`(Δ_x - t^{-2})F + F_zz = 0`,
`∫ v·∇h ⟨∇⟩h = -∫_{z=0} v·∇F ∂_z F = ∫_{z>0} ∇v : [∇F,∇F] + boundary terms`), Lipschitz only. -/
theorem kp_base_half (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
      ∀ h : Torus d → ℝ, Torus.IsSmooth h →
        |∫ x, besselOpPow d t 1 h x * inner ℝ (v x) (Torus.grad h x)| ≤
          C * L * ∫ x, h x * besselOpPow d t 1 h x := by
  sorry

/-- **KP-2 (per-scale Kato-Ponce commutator estimate, `[HCRS Prop. 3.1]` for `a = d+1`, torus).**
`C = C(d)`, uniform in `t > 0`. -/
theorem bessel_commutator_scale (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ (L F : ℝ) (v : Torus d → Euc d), 0 ≤ L → 0 ≤ F →
      IsLipschitzVF L v → HasFracBound d v F → ∀ h : Torus d → ℝ, Torus.IsSmooth h →
        |∫ x, besselOp d t h x * inner ℝ (v x) (Torus.grad h x)| ≤
          C * (L + F) * ∫ x, h x * besselOp d t h x := by
  sorry

/-- **KP-3 (integrated, rough charges; `[HCRS Cor. 3.2]` + Remark 3.4).**  The commutator quantity
of the *truncated* kernel against `μ_N - μ` (Dirac masses!) is bounded by the truncated energy:
`|Comm_N[g_η]| ≤ C (L+F) E_η`.  Proof: per-scale estimate (KP-2) for the trigonometric polynomials
`h_t = φ_t * (Fejér-mollified μ_N - μ)`, Fubini in `t` against `c t^{d-s-1} dt` (all kernels are
bounded and `∇g_η` has only a logarithmic singularity, `|x||∇g_η| ≲ 1`), then removal of the
mollification by dominated convergence; the diagonal can be reinserted because
`k(x,x) = 0`. -/
theorem gEta_commutator (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 → ∀ (L F : ℝ) (v : Torus d → Euc d), 0 ≤ L → 0 ≤ F →
      IsLipschitzVF L v → HasFracBound d v F → ∀ (ρ : Torus d → ℝ) (Λ : ℝ), IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ (N : ℕ), 2 ≤ N → ∀ X : Config d N,
        |commQuantityWith (fun z => Torus.grad (gEta d s η) z) v X (withDensityReal ρ)| ≤
          C * (L + F) * etaEnergy d s η X (withDensityReal ρ) := by
  sorry

end HRS.Commutator
