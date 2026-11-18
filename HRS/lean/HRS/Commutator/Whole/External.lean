import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Local
import HRS.Commutator.Whole.YoungAux
import HRS.Commutator.Whole.RieszAux
import HRS.Commutator.Whole.ExternalAuxMult3
import HRS.Commutator.Whole.ExternalAuxMult4
import HRS.Commutator.Whole.ExternalAuxHLS5
import HRS.Commutator.Whole.ExternalAuxHLS12
import HRS.Commutator.Whole.XLIAux44
import HRS.Commutator.Whole.XNRSAux37
import HRS.Commutator.Whole.XBBAux14

/-!
# Sub-Coulomb commutator on `ℝ^d`: external dependencies of the note (to be formalized, not assumed)

The note `[N]` rests on the following results of the literature.  Each is stated here in the exact
form used (a `sorry`'d theorem, packet `CMX-EXT-*` in `docs/external/subcoulomb-plan.md`), with the
reference:

* `nrs_commutator` (`[N] (4.knowncomm)` L515-520): Nguyen–Rosenzweig–Serfaty, arXiv 2107.02592
  (Ars Inveniendi Analytica 2022), Prop. 3.1; also Hess-Childs–Rosenzweig–Serfaty, arXiv 2601.02326,
  Prop. 1.2.  Split into the generic case and the exceptional integer case `s = d - 2k`, `k ≥ 2`
  (the latter needs the Christ–Journé theorem in NRS's proof, `[NRS22] L1330-1336`, or the polyharmonic
  stress-tensor alternative of the plan).
* `li_leibniz` (`[N] (3.leibniz)` L501-507): Dong Li, *On Kato–Ponce and fractional Leibniz*,
  Rev. Mat. Iberoam. 35 (2019), arXiv 1609.01780, (1.15) (the inhomogeneous `J^s` variant: "One should
  note that the same inequality also holds for the inhomogeneous operator `J^s`", Li L469).
* `sobolev_embedding_frac` (`[N] (1.regularity-embedding)` L128-134) and `hls_sobolev`:
  homogeneous Sobolev embedding (Stein, *Singular integrals*, Ch. V §1, Thm 1 and §2.3 Thm 2),
  Hardy–Littlewood–Sobolev.
* `riesz_potential_fourier`: Stein Ch. V Lemma 1 (Fourier transform of `|x|^{-α}`), used for the kernel
  bounds `(3.K-bounds)` L466-468 and Lemma 3.1 (L418-423).
* `mult_kernel_*`: the Fourier multiplier facts (Stein Ch. IV) in the explicit form needed
  (kernel bounds instead of the Mikhlin theorem, `[N] (3.high-multipliers)` L455-460).
* `bernstein_Lq`: `‖a_0‖_{L^{p₂}} ≲ ‖a_0‖_{L²}` for Fourier-localised `a_0` (`[N] L583-584`).
* Plancherel, the Fourier transform on `L¹, L²`, Hölder: Mathlib (`Real.fourierIntegral`,
  `Lp.fourierTransformₗᵢ`, `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm`); Young's inequality
  for convolutions and the Hardy–Littlewood maximal theorem are *absent* from the pinned Mathlib.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-! ### The unrenormalized commutator estimate of Nguyen–Rosenzweig–Serfaty -/

/-- `[N] (4.knowncomm)` (L515-520) in the generic case: `s` is not of the form `d - 2k`, `k ≥ 2`.
NRS22 Prop. 3.1 proof route (L1033-1450 of the arXiv text): super-Coulombic `d-2 < s < d` via the
integration by parts `(3.5)-(3.27)` and the Gagliardo seminorm equivalence `[DNPV12]`;
sub-Coulombic `0 ≤ s < d-2` by induction on `k` with `d-2(k+1) ≤ s < d-2k` through `(3.37)-(3.46)`:
Hardy–Littlewood–Sobolev, `L^p` boundedness of Riesz transforms and the fractional Leibniz rule
`[Gra14b, Thm 7.6.1]` (= `li_leibniz`). -/
theorem nrs_generic (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (hgen : ¬ ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ a : Euc d → ℝ, IsRealSchwartz a → (s = 0 → ∫ x, a x = 0) →
        ENNReal.ofReal |CcommFun (kernGrad s) v a| ≤
          ENNReal.ofReal (C * K) * homSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a) := by
  obtain ⟨CB, hCB⟩ := HRS.Commutator.Whole.XBB.xbb_exists hd hs0 hsd
  exact HRS.Commutator.Whole.XNRS.xnrs_conditional hd hs0 hsd hCB

/-- `[N] (4.knowncomm)` in the exceptional integer case `s = d - 2k`, `k ≥ 2` (`d ≥ 4`; `s ≥ 0`).
NRS22 assume in this case that the kernel `(x-y) ⊗ ∇^{⊗(1+2k)}g(x-y)` is a Calderón–Zygmund kernel
(`(3.3)`, true for `g = |x|^{-s}`), and the Coulombic-type term `(3.32)-(3.36)` is a Calderón
commutator handled by the Christ–Journé theorem `[CJ87]`.  Plan: either formalize Calderón–Zygmund
theory + Christ–Journé, or the polyharmonic stress-tensor route (for `s = d-2k`,
`g` is the fundamental solution of `(-Δ)^k`, `α = k`, `p₁ = d/(k-1)`: local Leibniz + Gagliardo–Nirenberg),
see the plan, packet `CMX-NRS-X`. -/
theorem nrs_exceptional (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (hexc : ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ a : Euc d → ℝ, IsRealSchwartz a → (s = 0 → ∫ x, a x = 0) →
        ENNReal.ofReal |CcommFun (kernGrad s) v a| ≤
          ENNReal.ofReal (C * K) * homSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a) := by
  obtain ⟨CB, hCB⟩ := HRS.Commutator.Whole.XBB.xbb_exists hd hs0 hsd
  exact HRS.Commutator.Whole.XNRS.xnrs_conditional hd hs0 hsd hCB

/-- `[N] (4.knowncomm)` (L515-520): the unrenormalized commutator estimate
`|𝒞_g(v,a)| ≲ C(v) ‖a‖²_{Ḣ^{-α}}` for real Schwartz `a` (mass zero when `s = 0`), `v` Lipschitz with
`C(v) ≤ K` (no compact support of `v`).  NRS22 Prop. 3.1 is the bilinear form `(f,g)`; the note uses
`f = g = a`.  Proved from the two cases above. -/
theorem nrs_commutator (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ a : Euc d → ℝ, IsRealSchwartz a → (s = 0 → ∫ x, a x = 0) →
        ENNReal.ofReal |CcommFun (kernGrad s) v a| ≤
          ENNReal.ofReal (C * K) * homSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a) := by
  by_cases h : ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k
  · exact nrs_exceptional hd hs0 hsd h
  · exact nrs_generic hd hs0 hsd h

/-! ### Fractional Leibniz (Li) -/

/-- `⟨∇⟩^α φ = 𝓕⁻[(1+4π²|ξ|²)^{α/2} φ̂]` on Schwartz functions. -/
def besselS (α : ℝ) (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) : ℂ :=
  𝓕⁻ (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x

/-- `|∇|^σ φ = 𝓕⁻[(2π|ξ|)^σ φ̂]` on Schwartz functions (the repository's convention in
`IsFracDerivRep`). -/
def fracS (σ : ℝ) (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) : ℂ :=
  𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x

/-- Fractional Leibniz rule `[N] (3.leibniz)` (L501-507), Li (1.15) with `J^s` in place of `D^s`:
for `s > 0`, `1 < r < ∞`, `1 < p_i, q_i ≤ ∞`, `1/r = 1/p₁ + 1/q₁ = 1/p₂ + 1/q₂`, and Schwartz `f, g`,
`‖J^s(fg)‖_{L^r} ≲ ‖J^s f‖_{L^{p₁}}‖g‖_{L^{q₁}} + ‖J^s g‖_{L^{p₂}}‖f‖_{L^{q₂}}`.
The note uses `s = α`, `r = 2`, `(p₁,q₁) = (p₁,p₂)`, `(p₂,q₂)` swapped (`[N] L506-507`).  The
constant depends only on `s, d` and the exponents.  Extension from Schwartz to the classes used in
`(3.product)` is by density (part of `Local.product_estimate`). -/
theorem li_leibniz (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) (r p₁ q₁ p₂ q₂ : ℝ≥0∞)
    (hr : 1 < r) (hr' : r < ⊤) (hp₁ : 1 < p₁) (hq₁ : 1 < q₁) (hp₂ : 1 < p₂) (hq₂ : 1 < q₂)
    (h1 : p₁⁻¹ + q₁⁻¹ = r⁻¹) (h2 : p₂⁻¹ + q₂⁻¹ = r⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g h : SchwartzMap (Euc d) ℂ, (∀ x, h x = f x * g x) →
      eLpNorm (besselS α h) r volume ≤
        ENNReal.ofReal C *
          (eLpNorm (besselS α f) p₁ volume * eLpNorm (⇑g) q₁ volume +
            eLpNorm (besselS α g) p₂ volume * eLpNorm (⇑f) q₂ volume) := by
  obtain ⟨C, hC, hmain⟩ := XLI.main_uncond α hd hα hr hr' hp₁ hq₁ hp₂ hq₂ h1 h2
  have hb : ∀ φ : SchwartzMap (Euc d) ℂ, besselS α φ = ⇑(XLI.Fm α φ) := fun φ => by
    funext x
    exact (XLI.mulS_apply _ _ φ x).symm
  refine ⟨C.toReal + 1, by positivity, fun f g h hh => ?_⟩
  have hhp : h = XLI.prodS f g := SchwartzMap.ext fun x => by rw [XLI.prodS_apply, hh x]
  rw [hhp, hb, hb f, hb g]
  refine (hmain f g).trans ?_
  gcongr
  calc C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC).symm
    _ ≤ ENNReal.ofReal (C.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Homogeneous Sobolev embedding, Riesz potentials, multipliers -/

/-- Homogeneous Sobolev inequality / Hardy–Littlewood–Sobolev (Stein V §1 Thm 1, §2.3):
for `1 < p < q < ∞`, `0 < σ < d/p`, `1/q = 1/p - σ/d` and Schwartz `φ`,
`‖φ‖_{L^q} ≲ ‖|∇|^σ φ‖_{L^p}`.  Used in `(3.potential-proof)` (L489-493: `p = 2`,
`σ = α-1`, `q = p₂`) and in `sobolev_embedding_frac`. -/
theorem hls_sobolev (hd : 1 ≤ d) (σ : ℝ) (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq : q < ⊤)
    (hσ : 0 < σ) (hrel : q⁻¹ = p⁻¹ - ENNReal.ofReal (σ / d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap (Euc d) ℂ,
      eLpNorm (⇑φ) q volume ≤ ENNReal.ofReal C * eLpNorm (fracS σ φ) p volume := by
  obtain ⟨C, hC, h⟩ := cmxHLS_main hd σ p q hp hpq hq hσ hrel
  exact ⟨C, hC, fun φ => h φ⟩

/-- `[N] (1.regularity-embedding)` (L128-134): for `a ∈ (d, d+2)`,
`‖|∇|^{(d-s)/2} v‖_{L^{2d/(d-s-2)}} ≲_{d,s,a} ‖|∇|^{a/2} v‖_{L^{2d/(a-2)}}` (Stein V; `|∇|^{(d-s)/2} =
|∇|^{-σ}|∇|^{a/2}`, `σ = (a-d+s)/2`, `1/q = 1/p - σ/d`, `σ < d/p ⇔ s < d-2`, HLS).  Stated at the level
of the transport bound `HasFracTransportBound` (Lipschitz `v`, distributional `|∇|^α v`, i.e.
"modulo polynomials" is handled by `α > 1` and the Lipschitz bound: `∫ v |∇|^α φ` converges because
`| |∇|^α φ(x)| ≲ |x|^{-d-α}`, and the low-frequency part of the test function contributes
`O(ε^{α-1})`). -/
theorem sobolev_embedding_frac (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ),
      HasFracTransportBound (a / 2) (2 * d / (a - 2)) v K → SubTransport d s v (C * K) := by
  obtain ⟨C, hC, h⟩ := cmxHLS_embedding hd hs0 hsd a ha
  exact ⟨C, hC, fun v K hv => h v K hv⟩

/-- Stein V Lemma 1(a): for `0 < γ < d` and Schwartz `φ`,
`π^{-γ/2} Γ(γ/2) ∫ |x|^{-γ} φ̂(x) dx = π^{-(d-γ)/2} Γ((d-γ)/2) ∫ |ξ|^{γ-d} φ(ξ) dξ`
(the Fourier transform of `|x|^{-γ}` is `c |ξ|^{γ-d}`), with Mathlib's convention `e^{-2πi x·ξ}`;
proved from the Gaussian subordination `|x|^{-γ} = c ∫ t^{γ/2-1} e^{-t|x|²} dt` and
`Real.fourierIntegral_gaussian`. -/
theorem riesz_potential_fourier (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (hγd : γ < d)
    (φ : SchwartzMap (Euc d) ℂ) :
    (Real.pi ^ (-γ / 2) * Real.Gamma (γ / 2) : ℝ) *
        ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 (⇑φ) x =
      (Real.pi ^ (-((d : ℝ) - γ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2) : ℝ) *
        ∫ ξ : Euc d, ((‖ξ‖ ^ (γ - d) : ℝ) : ℂ) * φ ξ :=
  riesz_potential_aux hd γ hγ hγd φ

/-- `(3.K-bounds)` (`[N] L466-468`) and Lemma 3.1's kernel argument (L418-423): for `0 < γ < d` the symbol
`(1-χ(ξ))|2πξ|^{-γ}` (smooth, not integrable) is the Fourier transform of an integrable real kernel `K_γ`
(`𝓕K_γ = symbol`; stated with `K ∈ L¹` so that no junk `𝓕⁻` of a non-integrable symbol enters) with
`|K_γ(x)| ≲ |x|^{γ-d}` for `0 < |x| ≤ 1` and `|K_γ(x)| ≤ C_m |x|^{-m}` for `|x| ≥ 1`, every `m`
(Riesz potential minus a smooth part, `riesz_potential_fourier`; Fourier differentiation `x^m K`).
This `K_γ` is the kernel in `v_{>1} = K_α * |∇|^α v` (`vhi_Lp`, `vhi_cube_sampling`). -/
theorem mult_kernel_bounds (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (hγd : γ < d) :
    ∃ K : Euc d → ℝ, Integrable K ∧
      (∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
        (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-γ) : ℝ) : ℂ)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |K x| ≤ C * ‖x‖ ^ (γ - d)) ∧
      (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : Euc d, 1 ≤ ‖x‖ → |K x| ≤ C * ‖x‖ ^ (-(m : ℝ))) :=
  cmxMY_mult_kernel_bounds hd γ hγ hγd

/-- `(3.high-multipliers)` second symbol `(1+4π²|ξ|²)^{α/2}(1-χ)|2πξ|^{-α}` (`[N] L456-458`):
its kernel is `δ - ψ + (L¹ function)` (the symbol minus `1 - χ` has order `-2`); stated as: there is
an integrable `k` such that the symbol equals `1 - χ + k̂`. -/
theorem mult_kernel_bessel (hd : 3 ≤ d) (α : ℝ) (hα : 0 < α) (hαd : α < d) :
    ∃ k : Euc d → ℝ, Integrable k ∧ ∀ ξ : Euc d,
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) * ((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α)) : ℝ) : ℂ) =
        (((1 - chi ξ : ℝ)) : ℂ) + 𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ :=
  cmxMY_mult_kernel_bessel hd α hα hαd

/-- Bernstein/Young (`[N] L583-584`): for `1 ≤ p ≤ q ≤ ∞`, a function `a ∈ L^p` with Fourier support
in `B̄(0,R)` is in `L^q` with `‖a‖_{L^q} ≲_{d,R,p,q} ‖a‖_{L^p}` (`a = Ω * a` for a Schwartz `Ω` with
`Ω̂ = 1` on `B̄(0,R)`, then Young). -/
theorem bernstein_Lq (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R) (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Euc d → ℝ, MemLp a p volume → FourierSuppIn R a →
      MemLp a q volume ∧ eLpNorm a q volume ≤ ENNReal.ofReal C * eLpNorm a p volume := by
  have : p.HolderConjugate (ENNReal.conjExponent p) := ENNReal.HolderConjugate.conjExponent hp
  obtain ⟨K, hK⟩ := exists_kernel_fourier_one (d := d) (R + 1) (by linarith)
  refine ⟨(eLpNorm K (ENNReal.conjExponent p) volume).toReal + 1, by positivity, fun a ha hsupp => ?_⟩
  have hcore := bernstein_core (p' := ENNReal.conjExponent p) hp hpq K hK a ha hsupp
  have hlt : eLpNorm a q volume < ⊤ :=
    lt_of_le_of_lt hcore (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ha.eLpNorm_lt_top)
  exact ⟨hlt, hcore⟩

end HRS.Commutator.Whole
