import HRS.Commutator.Torus.Defs
import HRS.Commutator.Torus.Layer
import HRS.Commutator.Torus.TEXTAux19
import HRS.Commutator.Torus.LEIBTAux27
import HRS.Commutator.Torus.NRSTAux49

/-!
# Torus sub-Coulomb commutator: external dependencies (torus versions)

Torus analogues of `HRS/Commutator/Whole/External.lean`; transference decisions (plan §7.3):

* `nrs_T` (NRS Prop 3.1 on `𝕋^d`): **proved directly on the torus** (the proof of NRS is local + Fourier: integration by
  parts with a cutoff `|x-y|≥ε`, Taylor, Gagliardo seminorm, Leibniz, HLS; for the torus kernel `g_T = |x|^{-s}+smooth` the
  hypotheses (3.1)-(3.3) hold).  *Transference from `ℝ^d` does not work*: periodic `v` has `|∇|^α v ∉ L^{p₁}(ℝ^d)`, and
  localising `v` multiplies the fractional norm by `L^{d/p₁}`.  Scale invariance reduces the family `𝕋_R` to the single period-1 torus.
* `hls_T` (HLS/Sobolev on `𝕋^d` for mean-free functions): **by transference from `ℝ^d`**: the periodic Riesz potential kernel is
  dominated by `C(|x|_𝕋^{σ-d}+1)`; apply the `ℝ^d` Hardy–Littlewood–Sobolev inequality in *kernel form* (`|x|^{σ-d} * |f|`) to
  `f 1_{[-1,1)^d}`; the constant is scale invariant.
* `leibniz_T` (inhomogeneous fractional Leibniz on `𝕋_R`, uniformly in `R ≥ 1`): **direct** (Fourier-series paraproducts) or by
  transference of the `ℝ^d` bilinear multiplier bound (Coifman–Meyer type) — a Calderón-type periodisation argument for *bilinear* symbols;
  the family in `η` is needed (the `⟨∇⟩_η` weights).
* `mult_kernel_T`, `bernstein_T`: by Poisson summation from the `ℝ^d` kernel bounds (`Whole.mult_kernel_bounds`) — periodisation of an
  integrable kernel with the stated decay; Bernstein by Young.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s : ℝ}

/-- NRS22 Prop 3.1 on `𝕋^d`, generic case (`s ≠ d-2k`, `k ≥ 2`): for smooth mean-free real `a`,
`|𝒞_g(v,a)| ≲ C(v)‖a‖²_{Ḣ^{-α}}` with `‖a‖²_{Ḣ^{-α}} = ∑_{k≠0}(2π|k|)^{-2α}|â(k)|²`; `v` Lipschitz for `tdist`. -/
theorem nrs_T_generic (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (hgen : ¬ ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
      ∀ a : Torus d → ℝ, Torus.IsSmooth a → ∫ x, a x = 0 →
        ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) v a| ≤
          ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k) := by
  obtain ⟨CB, hCB0, hmul⟩ := nrstr_hmul hd hs0 hsd
  set α : ℝ := ((d : ℝ) - s) / 2 with hα
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hfl0 : (⌊α⌋₊ : ℝ) ≤ α := Nat.floor_le hα0
  have hfl1 : α < (⌊α⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one α
  have hα1 : 1 < α := by rw [hα]; linarith
  have hσ0 : 0 < α - ⌊α⌋₊ := by
    rcases hfl0.lt_or_eq with h1 | h1
    · linarith
    · exfalso
      apply hgen
      refine ⟨⌊α⌋₊, ?_, ?_⟩
      · have : (1 : ℝ) < ⌊α⌋₊ := by rw [h1]; exact hα1
        exact_mod_cast this
      · have : (d : ℝ) - s = 2 * ⌊α⌋₊ := by rw [h1, hα]; ring
        linarith
  have hσ1 : α - ⌊α⌋₊ < 1 := by linarith
  have hd1 : 1 ≤ d := by omega
  refine NRST.nrst_main hd hs0 hsd (C0 := (d : ℝ) + ((d : ℝ) + 2 * (α - ⌊α⌋₊) + 2) / 2) (CB := CB)
    (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; positivity) hCB0
    (fun V hVr L hL0 hLip h _ => ?_) hmul
  exact nrstr_hbase hd1 hσ0 hσ1 V hVr hL0 hLip h

/-- NRS22 Prop 3.1 on `𝕋^d`, exceptional integer case `s = d-2k`, `k ≥ 2` (Christ–Journé, or the polyharmonic stress-tensor route). -/
theorem nrs_T_exceptional (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (hexc : ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
      ∀ a : Torus d → ℝ, Torus.IsSmooth a → ∫ x, a x = 0 →
        ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) v a| ≤
          ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k) := by
  obtain ⟨CB, hCB0, hmul⟩ := nrstr_hmul hd hs0 hsd
  obtain ⟨k, hk2, hsk⟩ := hexc
  have hα : ((d : ℝ) - s) / 2 = (k : ℝ) := by rw [hsk]; ring
  refine NRST.nrst_main hd hs0 hsd (C0 := (d : ℝ) / 2) (CB := CB) (by positivity) hCB0
    (fun V hVr L hL0 hLip h _ => ?_) hmul
  rw [hα, Nat.floor_natCast, sub_self]
  exact NRST.base_exceptional V hVr hL0 hLip h

/-- The unrenormalized torus commutator estimate `(4.knowncomm)`; proved from the two cases. -/
theorem nrs_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
      ∀ a : Torus d → ℝ, Torus.IsSmooth a → ∫ x, a x = 0 →
        ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) v a| ≤
          ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k) := by
  by_cases h : ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k
  · exact nrs_T_exceptional hd hs0 hsd h
  · exact nrs_T_generic hd hs0 hsd h

/-- HLS/Sobolev on `𝕋^d` for mean-free functions: for `1 < p < q < ∞`, `σ > 0`, `q⁻¹ = p⁻¹ - σ/d` and `f ∈ L^p` with
`f̂(0) = 0` there is `h ∈ L^q` with `ĥ(k) = (2π|k|)^{-σ} f̂(k)` and `‖h‖_q ≲ ‖f‖_p` (period 1; scale invariant, hence also
for every `𝕋_R`). -/
theorem hls_T (hd : 1 ≤ d) (σ : ℝ) (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq : q < ⊤) (hσ : 0 < σ)
    (hrel : q⁻¹ = p⁻¹ - ENNReal.ofReal (σ / d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Torus d → ℝ, MemLp f p volume → Torus.fcoef f 0 = 0 →
      ∃ h : Torus d → ℝ, MemLp h q volume ∧ Torus.fcoef h 0 = 0 ∧
        (∀ k : Lattice d, k ≠ 0 → Torus.fcoef h k =
          (((2 * Real.pi * Lattice.enorm k) ^ (-σ) : ℝ) : ℂ) * Torus.fcoef f k) ∧
        eLpNorm h q volume ≤ ENNReal.ofReal C * eLpNorm f p volume :=
  text_hls_main hd σ p q hp hpq hq hσ hrel

/-- The torus embedding `HasFracBound d v F ⇒` the note's norm (`a = d+1`, `|∇|^{(d-s)/2}v = |∇|^{-σ}|∇|^{(d+1)/2}v`,
`σ = (s+1)/2`, `1/q = (d-1)/(2d) - (s+1)/(2d) = (d-s-2)/(2d)`; `|∇|^{(d+1)/2}v` has mean zero): from `hls_T`. -/
theorem embedding_T (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Torus d → Euc d) (F : ℝ), 0 ≤ F → Commutator.HasFracBound d v F →
      ∃ w : Torus d → Euc d, IsFracDeriv (((d : ℝ) - s) / 2) v w ∧
        eLpNorm w (ENNReal.ofReal (2 * d / ((d : ℝ) - s - 2))) volume ≤ ENNReal.ofReal (C * F) :=
  text_embedding_main hd hs0 hsd

/-- Inhomogeneous fractional Leibniz on `𝕋_R` (Li (1.15), `J^s` variant), uniformly in the scale `η = 1/R ∈ (0,1]`
(`⟨∇⟩_η` has symbol `(1+4π²η²|k|²)^{1/2}`); smooth real `f, g, h = fg`, with distributional Bessel derivatives `F, G, H` (integrable: for a non-integrable
`H` all Fourier coefficients are the Bochner junk `0`). -/
theorem leibniz_T (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) (r p₁ q₁ p₂ q₂ : ℝ≥0∞)
    (hr : 1 < r) (hr' : r < ⊤) (hp₁ : 1 < p₁) (hq₁ : 1 < q₁) (hp₂ : 1 < p₂) (hq₂ : 1 < q₂)
    (h1 : p₁⁻¹ + q₁⁻¹ = r⁻¹) (h2 : p₂⁻¹ + q₂⁻¹ = r⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ f g h F G H : Torus d → ℝ,
      Torus.IsSmooth f → Torus.IsSmooth g → (∀ x, h x = f x * g x) →
      Integrable F → Integrable G → Integrable H →
      IsBesselRepT η α f F → IsBesselRepT η α g G → IsBesselRepT η α h H →
        eLpNorm H r volume ≤ ENNReal.ofReal C *
          (eLpNorm F p₁ volume * eLpNorm g q₁ volume + eLpNorm G p₂ volume * eLpNorm f q₂ volume) :=
  leibt_main hd α hα r p₁ q₁ p₂ q₂ hr hr' hp₁ hq₁ hp₂ hq₂ h1 h2

/-- Multiplier kernel at scale `η` (`[N] (3.K-bounds)` L466-468 on `𝕋_R`; `K(x) = η^{γ-d}K̃(x/η)`, periodising the `ℝ^d` kernel):
for `0 < γ < d` there are constants `C`, `C_m` (independent of `η`) such that for every `η ∈ (0,1]` there is `K` with coefficients
`(1-χ(ηk))(2π|k|)^{-γ}` (`k ≠ 0`; `0` at `k=0`), `|K(x)| ≤ C|x|^{γ-d}` for `|x|_𝕋 ≤ η` and
`|K(x)| ≤ C_m η^{γ-d+m}|x|^{-m}` for `η ≤ |x|_𝕋`; in particular `‖K‖_{L¹} ≲ η^γ`. -/
theorem mult_kernel_T (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (hγd : γ < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ Cm : ℕ → ℝ, (∀ m, 0 < Cm m) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ K : Torus d → ℝ, Integrable K ∧
        (∀ k : Lattice d, Torus.fcoef K k = ((if k = 0 then 0 else
            (1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * Lattice.enorm k) ^ (-γ) : ℝ) : ℂ)) ∧
        (∀ x : Torus d, x ≠ 0 → KernelGrad.tdist x 0 ≤ η → |K x| ≤ C * KernelGrad.tdist x 0 ^ (γ - d)) ∧
        (∀ (m : ℕ) (x : Torus d), η ≤ KernelGrad.tdist x 0 →
            |K x| ≤ Cm m * η ^ (γ - d + m) * KernelGrad.tdist x 0 ^ (-(m : ℝ))) :=
  text_mult_kernel_main hd γ hγ hγd

/-- Bernstein/Young at scale `η`: `1 ≤ p ≤ q ≤ ∞`, coefficients vanishing for `η|k| > R` give
`‖a‖_q ≲_{d,R,p,q} η^{-d(1/p-1/q)}‖a‖_p`. -/
theorem bernstein_T (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R) (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ a : Torus d → ℝ, MemLp a p volume →
      (∀ k : Lattice d, R < η * Lattice.enorm k → Torus.fcoef a k = 0) →
        MemLp a q volume ∧
          eLpNorm a q volume ≤ ENNReal.ofReal (C * η ^ (-(d : ℝ) * ((p⁻¹).toReal - (q⁻¹).toReal))) *
            eLpNorm a p volume :=
  text_bernstein_main hd R hR p q hp hpq

end HRS.Commutator.TorusNote
