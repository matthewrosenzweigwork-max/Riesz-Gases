import HRS.PDE.WellPosed

/-!
# S.A.12 C4 (SA12W2 worker), part A: jets of Fourier series on the torus

Evaluation bound `‖D^j (toFun c) (y)‖ ≤ C ‖c‖_{H^m}` (`m > d/2 + j`, real `c`) and the linear combination identity
`D^j toFun (r (a - b) - e) = r (D^j toFun a - D^j toFun b) - D^j toFun e`, used by `sa12w2_C4` (SA12W2B).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

theorem sa12w2_toFun_comb (a b e : Coeff d) (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖)
    (he : Summable fun k => ‖e k‖) (r : ℝ) (x : Torus d) :
    toFun (fun k => (r : ℂ) * (a k - b k) - e k) x = r * (toFun a x - toFun b x) - toFun e x := by
  unfold toFun series
  have h1 := summable_series_terms a ha x
  have h2 := summable_series_terms b hb x
  have h3 := summable_series_terms e he x
  have h4 : ∑' k, ((r : ℂ) * (a k - b k) - e k) * Torus.mode k x
      = (r : ℂ) * (∑' k, a k * Torus.mode k x - ∑' k, b k * Torus.mode k x)
        - ∑' k, e k * Torus.mode k x := by
    rw [← h1.tsum_sub h2, ← tsum_mul_left, ← ((h1.sub h2).mul_left (r : ℂ)).tsum_sub h3]
    congr 1
    funext k
    ring
  rw [h4, Complex.sub_re, Complex.re_ofReal_mul, Complex.sub_re]

theorem sa12w2_memHs_comb {m : ℝ} {a b e : Coeff d} (ha : MemHs m a) (hb : MemHs m b) (he : MemHs m e)
    (r : ℝ) : MemHs m (fun k => (r : ℂ) * (a k - b k) - e k) := by
  have h1 : MemHs m (a - b) := memHs_sub ha hb
  have h2 : MemHs m (fun k => (r : ℂ) * (a k - b k)) := by
    unfold MemHs at *
    refine (h1.mul_left (‖(r : ℂ)‖ ^ 2)).congr fun k => ?_
    simp only [norm_mul, Pi.sub_apply]
    ring
  exact memHs_sub h2 he

theorem sa12w2_isReal_comb {a b e : Coeff d} (ha : IsRealCoeff a) (hb : IsRealCoeff b) (he : IsRealCoeff e)
    (r : ℝ) : IsRealCoeff (fun k => (r : ℂ) * (a k - b k) - e k) := by
  intro k
  simp only [ha k, hb k, he k, map_sub, map_mul, Complex.conj_ofReal]

/-- Sobolev evaluation bound for the jets of the Fourier series of a real coefficient. -/
theorem sa12w2_jet_bound (j : ℕ) (m : ℝ) (hm : (d : ℝ) / 2 + j < m) :
    ∃ C : ℝ, ∀ c : Coeff d, MemHs m c → IsRealCoeff c → ∀ y : Euc d,
      ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift (toFun c)) ∧
        ‖iteratedFDeriv ℝ j (Torus.lift (toFun c)) y‖ ≤ C * hsNorm m c := by
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) j m hm
  refine ⟨C, fun c hc hr y => ?_⟩
  obtain ⟨h1, h2⟩ := hC c hc hr
  exact ⟨h1, (norm_iteratedFDeriv_le_cbNorm j j le_rfl _ h1 y).trans h2⟩

theorem sa12w2_jet_comb (j : ℕ) (m : ℝ) (hm : (d : ℝ) / 2 + j < m) (a b e : Coeff d)
    (ha : MemHs m a) (hb : MemHs m b) (he : MemHs m e)
    (hra : IsRealCoeff a) (hrb : IsRealCoeff b) (hre : IsRealCoeff e) (r : ℝ) (y : Euc d) :
    iteratedFDeriv ℝ j (Torus.lift (toFun (fun k => (r : ℂ) * (a k - b k) - e k))) y =
      r • (iteratedFDeriv ℝ j (Torus.lift (toFun a)) y - iteratedFDeriv ℝ j (Torus.lift (toFun b)) y)
        - iteratedFDeriv ℝ j (Torus.lift (toFun e)) y := by
  obtain ⟨C, hC⟩ := sa12w2_jet_bound j m hm
  have hd : (d : ℝ) / 2 < m := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have h1 := summable_norm_of_memHs m hd a ha
  have h2 := summable_norm_of_memHs m hd b hb
  have h3 := summable_norm_of_memHs m hd e he
  have hca := (hC a ha hra y).1
  have hcb := (hC b hb hrb y).1
  have hce := (hC e he hre y).1
  have hf : Torus.lift (toFun (fun k => (r : ℂ) * (a k - b k) - e k)) =
      r • (Torus.lift (toFun a) - Torus.lift (toFun b)) - Torus.lift (toFun e) := by
    funext z
    simp only [Torus.lift, Function.comp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact sa12w2_toFun_comb a b e h1 h2 h3 r _
  have hab : ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift (toFun a) - Torus.lift (toFun b)) := hca.sub hcb
  have hs : ContDiff ℝ (j : WithTop ℕ∞) (r • (Torus.lift (toFun a) - Torus.lift (toFun b))) :=
    hab.const_smul r
  rw [hf, iteratedFDeriv_sub_apply hs.contDiffAt hce.contDiffAt,
    iteratedFDeriv_const_smul_apply hab.contDiffAt,
    iteratedFDeriv_sub_apply hca.contDiffAt hcb.contDiffAt]

end HRS.PDE.SA12W2
