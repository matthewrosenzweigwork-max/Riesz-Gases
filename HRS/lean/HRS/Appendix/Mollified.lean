import HRS.PDE.Toolbox
import HRS.Kernel.HigherDerivBounds

/-!
# Appendix C: Lemma C.2 (mollified kernels), statement (packet SPEC-D, part C)

Source: `HRS_periodic_main_20261008T010000Z.tex`, Lemma C.2 `M:B:lem:mollified-kernels`
(L12235-12237), with `γ_δ` as in Step 1 of `B:sec:adjoint-existence` (L1957):
`χ₁ ∈ C_c^∞(ℝ^d;[0,1])` radial, `χ₁ ≡ 1` on `B(0,1)`, `supp χ₁ ⊂ B(0,2)`, and `ĝ_δ(k) = ĝ(k) χ₁(δk)²`.

## Representation decisions

* The cutoff `χ₁` is the existing `HRS.PDE.IsFriedrichsCutoff` (reused, not redefined).
* `mollifiedRiesz d s χ δ` is the trigonometric series `∑_k ĝ(k) χ₁(δk)² cos(2π k·x)`, i.e. the function
  with Fourier coefficients `ĝ(k) χ₁(δk)²` (`ĝ` even, `rieszCoeff`).  Because `χ₁(δk) = 0` for `|δk| ≥ 2`
  the series is a finite trigonometric sum, so the `tsum` is not a junk value.
* The TeX range `1 ≤ n ≤ m + 2` (with `m` the regularity level of the surrounding section, the constant
  `C_n` not depending on `m`) is stated as "for every `n ≥ 1`".
* `|x|` on the torus is the quotient distance `KernelGrad.tdist x 0` (norm of the centered representative);
  derivatives are taken on the covering space (`iteratedFDeriv` of the periodic lift) at a point `y` with
  `mk y ≠ 0` (the bounds are meaningless at `x = 0`, where `|x|^{-s-n} = ∞`).
* Constants `C_n`, `C` depend on `d, s, n` and the cutoff `χ₁` and are chosen before `δ` and `x`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

/-- The mollified periodic Riesz/log kernel `g_δ` with `ĝ_δ(k) = ĝ(k) χ₁(δk)²`
(Step 1 of `B:sec:adjoint-existence`, TeX M L1957): `g_δ(x) = ∑_k ĝ(k) χ₁(δk)² cos(2π k·x)`
(a finite sum since `χ₁` has compact support). -/
def mollifiedRiesz (d : ℕ) (s : ℝ) (χ : Euc d → ℝ) (δ : ℝ) (x : Torus d) : ℝ :=
  ∑' k : Lattice d, rieszCoeff d s k * χ (δ • Lattice.toEuc k) ^ 2 * Torus.cosMode k x

/-- `g_δ` is the trigonometric series `mollSum` of `HRS.HDB` -/
theorem mollifiedRiesz_eq_mollSum (s : ℝ) (χ : Euc d → ℝ) (δ : ℝ) :
    mollifiedRiesz d s χ δ = HDB.mollSum d s χ δ := rfl

theorem rieszCoeff_nonneg_of_one_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) :
    0 ≤ rieszCoeff d s k := by
  have h := KernelD1Aux.rieszConst_pos_d1 hd hs0 hsd
  unfold rieszCoeff
  split_ifs
  · exact le_rfl
  · exact mul_nonneg h.le (Real.rpow_nonneg (by unfold Lattice.enorm; positivity) _)

theorem mollifiedRiesz_neg (s : ℝ) (χ : Euc d → ℝ) (δ : ℝ) (x : Torus d) :
    mollifiedRiesz d s χ δ (-x) = mollifiedRiesz d s χ δ x := by
  unfold mollifiedRiesz
  refine tsum_congr fun k => ?_
  have : Torus.cosMode k (-x) = Torus.cosMode k x := by
    unfold Torus.cosMode
    rw [PDE.LevyAux.mode_neg_arg, Torus.mode_neg, Complex.conj_re]
  rw [this]

/-- the coefficients of `g_δ`: `fcoef g_δ k = ĝ(k) χ(δk)²` -/
theorem fcoef_mollifiedRiesz (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {χ : Euc d → ℝ}
    (hχ : PDE.IsFriedrichsCutoff χ) {δ : ℝ} (hδ : 0 < δ) (k : Lattice d) :
    Torus.fcoef (mollifiedRiesz d s χ δ) k =
      ((rieszCoeff d s k * χ (δ • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) := by
  have h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0 := hχ.support
  set b : Lattice d → ℂ := fun k => ((HDB.bC d s χ δ k : ℝ) : ℂ) with hb
  have hT : PDE.IsTrigPoly ⌈2 / δ⌉₊ b :=
    HDB.isTrigPoly_of_enorm_lt (fun k hk => HDB.bC_support h2 hδ k (by simpa [hb] using hk))
  have hbeven : ∀ k, b (-k) = b k := by
    intro k
    simp only [hb, HDB.bC]
    have h1 : rieszCoeff d s (-k) = rieszCoeff d s k := rieszCoeff_neg k
    have h3 : Lattice.toEuc (-k) = -Lattice.toEuc k := by ext i; simp [Lattice.toEuc]
    have h4 : ‖δ • Lattice.toEuc k‖ = ‖δ • Lattice.toEuc (-k)‖ := by rw [h3, smul_neg, norm_neg]
    rw [h1, hχ.radial _ _ h4.symm]
  -- the function is the trigonometric polynomial `trig b`
  have hfun : ∀ x : Torus d, ((mollifiedRiesz d s χ δ x : ℝ) : ℂ) = PDE.Kern.trig b x := by
    intro x
    have hs1 : Summable fun k => b k * Torus.mode k x := PDE.Kern.summable_trig hT x
    have hs2 : Summable fun k => b k * Torus.mode (-k) x := by
      refine summable_of_ne_finset_zero (s := PDE.Kern.boxF d ⌈2 / δ⌉₊) fun k hk => ?_
      have : b k = 0 := by
        by_contra h
        exact hk (PDE.Kern.mem_boxF.2 (hT k h))
      simp [this]
    have hneg : PDE.Kern.trig b x = ∑' k, b k * Torus.mode (-k) x := by
      unfold PDE.Kern.trig
      rw [← (Equiv.neg (Lattice d)).tsum_eq (fun k => b k * Torus.mode k x)]
      exact tsum_congr fun k => by simp [hbeven]
    have h2x : 2 * PDE.Kern.trig b x = ∑' k, b k * (2 * (Torus.cosMode k x : ℂ)) := by
      have : ∀ k, b k * (2 * (Torus.cosMode k x : ℂ)) = b k * Torus.mode k x + b k * Torus.mode (-k) x := by
        intro k
        rw [Torus.mode_neg, Torus.cosMode, ← mul_add, Complex.add_conj]
        push_cast; ring
      simp_rw [this]
      rw [hs1.tsum_add hs2, ← hneg]
      unfold PDE.Kern.trig; ring
    have : PDE.Kern.trig b x = ∑' k, b k * (Torus.cosMode k x : ℂ) := by
      have h3 : ∑' k, b k * (2 * (Torus.cosMode k x : ℂ)) = 2 * ∑' k, b k * (Torus.cosMode k x : ℂ) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun k => by ring
      rw [h3] at h2x
      exact mul_left_cancel₀ two_ne_zero h2x
    rw [this]
    unfold mollifiedRiesz
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun k => by simp [hb, HDB.bC]
  have hcoef : Torus.fcoef (mollifiedRiesz d s χ δ) k = PDE.coeffOfC (PDE.Kern.trig b) k := by
    unfold Torus.fcoef
    rw [PDE.coeffOfC_eq_integral']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Torus.mode_neg, hfun x]
  rw [hcoef, PDE.Fried.coeffOfC_trig hT]
  simp [hb, HDB.bC]

/-- Lemma C.2 (`M:B:lem:mollified-kernels`, TeX M L12235-12237).  Let `γ_δ` be the mollified kernel,
`0 ≤ s < d`.  Then
* for `n ≥ 1` and `0 < δ ≤ 1`, `|∇^{⊗n} g_δ(x)| ≤ C_n (|x|^{-s-n} + 1)`, uniformly in `δ`;
* for `n = 0` the same bound `|g_δ(x)| ≤ C (|x|^{-s} + 1)` holds when `s > 0`, while in the logarithmic
  case `s = 0`, `|g_δ(x)| ≤ C (1 + |log(δ ∨ |x|)|)`;
* in all cases `g_δ` is even and `ĝ_δ ≥ 0` (`ĝ_δ(k) = ĝ(k) χ₁(δk)² ≥ 0` is the Fourier coefficient of
  `g_δ`, stated through `Torus.fcoef`).
Pointwise bounds are for `x ≠ 0`.  Technical hypotheses: `1 ≤ d` (`d = 0` is degenerate). -/
theorem mollified_kernels (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {χ : Euc d → ℝ} (hχ : PDE.IsFriedrichsCutoff χ) :
    (∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ y : Euc d, Torus.mk y ≠ 0 →
        ‖iteratedFDeriv ℝ n (Torus.lift (mollifiedRiesz d s χ δ)) y‖ ≤
          C * (KernelGrad.tdist (Torus.mk y) 0 ^ (-s - (n : ℝ)) + 1)) ∧
    (0 < s → ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Torus d, x ≠ 0 →
        |mollifiedRiesz d s χ δ x| ≤ C * (KernelGrad.tdist x 0 ^ (-s) + 1)) ∧
    (s = 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : Torus d, x ≠ 0 →
        |mollifiedRiesz d s χ δ x| ≤ C * (1 + |Real.log (max δ (KernelGrad.tdist x 0))|)) ∧
    (∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ x : Torus d, mollifiedRiesz d s χ δ (-x) = mollifiedRiesz d s χ δ x) ∧
      ∀ k : Lattice d,
        Torus.fcoef (mollifiedRiesz d s χ δ) k =
            ((rieszCoeff d s k * χ (δ • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) ∧
          0 ≤ rieszCoeff d s k * χ (δ • Lattice.toEuc k) ^ 2) := by
  have hcut := hχ
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hχ.smooth
  have h0 : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1 := hχ.range
  have h1 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1 := hχ.one
  have h2 : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0 := hχ.support
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨C, hC0, hC⟩ := HDB.deriv_bound_pos hd hsd hs h0 h1 h2 n (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)
    exact ⟨C, hC0, fun δ hδ hδ1 y hy => hC δ hδ hδ1 y hy⟩
  · intro hs'
    obtain ⟨C, hC0, hC⟩ := HDB.zeroth_bound_pos hd hsd hs h0 h1 h2 hs'
    exact ⟨C, hC0, fun δ hδ hδ1 x hx => hC δ hδ hδ1 x hx⟩
  · intro hs'
    subst hs'
    obtain ⟨C, hC0, hC⟩ := HDB.zeroth_bound_log hd hsd hs h0 h1 h2
    exact ⟨C, hC0, fun δ hδ hδ1 x hx => hC δ hδ hδ1 x hx⟩
  · intro δ hδ hδ1
    refine ⟨mollifiedRiesz_neg s χ δ, fun k => ⟨fcoef_mollifiedRiesz hd hs0 hsd hχ hδ k, ?_⟩⟩
    exact mul_nonneg (rieszCoeff_nonneg_of_one_le hd hs0 hsd k) (sq_nonneg _)

end HRS
