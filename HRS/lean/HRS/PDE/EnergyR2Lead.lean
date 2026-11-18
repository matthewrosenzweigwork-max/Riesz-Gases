import HRS.PDE.EnergyR2Q
import HRS.PDE.EnergyR2Dec

/-!
# Regime R2: the leading term (`β = 0`) of `⟨∂^α𝒢[F], ∂^αF⟩`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

theorem bilinForm_self (𝔪 : Lattice d → ℝ) (c : Coeff d) :
    bilinForm 𝔪 c c = ((quadForm 𝔪 c : ℝ) : ℂ) := by
  unfold bilinForm quadForm
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul]

theorem bilinForm_box' {n : ℕ} (w : Lattice d → ℝ) (G F : Coeff d) (hF : IsTrigPoly n F) :
    bilinForm w G F = ∑ k ∈ boxFin d n, ((w k : ℝ) : ℂ) * (G k * conj (F k)) := by
  unfold bilinForm
  refine tsum_eq_sum fun k hk => ?_
  rw [eq_zero_of_isTrigPoly hF hk]; simp

/-- `Re` of the `K`-pairing is the symbol form of `μ w` against `w`. -/
theorem re_PK_eq {n : ℕ} (𝔪 : Lattice d → ℝ) (μ : Torus d → ℝ) (hμ : Continuous μ)
    {w : Coeff d} (hr : IsRealCoeff w) (hwt : IsTrigPoly n w) :
    (∑ k ∈ boxFin d n, conj (w k) * (((𝔪 k : ℝ) : ℂ) * mulCoeff (coeffOf μ) w k)).re =
      symbolForm 𝔪 (fun x => μ x * toFun w x) (toFun w) := by
  have hwc : Continuous (toFun w) := continuous_toFun_trig hr hwt
  have h1 : coeffOf (fun x => μ x * toFun w x) = mulCoeff (coeffOf μ) w := by
    rw [coeffOf_mul μ (toFun w) (memLp_of_continuous_real hμ) (memLp_of_continuous_real hwc),
      coeffOf_toFun_trig hr hwt]
  unfold symbolForm
  rw [h1, coeffOf_toFun_trig hr hwt, bilinForm_box' 𝔪 _ w hwt]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem quadForm_eq_symbolForm {n : ℕ} (𝔪 : Lattice d → ℝ) (a : Torus d → ℝ) (ha : Continuous a)
    {w : Coeff d} (hr : IsRealCoeff w) (hwt : IsTrigPoly n w) :
    symbolForm 𝔪 (fun x => a x * toFun w x) (fun x => a x * toFun w x) =
      quadForm 𝔪 (mulCoeff (coeffOf a) w) := by
  have hwc : Continuous (toFun w) := continuous_toFun_trig hr hwt
  have h1 : coeffOf (fun x => a x * toFun w x) = mulCoeff (coeffOf a) w := by
    rw [coeffOf_mul a (toFun w) (memLp_of_continuous_real ha) (memLp_of_continuous_real hwc),
      coeffOf_toFun_trig hr hwt]
  unfold symbolForm
  rw [h1, bilinForm_self]
  simp

/-- Iterated partial derivatives as functions: for `b ∈ C^K` and `|β| = p ≤ K`, there is
`φ ∈ C^{K-p}` with `‖φ‖_{C^{K-p}} ≤ ‖b‖_{C^K}` and Fourier coefficients `D_β b̂`. -/
theorem derivFn (b : Torus d → ℝ) : ∀ (p K : ℕ) (β : Fin d → ℕ), ∑ i, β i = p → p ≤ K →
    Torus.IsCk (K : WithTop ℕ∞) b →
    ∃ φ : Torus d → ℝ, Torus.IsCk ((K - p : ℕ) : WithTop ℕ∞) φ ∧
      Torus.cbNorm (K - p) φ ≤ Torus.cbNorm K b ∧
      coeffOf φ = multiDerivCoeff β (coeffOf b) := by
  intro p
  induction p with
  | zero =>
    intro K β hβ _ hb
    have : β = 0 := by
      funext i
      exact (Finset.sum_eq_zero_iff.mp hβ) i (Finset.mem_univ _)
    subst this
    exact ⟨b, by simpa using hb, by simp, by rw [multiDerivCoeff_zero]⟩
  | succ p ih =>
    intro K β hβ hpK hb
    have hex : ∃ j, 0 < β j := by
      by_contra h
      push Not at h
      have : ∑ i, β i = 0 := Finset.sum_eq_zero fun i _ => Nat.le_zero.mp (h i)
      omega
    obtain ⟨j, hj⟩ := hex
    set β' : Fin d → ℕ := Function.update β j (β j - 1) with hβ'
    have hβe : β = β' + Pi.single j 1 := by
      funext i
      by_cases hi : i = j
      · subst hi; simp [hβ']; omega
      · simp [hβ', hi]
    have hsum : ∑ i, β' i = p := by
      have h1 : ∑ i, β i = ∑ i, β' i + 1 := by
        conv_lhs => rw [hβe]
        simp [Finset.sum_add_distrib]
      omega
    obtain ⟨φ', h1, h2, h3⟩ := ih K β' hsum (by omega) hb
    have hKp : K - p = (K - (p + 1)) + 1 := by omega
    rw [hKp] at h1 h2
    obtain ⟨h4, h5⟩ := partialDeriv_cbNorm (K - (p + 1)) j φ' (by exact_mod_cast h1)
    refine ⟨Torus.partialDeriv j φ', h4, ?_, ?_⟩
    · refine h5.trans (h2.trans le_rfl)
    · have hφ1 : Torus.IsCk 1 φ' := h1.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))
      rw [coeffOf_partialDeriv j φ' hφ1, h3, derivCoeff_eq_multi, ← multiDerivCoeff_add, hβe]
      congr 1
      exact add_comm _ _


/-- The complex pairing splits along `ct_decomp` (integration by parts) with `a = coeffOf μ`. -/
theorem pairing_split {n : ℕ} (D : DynData d) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hdiag : ∀ i j, Torus.symPart D.M i j = -∑ l, lam l * q l i * q l j)
    (μ : Torus d → ℝ) (w : Coeff d) (hw : IsTrigPoly n w) :
    ∑ k ∈ boxFin d n, conj (w k) * nonlocalCoeff D μ w k =
      ∑ l, ((lam l : ℝ) : ℂ) * (∑ k ∈ boxFin d n, conj (w k) *
          (((symbolK d D.s (q l) k : ℝ) : ℂ) * mulCoeff (coeffOf μ) w k)) -
      ∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) * (∑ k ∈ boxFin d n, conj (w k) *
          (Ssym d D.s i k * mulCoeff (derivCoeff j (coeffOf μ)) w k)) := by
  have hk : ∀ k, nonlocalCoeff D μ w k =
      ∑ l, ((lam l : ℝ) : ℂ) * (((symbolK d D.s (q l) k : ℝ) : ℂ) * mulCoeff (coeffOf μ) w k) -
      ∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) * (Ssym d D.s i k * mulCoeff (derivCoeff j (coeffOf μ)) w k) :=
    fun k => ct_decomp D.M D.s lam q hdiag (coeffOf μ) w hw k
  simp_rw [hk, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem abs_partialDeriv_le_cb2 {μ : Torus d → ℝ} (hμ : Torus.IsCk 2 μ) (j : Fin d) (x : Torus d) :
    |Torus.partialDeriv j μ x| ≤ Torus.cbNorm 2 μ := by
  obtain ⟨h1, h2⟩ := partialDeriv_cbNorm 1 j μ (by simpa using hμ)
  have := abs_le_cbNorm h1 x
  exact this.trans (by simpa using h2)

theorem leading_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d)
    (hK : R2KernelFacts d s) (MB Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M →
      ∀ (lam : Fin d → ℝ) (q : Fin d → Euc d), (∀ l, 0 ≤ lam l) → Orthonormal ℝ q →
      (∀ i j, Torus.symPart D.M i j = -∑ l, lam l * q l i * q l j) →
      ∀ (μ : Torus d → ℝ), (∀ x, 0 ≤ μ x) → Torus.IsCk 2 μ → Torus.cbNorm 2 μ ≤ Λ →
      ∀ (n : ℕ) (w : Coeff d), IsRealCoeff w → IsTrigPoly n w →
      -(∑ k ∈ boxFin d n, conj (w k) * nonlocalCoeff D μ w k).re ≤
        -∑ l, lam l * quadForm (symbolK d s (q l))
            (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) + C * hsNormSq 0 w := by
  obtain ⟨Cw, hCw0, hCw⟩ := weighted_bound hd s hs0 hs1 hsd
  obtain ⟨Cs, hCs0, hCs⟩ := sameFunction_bound hd s hsd hK
  set dd : ℝ := (d : ℝ) with hdd
  set MB' : ℝ := |MB| with hMB'
  set Λ' : ℝ := |Λ| with hΛ'
  refine ⟨dd * MB' * (Cw * (3 / 2 * Λ')) * dd + dd * dd * MB' * (Cs * (Λ' + Λ' * Real.sqrt dd)),
    by positivity, ?_⟩
  intro D hDs hM lam q hlam hq hdiag μ hμ0 hμ2 hΛ n w hw hwt
  subst hDs
  have hμc : Continuous μ := continuous_of_lift' (hμ2.continuous)
  have hsq : Continuous fun x => Real.sqrt (μ x) := hμc.sqrt
  have hΛ0 : 0 ≤ Λ := (cbNorm_nonneg' 2 μ).trans hΛ
  have hΛa : Λ' = Λ := abs_of_nonneg hΛ0
  set f := toFun w with hf
  have hfc : Continuous f := continuous_toFun_trig hw hwt
  have hf1 : Torus.IsCk 1 f := isCk_toFun_trig hw hwt 1
  have hfS : MemSobolev (thetaOrder d D.s / 2) f := memSobolev_toFun_trig hw hwt _
  have hl2 : l2NormSq f = hsNormSq 0 w := by
    rw [l2NormSq_eq_hsNormSq hfc, hf, coeffOf_toFun_trig hw hwt]
  set N0 := hsNormSq 0 w with hN0
  have hN0nn : 0 ≤ N0 := hsNormSq_nonnegE 0 w
  have hMBnn : 0 ≤ MB' := abs_nonneg _
  have hMBle : ∀ i j, |D.M i j| ≤ MB' := fun i j => (hM i j).trans (le_abs_self _)
  have hd1 : 1 ≤ d := by omega
  have hdd0 : 0 ≤ dd := Nat.cast_nonneg _
  -- real part of the split
  have hsplit := pairing_split D lam q hdiag μ w hwt
  have hRe : (∑ k ∈ boxFin d n, conj (w k) * nonlocalCoeff D μ w k).re =
      ∑ l, lam l * symbolForm (symbolK d D.s (q l)) (fun x => μ x * f x) f -
      ∑ i, ∑ j, D.M j i * (∑ k ∈ boxFin d n, conj (w k) *
          (Ssym d D.s i k * mulCoeff (derivCoeff j (coeffOf μ)) w k)).re := by
    rw [hsplit, Complex.sub_re, Complex.re_sum, Complex.re_sum]
    congr 1
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.re_ofReal_mul, re_PK_eq _ μ hμc hw hwt]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_ofReal_mul]
  -- leading terms
  have hlead : ∀ l, symbolForm (symbolK d D.s (q l)) (fun x => μ x * f x) f ≥
      quadForm (symbolK d D.s (q l)) (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) -
        Cw * (3 / 2 * Λ') * N0 := by
    intro l
    have hql : ‖q l‖ ≤ 1 := (hq.1 l).le
    have h := hCw (q l) hql (Torus.cbNorm 2 μ) Λ μ f (cbNorm_nonneg' 2 μ) hμ0
      (fun x => (le_abs_self _).trans ((abs_le_cbNorm hμ2 x).trans hΛ)) (isC11_of_cbNorm hμ2)
      hf1 hfS
    have hq' : symbolForm (symbolK d D.s (q l)) (fun x => Real.sqrt (μ x) * f x)
        (fun x => Real.sqrt (μ x) * f x) = quadForm (symbolK d D.s (q l))
          (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) :=
      quadForm_eq_symbolForm _ _ hsq hw hwt
    rw [hl2, hq'] at h
    have h2 : Cw * (Torus.cbNorm 2 μ / 2 + Λ) * N0 ≤ Cw * (3 / 2 * Λ') * N0 := by
      rw [hΛa]
      gcongr
      linarith
    have := (abs_le.mp h).2
    have h3 := (abs_le.mp h).1
    linarith
  -- same-function terms
  have hsame : ∀ i j, |(∑ k ∈ boxFin d n, conj (w k) *
          (Ssym d D.s i k * mulCoeff (derivCoeff j (coeffOf μ)) w k)).re| ≤
      Cs * (Λ' + Λ' * Real.sqrt dd) * N0 := by
    intro i j
    have hc : coeffOf (Torus.partialDeriv j μ) = derivCoeff j (coeffOf μ) :=
      coeffOf_partialDeriv j μ (hμ2.of_le (by norm_num))
    have hLip := isLipschitz_partialDeriv hμ2 j
    have h := hCs i (Torus.cbNorm 2 μ) Λ (Torus.partialDeriv j μ) hLip
      (fun x => (abs_partialDeriv_le_cb2 hμ2 j x).trans hΛ) n w hw hwt
    rw [hc] at h
    refine h.trans ?_
    have hL : |Torus.cbNorm 2 μ| ≤ Λ' := by
      rw [abs_of_nonneg (cbNorm_nonneg' 2 μ), hΛa]; exact hΛ
    rw [← hN0]
    have : Λ + |Torus.cbNorm 2 μ| * Real.sqrt dd ≤ Λ' + Λ' * Real.sqrt dd := by
      rw [← hΛa]; gcongr
    gcongr
  rw [hRe]
  have e1 : ∑ l, lam l * symbolForm (symbolK d D.s (q l)) (fun x => μ x * f x) f ≥
      ∑ l, lam l * quadForm (symbolK d D.s (q l))
        (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) - dd * MB' * (Cw * (3 / 2 * Λ') * N0) * dd := by
    have : ∀ l, lam l * symbolForm (symbolK d D.s (q l)) (fun x => μ x * f x) f ≥
        lam l * quadForm (symbolK d D.s (q l))
          (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) - dd * MB' * (Cw * (3 / 2 * Λ') * N0) := by
      intro l
      have hl1 := lam_le hd1 MB D.M hM lam q hdiag hq l
      have hl2' : lam l ≤ dd * MB' := hl1.trans (by gcongr; exact le_abs_self _)
      have hE : 0 ≤ Cw * (3 / 2 * Λ') * N0 := by positivity
      have := hlead l
      nlinarith [hlam l, mul_le_mul_of_nonneg_right hl2' hE]
    calc ∑ l, lam l * symbolForm (symbolK d D.s (q l)) (fun x => μ x * f x) f
        ≥ ∑ l, (lam l * quadForm (symbolK d D.s (q l))
          (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) - dd * MB' * (Cw * (3 / 2 * Λ') * N0)) :=
          Finset.sum_le_sum fun l _ => this l
      _ = _ := by
          rw [Finset.sum_sub_distrib]
          simp [Finset.sum_const, Finset.card_univ, hdd]
          ring
  have e2 : |∑ i, ∑ j, D.M j i * (∑ k ∈ boxFin d n, conj (w k) *
          (Ssym d D.s i k * mulCoeff (derivCoeff j (coeffOf μ)) w k)).re| ≤
      dd * dd * MB' * (Cs * (Λ' + Λ' * Real.sqrt dd) * N0) := by
    calc _ ≤ ∑ i, ∑ j, |D.M j i * (∑ k ∈ boxFin d n, conj (w k) *
          (Ssym d D.s i k * mulCoeff (derivCoeff j (coeffOf μ)) w k)).re| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, MB' * (Cs * (Λ' + Λ' * Real.sqrt dd) * N0) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hMBle j i) (hsame i j) (abs_nonneg _) hMBnn
      _ = _ := by
          simp [Finset.sum_const, Finset.card_univ, hdd]
          ring
  have e3 := (abs_le.mp e2).2
  have e4 := (abs_le.mp e2).1
  have : 0 ≤ Cs * (Λ' + Λ' * Real.sqrt dd) * N0 := by positivity
  nlinarith [e1, e3, e4]


end HRS.PDE.R2Aux
