import HRS.Main.A34Aux10

/-!
# Packet A34, helper 11: truncated Fourier approximation of a continuous `H^m` function
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main HRS.StaticLimitAux

variable {d : ℕ}

lemma a34_res_coeff {φ : Torus d → ℝ} (hφc : Continuous φ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ)
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (a33_res φ e n) k =
      Torus.funRealCoeff φ k * (if e.symm k < n then 0 else 1) := by
  have hc : ∀ l : NonzeroLattice d, Continuous (Torus.realMode l) := fun l =>
    a33_cont (HRS.FieldSingAux.isSmooth_realMode l)
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f := fun hf => a33_integrable hf
  have hres : ∀ x, a33_res φ e n x = φ x - Torus.mean φ -
      ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x := fun x => rfl
  simp only [Torus.funRealCoeff, hres]
  have h1 : ∀ x, Torus.realMode k x * (φ x - Torus.mean φ -
      ∑ i ∈ Finset.range n, (∫ y, Torus.realMode (e i) y * φ y) * Torus.realMode (e i) x) =
      Torus.realMode k x * φ x - Torus.mean φ * Torus.realMode k x -
        ∑ i ∈ Finset.range n, (∫ y, Torus.realMode (e i) y * φ y) *
          (Torus.realMode k x * Torus.realMode (e i) x) := by
    intro x
    rw [mul_sub, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [h1]
  have i1 : Integrable fun x => Torus.realMode k x * φ x := hint ((hc k).mul hφc)
  have i2 : Integrable fun x => Torus.mean φ * Torus.realMode k x := hint (continuous_const.mul (hc k))
  have i3 : ∀ i ∈ Finset.range n, Integrable fun x => (∫ y, Torus.realMode (e i) y * φ y) *
      (Torus.realMode k x * Torus.realMode (e i) x) := fun i _ =>
    hint (continuous_const.mul ((hc k).mul (hc _)))
  have iA : Integrable fun x => Torus.realMode k x * φ x - Torus.mean φ * Torus.realMode k x :=
    i1.sub i2
  have iB : Integrable fun x => ∑ i ∈ Finset.range n, (∫ y, Torus.realMode (e i) y * φ y) *
      (Torus.realMode k x * Torus.realMode (e i) x) := integrable_finsetSum _ i3
  rw [integral_sub iA iB, integral_sub i1 i2, integral_finset_sum _ i3, integral_const_mul,
    Torus.integral_realMode]
  simp_rw [integral_const_mul, Torus.realMode_orthonormal]
  simp only [mul_zero, sub_zero]
  have hsum : ∑ i ∈ Finset.range n, (∫ y, Torus.realMode (e i) y * φ y) *
      (if k = e i then (1 : ℝ) else 0) = if e.symm k < n then Torus.funRealCoeff φ k else 0 := by
    have : ∀ i, (if k = e i then (1 : ℝ) else 0) = if i = e.symm k then 1 else 0 := by
      intro i
      by_cases h : i = e.symm k
      · subst h; simp
      · have : k ≠ e i := fun hk => h (by rw [hk]; simp)
        simp [this, h]
    simp_rw [this, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.range n) (e.symm k)]
    simp only [Finset.mem_range, Equiv.apply_symm_apply]
    rfl
  rw [hsum]
  split_ifs <;> simp [Torus.funRealCoeff]

lemma a34_res_mean {φ : Torus d → ℝ} (hφc : Continuous φ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    Torus.mean (a33_res φ e n) = 0 := by
  have hc : ∀ l : NonzeroLattice d, Continuous (Torus.realMode l) := fun l =>
    a33_cont (HRS.FieldSingAux.isSmooth_realMode l)
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f := fun hf => a33_integrable hf
  have hres : ∀ x, a33_res φ e n x = φ x - Torus.mean φ -
      ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x := fun x => rfl
  have i3 : ∀ i ∈ Finset.range n, Integrable fun x =>
      Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x := fun i _ =>
    hint (continuous_const.mul (hc _))
  have iA : Integrable fun x => φ x - Torus.mean φ := (hint hφc).sub (integrable_const _)
  have iB : Integrable fun x => ∑ i ∈ Finset.range n,
      Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x := integrable_finsetSum _ i3
  show ∫ x, a33_res φ e n x = 0
  simp only [hres]
  rw [integral_sub iA iB, integral_sub (hint hφc) (integrable_const _), integral_finset_sum _ i3]
  simp_rw [integral_const_mul, Torus.integral_realMode]
  simp [Torus.mean]

/-- The truncation error tends to zero in every Sobolev norm. -/
lemma a34_trunc_sob {m : ℝ} {φ : Torus d → ℝ} (hφc : Continuous φ) (hφm : MemSobolev m φ) (e : ℕ ≃ NonzeroLattice d) :
    (∀ n, MemSobolev m (a33_res φ e n)) ∧
      Tendsto (fun n => sobolevNorm m (a33_res φ e n)) atTop (𝓝 0) := by
  have hcoef := a34_res_coeff hφc e
  have hmem : ∀ n, MemSobolev m (a33_res φ e n) := by
    intro n
    have hrc : Continuous (a33_res φ e n) :=
      (hφc.sub continuous_const).sub (a33_cont (a33_tr_smooth φ e n))
    refine ⟨hrc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hφm.2
    · exact mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
    · rw [hcoef n k]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Torus.jp_pos _).le _)
      split_ifs <;> simp <;> positivity
  refine ⟨hmem, ?_⟩
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2
    with hw
  have hwsum : Summable w := hφm.2
  set f : ℕ → ℝ := fun i => w (e i) with hf
  have hfsum : Summable f := (e.summable_iff.2 hwsum)
  have htsum : ∀ n, ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) *
      Torus.funRealCoeff (a33_res φ e n) k ^ 2 = ∑' i, f i - ∑ i ∈ Finset.range n, f i := by
    intro n
    have h1 : ∀ k, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff (a33_res φ e n) k ^ 2 =
        w k * (if e.symm k < n then 0 else 1) := by
      intro k
      rw [hcoef n k, hw]
      simp only
      split_ifs <;> ring
    simp_rw [h1]
    rw [← e.tsum_eq (fun k => w k * (if e.symm k < n then 0 else 1))]
    have h2 : ∀ i, w (e i) * (if e.symm (e i) < n then (0 : ℝ) else 1) =
        f i - (if i < n then f i else 0) := by
      intro i
      simp only [Equiv.symm_apply_apply, hf]
      split_ifs <;> ring
    simp_rw [h2]
    have hfin : Summable fun i => if i < n then f i else 0 :=
      summable_of_ne_finset_zero (s := Finset.range n) fun i hi =>
        if_neg (fun hlt => hi (Finset.mem_range.2 hlt))
    rw [hfsum.tsum_sub hfin, tsum_eq_sum (s := Finset.range n) (fun i hi =>
      if_neg (fun hlt => hi (Finset.mem_range.2 hlt)))]
    congr 1
    exact Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.1 hi)
  have hlim : Tendsto (fun n => ∑' i, f i - ∑ i ∈ Finset.range n, f i) atTop (𝓝 0) := by
    have := hfsum.hasSum.tendsto_sum_nat
    simpa using (tendsto_const_nhds (x := ∑' i, f i)).sub this
  have hnorm : ∀ n, sobolevNorm m (a33_res φ e n) =
      Real.sqrt (∑' i, f i - ∑ i ∈ Finset.range n, f i) := by
    intro n
    unfold sobolevNorm
    rw [a34_res_mean hφc e n, htsum n]
    simp
  simp_rw [hnorm]
  have := (Real.continuous_sqrt.tendsto 0).comp hlim
  simpa [Function.comp_def] using this


theorem a34_prop_sub (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s J R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {φ φ' : Torus d → ℝ} (hφc : Continuous φ) (hφ : MemSobolev (J : ℝ) φ)
    (hφ'c : Continuous φ') (hφ' : MemSobolev (J : ℝ) φ') {r : ℝ} (hr : r ∈ Set.Icc 0 t) :
    propagator D μ r t (fun x => φ x - φ' x) =
      fun x => propagator D μ r t φ x - propagator D μ r t φ' x := by
  have hA' : AdjointData D.s J R MB Λ VB D ν₀ T μ := by rw [hA.hs]; exact hA
  have h := prop_lin hd D.s D.hs0 D.hsd J hJ R MB Λ VB D ν₀ T μ hA' ht (φ := φ) (ψ := φ')
    ⟨hφc, hφ⟩ ⟨hφ'c, hφ'⟩ 1 (-1) hr
  have e : (fun x => φ x - φ' x) = fun x => 1 * φ x + (-1) * φ' x := by funext x; ring
  rw [e, h]
  funext x; ring

end HRS.A34
