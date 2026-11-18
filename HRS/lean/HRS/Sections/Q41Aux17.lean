import HRS.Sections.Q41Aux16

/-!
# Packet Q41, helper 17: truncated real Fourier expansions of smooth functions converge in `C^j`

For smooth `φ` and an enumeration `e : ℕ ≃ NonzeroLattice d`, the truncation
`φ_n = ∑_{i<n} φ̂(e i) e_{e i}` converges to `φ - ∫φ` in every `C^j` norm (`q41_trunc_cb`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.PDE.MFPair

variable {d : ℕ}

/-- Truncated real Fourier expansion along an enumeration. -/
def q41_tr (φ : Torus d → ℝ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) (x : Torus d) : ℝ :=
  ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x

/-- The truncation error `φ - ∫φ - φ_n`. -/
def q41_res (φ : Torus d → ℝ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) (x : Torus d) : ℝ :=
  φ x - Torus.mean φ - q41_tr φ e n x

lemma q41_cont_of_smooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  MFAux.continuous_of_isCk (isCk_of_smooth_ps hf 1)

lemma q41_tr_smooth (φ : Torus d → ℝ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    Torus.IsSmooth (q41_tr φ e n) := by
  unfold Torus.IsSmooth Torus.IsCk
  have h : ∀ i : NonzeroLattice d, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Torus.lift (Torus.realMode i)) := fun i => HRS.FieldSingAux.isSmooth_realMode i
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x => ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * Torus.realMode (e i) (Torus.mk x))
  exact ContDiff.sum fun i _ => contDiff_const.mul (h (e i))

lemma q41_res_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    Torus.IsSmooth (q41_res φ e n) := by
  have h1 := q41_tr_smooth φ e n
  unfold Torus.IsSmooth Torus.IsCk at *
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x => φ (Torus.mk x) - Torus.mean φ - q41_tr φ e n (Torus.mk x))
  exact (hφ.sub contDiff_const).sub h1

lemma q41_res_coeff {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ)
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (q41_res φ e n) k =
      Torus.funRealCoeff φ k * (if e.symm k < n then 0 else 1) := by
  have hc : ∀ l : NonzeroLattice d, Continuous (Torus.realMode l) := fun l =>
    q41_cont_of_smooth (HRS.FieldSingAux.isSmooth_realMode l)
  have hφc := q41_cont_of_smooth hφ
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f := fun hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hres : ∀ x, q41_res φ e n x = φ x - Torus.mean φ -
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

lemma q41_res_mean {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    Torus.mean (q41_res φ e n) = 0 := by
  have hc : ∀ l : NonzeroLattice d, Continuous (Torus.realMode l) := fun l =>
    q41_cont_of_smooth (HRS.FieldSingAux.isSmooth_realMode l)
  have hφc := q41_cont_of_smooth hφ
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f := fun hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hres : ∀ x, q41_res φ e n x = φ x - Torus.mean φ -
      ∑ i ∈ Finset.range n, Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x := fun x => rfl
  have i3 : ∀ i ∈ Finset.range n, Integrable fun x =>
      Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x := fun i _ =>
    hint (continuous_const.mul (hc _))
  have iA : Integrable fun x => φ x - Torus.mean φ := (hint hφc).sub (integrable_const _)
  have iB : Integrable fun x => ∑ i ∈ Finset.range n,
      Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x := integrable_finsetSum _ i3
  show ∫ x, q41_res φ e n x = 0
  simp only [hres]
  rw [integral_sub iA iB, integral_sub (hint hφc) (integrable_const _), integral_finset_sum _ i3]
  simp_rw [integral_const_mul, Torus.integral_realMode]
  simp [Torus.mean]

/-- The truncation error tends to zero in every Sobolev norm. -/
lemma q41_trunc_sob {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (e : ℕ ≃ NonzeroLattice d) (m : ℝ) :
    MemSobolev m (q41_res φ e 0) ∧ (∀ n, MemSobolev m (q41_res φ e n)) ∧
      Tendsto (fun n => sobolevNorm m (q41_res φ e n)) atTop (𝓝 0) := by
  have hφm : MemSobolev m φ := MFSemigroup.memSobolev_of_isSmooth hφ m
  have hcoef := q41_res_coeff hφ e
  have hmem : ∀ n, MemSobolev m (q41_res φ e n) := by
    intro n
    refine ⟨(q41_cont_of_smooth (q41_res_smooth hφ e n)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _), ?_⟩
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hφm.2
    · exact mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
    · rw [hcoef n k]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Torus.jp_pos _).le _)
      split_ifs <;> simp <;> positivity
  refine ⟨hmem 0, hmem, ?_⟩
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2
    with hw
  have hwsum : Summable w := hφm.2
  set f : ℕ → ℝ := fun i => w (e i) with hf
  have hfsum : Summable f := (e.summable_iff.2 hwsum)
  have htsum : ∀ n, ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) *
      Torus.funRealCoeff (q41_res φ e n) k ^ 2 = ∑' i, f i - ∑ i ∈ Finset.range n, f i := by
    intro n
    have h1 : ∀ k, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff (q41_res φ e n) k ^ 2 =
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
  have hnorm : ∀ n, sobolevNorm m (q41_res φ e n) =
      Real.sqrt (∑' i, f i - ∑ i ∈ Finset.range n, f i) := by
    intro n
    unfold sobolevNorm
    rw [q41_res_mean hφ e n, htsum n]
    simp
  simp_rw [hnorm]
  have := (Real.continuous_sqrt.tendsto 0).comp hlim
  simpa [Function.comp_def] using this

/-- The truncation error tends to zero in every `C^j` norm. -/
theorem q41_trunc_cb {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (e : ℕ ≃ NonzeroLattice d) (j : ℕ) :
    Tendsto (fun n => Torus.cbNorm j (q41_res φ e n)) atTop (𝓝 0) := by
  set m : ℝ := (d : ℝ) / 2 + j + 1 with hm
  obtain ⟨C, hC⟩ := cbNorm_le_sobolevNorm (d := d) j m (by rw [hm]; linarith)
  obtain ⟨-, hmem, hlim⟩ := q41_trunc_sob hφ e m
  have hC0 : Tendsto (fun n => C * sobolevNorm m (q41_res φ e n)) atTop (𝓝 0) := by
    simpa using hlim.const_mul C
  refine squeeze_zero (fun n => cbNorm_nonneg_ps j _) (fun n => ?_) hC0
  exact hC _ (hmem n) (isCk_of_smooth_ps (q41_res_smooth hφ e n) j)

end HRS.Q41
