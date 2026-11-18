import HRS.MP.HNegInfra
import HRS.MP.KolmChentsov
import HRS.Commutator.Whole.Energy
import HRS.Commutator.Whole.LocalAuxSAMP2

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MP.RdInit
open HRS HRS.Whole HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- the tuple of coordinate unit vectors `e_{idx 1}, …, e_{idx j}` -/
def mri_e {j : ℕ} (idx : Fin j → Fin d) : Fin j → Euc d := fun l => EuclideanSpace.single (idx l) 1

theorem mri_partialDeriv_def {j : ℕ} (idx : Fin j → Fin d) (f : Euc d → ℝ) (x : Euc d) :
    partialDeriv idx f x = iteratedFDeriv ℝ j f x (mri_e idx) := rfl

theorem mri_norm_e {j : ℕ} (idx : Fin j → Fin d) (l : Fin j) : ‖mri_e idx l‖ = 1 := by
  simp [mri_e]

theorem mri_abs_partialDeriv_le {j : ℕ} (idx : Fin j → Fin d) (f : Euc d → ℝ) (x : Euc d) :
    |partialDeriv idx f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  have := (iteratedFDeriv ℝ j f x).le_opNorm (mri_e idx)
  show |iteratedFDeriv ℝ j f x (mri_e idx)| ≤ _
  simpa [mri_norm_e] using this

theorem mri_fourier_partial {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ k u) (hc : HasCompactSupport u)
    {j : ℕ} (hj : j ≤ k) (idx : Fin j → Fin d) (ξ : Euc d) :
    ‖𝓕 (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) ξ‖ =
      (2 * Real.pi) ^ j * (∏ i, |ξ (idx i)|) * ‖𝓕 (fun x => ((u x : ℝ) : ℂ)) ξ‖ := by
  set f : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with hf
  have hfC : ContDiff ℝ (k : ℕ∞) f := by
    have := Complex.ofRealCLM.contDiff.comp hu
    exact this
  have hfc : HasCompactSupport f := hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) → Integrable (iteratedFDeriv ℝ n f) volume := by
    intro n hn
    have hcn : Continuous (iteratedFDeriv ℝ n f) := by
      refine hfC.continuous_iteratedFDeriv ?_
      exact_mod_cast hn
    exact hcn.integrable_of_hasCompactSupport (hfc.iteratedFDeriv n)
  have hjk : (j : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hj
  have h1 := Real.fourier_iteratedFDeriv hfC hint hjk
  have hcomp : ∀ x, iteratedFDeriv ℝ j f x (mri_e idx) = ((partialDeriv idx u x : ℝ) : ℂ) := by
    intro x
    have : iteratedFDeriv ℝ j f x = Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ j u x) := by
      have := Complex.ofRealCLM.iteratedFDeriv_comp_left (x := x) (f := u) (n := (k : WithTop ℕ∞))
        hu.contDiffAt (i := j) (by exact_mod_cast hj)
      exact this
    rw [this]
    rfl
  have h2 : 𝓕 (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) ξ = 𝓕 (iteratedFDeriv ℝ j f) ξ (mri_e idx) := by
    have h3 := Real.fourierIntegral_continuousMultilinearMap_apply' (L := innerSL ℝ) (μ := volume)
      (hf := hint j hjk) (m := mri_e idx) (w := ξ)
    have h4 : (fun x => ((partialDeriv idx u x : ℝ) : ℂ)) = fun x => iteratedFDeriv ℝ j f x (mri_e idx) := by
      funext x; exact (hcomp x).symm
    rw [h4]
    exact h3.symm
  rw [h2, h1]
  simp only [VectorFourier.fourierPowSMulRight_apply]
  have hin : ∀ a : Fin d, innerSL ℝ ξ (EuclideanSpace.single a (1 : ℝ)) = ξ a := by
    intro a
    rw [innerSL_apply_apply, EuclideanSpace.inner_single_right]
    simp
  simp [mri_e, hin]
  ring


theorem mri_sum_idx_sq (j : ℕ) (ξ : Euc d) :
    ∑ idx : Fin j → Fin d, (∏ i, |ξ (idx i)|) ^ 2 = ‖ξ‖ ^ (2 * j) := by
  have h1 : ∀ idx : Fin j → Fin d, (∏ i, |ξ (idx i)|) ^ 2 = ∏ i, ξ (idx i) ^ 2 := by
    intro idx
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => sq_abs _
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin j => (Finset.univ : Finset (Fin d)))
    (fun _ a => ξ a ^ 2)
  rw [Fintype.piFinset_univ] at h2
  rw [← h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul,
    EuclideanSpace.norm_sq_eq]
  simp

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem mri_partial_memLp {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ k u) (hc : HasCompactSupport u)
    {j : ℕ} (hj : j ≤ k) (idx : Fin j → Fin d) :
    Continuous (partialDeriv idx u) ∧ HasCompactSupport (partialDeriv idx u) := by
  have hcont : Continuous (iteratedFDeriv ℝ j u) := hu.continuous_iteratedFDeriv (by exact_mod_cast hj)
  refine ⟨?_, ?_⟩
  · exact (continuous_eval_const (mri_e idx)).comp hcont
  · have := (hc.iteratedFDeriv j).comp_left (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ => A (mri_e idx)) (by simp)
    exact this



open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
/-- For `u ∈ C^k_c`: the `H^k` norm squared is the binomial combination of the `L²` norms of the
partial derivatives. -/
theorem mri_sobolev_deriv {k : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ k u) (hc : HasCompactSupport u) :
    HRS.PDE.ToolboxRd.MemSobolev (k : ℝ) u ∧ HRS.PDE.ToolboxRd.sobolevNormSq (k : ℝ) u =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx u x) ^ 2 := by
  have hu0 : ContDiff ℝ (0 : ℕ) u := hu.of_le (by exact_mod_cast Nat.zero_le k)
  have hL2 : MemLp u 2 volume := hu0.continuous.memLp_of_hasCompactSupport hc
  have hL1 : Integrable u volume := hu0.continuous.integrable_of_hasCompactSupport hc
  have hFu : fourierL2 u =ᵐ[volume] 𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) :=
    HRS.Commutator.Whole.energyAux_fourierL2_eq u hL1 hL2
  have hv : ∀ j ≤ k, ∀ idx : Fin j → Fin d, MemLp (partialDeriv idx u) 2 volume ∧
      Integrable (partialDeriv idx u) volume := by
    intro j hj idx
    obtain ⟨h1, h2⟩ := mri_partial_memLp hu hc hj idx
    exact ⟨h1.memLp_of_hasCompactSupport h2, h1.integrable_of_hasCompactSupport h2⟩
  have hFv : ∀ j ≤ k, ∀ idx : Fin j → Fin d, ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      ‖fourierL2 (partialDeriv idx u) ξ‖ = (2 * Real.pi) ^ j * (∏ i, |ξ (idx i)|) * ‖fourierL2 u ξ‖ := by
    intro j hj idx
    have h := HRS.Commutator.Whole.energyAux_fourierL2_eq (partialDeriv idx u) (hv j hj idx).2
      (hv j hj idx).1
    filter_upwards [h, hFu] with ξ h1 h2
    rw [h1, h2, mri_fourier_partial hu hc hj idx ξ]
  -- the integrand identities
  have hterm : ∀ j ≤ k, (∀ᵐ ξ ∂(volume : Measure (Euc d)),
      (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j * ‖fourierL2 u ξ‖ ^ 2 =
        ∑ idx : Fin j → Fin d, ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2) := by
    intro j hj
    have hall : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ idx : Fin j → Fin d,
        ‖fourierL2 (partialDeriv idx u) ξ‖ = (2 * Real.pi) ^ j * (∏ i, |ξ (idx i)|) * ‖fourierL2 u ξ‖ :=
      ae_all_iff.2 fun idx => hFv j hj idx
    filter_upwards [hall] with ξ h
    simp_rw [h]
    have : ∀ idx : Fin j → Fin d, ((2 * Real.pi) ^ j * (∏ i, |ξ (idx i)|) * ‖fourierL2 u ξ‖) ^ 2 =
        (2 * Real.pi) ^ (2 * j) * ‖fourierL2 u ξ‖ ^ 2 * (∏ i, |ξ (idx i)|) ^ 2 := by
      intro idx
      rw [show (2 * Real.pi) ^ (2 * j) = ((2 * Real.pi) ^ j) ^ 2 by ring]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, mri_sum_idx_sq]
    have h4 : (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j = (2 * Real.pi) ^ (2 * j) * ‖ξ‖ ^ (2 * j) := by
      rw [show 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 by ring, mul_pow, ← pow_mul, ← pow_mul]
    rw [h4]; ring
  have hint_term : ∀ j ≤ k, Integrable (fun ξ : Euc d => (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j * ‖fourierL2 u ξ‖ ^ 2) volume := by
    intro j hj
    have : Integrable (fun ξ : Euc d => ∑ idx : Fin j → Fin d, ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2) volume :=
      integrable_finsetSum _ fun idx _ => integrable_norm_sq_fourierL2 (hv j hj idx).1
    exact this.congr (by filter_upwards [hterm j hj] with ξ h using h.symm)
  have hbin : ∀ ξ : Euc d, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (k : ℝ) * ‖fourierL2 u ξ‖ ^ 2 =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ j * ‖fourierL2 u ξ‖ ^ 2) := by
    intro ξ
    rw [Real.rpow_natCast, add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [one_pow, mul_one]
    ring
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (k : ℝ) * ‖fourierL2 u ξ‖ ^ 2) volume := by
    simp_rw [hbin]
    exact integrable_finsetSum _ fun j hj =>
      (hint_term j (by simpa [Nat.lt_succ_iff] using hj)).const_mul _
  refine ⟨⟨hL2, hint⟩, ?_⟩
  unfold sobolevNormSq
  simp_rw [hbin]
  rw [integral_finsetSum _ fun j hj =>
    (hint_term j (by simpa [Nat.lt_succ_iff] using hj)).const_mul _]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
  rw [integral_const_mul]
  congr 1
  rw [integral_congr_ae (hterm j hjk), integral_finsetSum _ fun idx _ =>
    integrable_norm_sq_fourierL2 (hv j hjk idx).1]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [integral_norm_sq_fourierL2 (hv j hjk idx).1]



/-! ### Localization with the cutoff -/

/-- derivative bounds of the cutoff -/
theorem mri_cutoff_bound {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M := by
  obtain ⟨hsm, hcs, -, -, -⟩ := hχ
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ C := fun i =>
    (hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hcs.iteratedFDeriv i)
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (m + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i hi x => ?_⟩
  refine (hC i x).trans ?_
  refine (le_abs_self _).trans ?_
  exact Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

theorem mri_cutoff_deriv_bound {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) {M : ℝ}
    (m : ℕ) (hM : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M) (z : Euc d) {i : ℕ} (hi : i ≤ m)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ ≤ (Metric.ball z 2).indicator (fun _ => M) x := by
  rw [iteratedFDeriv_comp_sub]
  by_cases hx : x ∈ Metric.ball z 2
  · rw [Set.indicator_of_mem hx]
    exact hM i hi _
  · rw [Set.indicator_of_notMem hx]
    have : x - z ∉ tsupport χ := by
      intro h
      apply hx
      have := hχ.2.2.1 h
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [Metric.mem_ball] using this
    have hz : iteratedFDeriv ℝ i χ (x - z) = 0 := by
      by_contra hne
      exact this (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))
    rw [hz]; simp



/-- `∑_{i ≤ m} ‖D^i g(x)‖²` -/
def mriG (m : ℕ) (g : Euc d → ℝ) (x : Euc d) : ℝ := ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i g x‖ ^ 2

theorem mriG_nonneg (m : ℕ) (g : Euc d → ℝ) (x : Euc d) : 0 ≤ mriG m g x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem mriG_continuous {m : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ m g) : Continuous (mriG m g) := by
  unfold mriG
  refine continuous_finset_sum _ fun i hi => ?_
  have : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  exact (hg.continuous_iteratedFDeriv (by exact_mod_cast this)).norm.pow 2

theorem mri_leibniz_sq {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) {M : ℝ} (hM0 : 0 ≤ M)
    (m : ℕ) (hM : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M) {g : Euc d → ℝ} (hg : ContDiff ℝ m g)
    (z : Euc d) {j : ℕ} (hj : j ≤ m) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => χ (y - z) * g y) x‖ ^ 2 ≤
      (Metric.ball z 2).indicator (fun y => ((m + 1 : ℕ) : ℝ) * 4 ^ m * M ^ 2 * mriG m g y) x := by
  have hχz : ContDiff ℝ m (fun y => χ (y - z)) :=
    (hχ.1.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have hle := norm_iteratedFDeriv_mul_le hχz hg x (n := j) (by exact_mod_cast hj)
  by_cases hx : x ∈ Metric.ball z 2
  · rw [Set.indicator_of_mem hx]
    have hb : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖ ≤ (2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) g x‖ := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 := mri_cutoff_deriv_bound hχ (M := M) m hM z (hi'.trans hj) x
      rw [Set.indicator_of_mem hx] at h1
      have h2 : (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
      have : (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ ≤ 2 ^ j * M :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have h3 := hle.trans (Finset.sum_le_sum hb)
    have h4 : ‖iteratedFDeriv ℝ j (fun y => χ (y - z) * g y) x‖ ^ 2 ≤
        (∑ i ∈ Finset.range (j + 1), (2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) g x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    refine h4.trans ?_
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    rw [Finset.card_range]
    have h5 : ∑ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) g x‖) ^ 2 ≤
        4 ^ m * M ^ 2 * mriG m g x := by
      have : ∀ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) g x‖) ^ 2 =
          (4 : ℝ) ^ j * M ^ 2 * ‖iteratedFDeriv ℝ (j - i) g x‖ ^ 2 := by
        intro i _
        rw [show (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        ring
      have hrefl : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) g x‖ ^ 2 =
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i g x‖ ^ 2 := by
        have := Finset.sum_range_reflect (fun i => ‖iteratedFDeriv ℝ i g x‖ ^ 2) (j + 1)
        simpa using this
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hrefl]
      have h6 : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i g x‖ ^ 2 ≤ mriG m g x := by
        unfold mriG
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) fun i _ _ => sq_nonneg _
      have h7 : (4 : ℝ) ^ j ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hj
      exact mul_le_mul (mul_le_mul_of_nonneg_right h7 (sq_nonneg _)) h6
        (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
    have h8 : ((j + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
    exact le_trans (mul_le_mul h8 h5 (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity))
      (le_of_eq (by ring))
  · rw [Set.indicator_of_notMem hx]
    have hb : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖ ≤ 0 := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 := mri_cutoff_deriv_bound hχ (M := M) m hM z (hi'.trans hj) x
      rw [Set.indicator_of_notMem hx] at h1
      have h0 : ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ = 0 := le_antisymm h1 (norm_nonneg _)
      rw [h0]; simp
    have h3 := hle.trans (Finset.sum_nonpos hb)
    have : ‖iteratedFDeriv ℝ j (fun y => χ (y - z) * g y) x‖ = 0 := le_antisymm h3 (norm_nonneg _)
    rw [this]; simp

theorem mri_norm_le_sum {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ) :
    ‖A‖ ≤ ∑ idx : Fin j → Fin d, |A (mri_e idx)| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun m => ?_
  have hm : ∀ i, m i = ∑ a : Fin d, (m i a) • EuclideanSpace.single a (1:ℝ) := by
    intro i
    ext b
    simp [Pi.single_apply]
  have h1 : A m = ∑ r ∈ Fintype.piFinset (fun _ : Fin j => (Finset.univ : Finset (Fin d))),
      A.toMultilinearMap (fun i => (m i (r i)) • EuclideanSpace.single (r i) (1:ℝ)) := by
    conv_lhs => rw [show m = fun i => ∑ a : Fin d, (m i a) • EuclideanSpace.single a (1:ℝ) from funext hm]
    exact A.toMultilinearMap.map_sum (fun i a => (m i a) • EuclideanSpace.single a (1:ℝ))
  have h2 : ∀ r : Fin j → Fin d, A.toMultilinearMap (fun i => (m i (r i)) • EuclideanSpace.single (r i) (1:ℝ)) =
      (∏ i, m i (r i)) • A (mri_e r) := by
    intro r
    rw [MultilinearMap.map_smul_univ]
    rfl
  rw [h1]
  simp_rw [h2]
  rw [Fintype.piFinset_univ, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod, mul_comm (|A (mri_e r)|)]
  have hp : ∏ i, |(m i).ofLp (r i)| ≤ ∏ i, ‖m i‖ :=
    Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => by
      have := PiLp.norm_apply_le (m i) (r i)
      simpa using this)
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)


theorem mri_norm_sq_le {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ) :
    ‖A‖ ^ 2 ≤ (d : ℝ) ^ j * ∑ idx : Fin j → Fin d, (A (mri_e idx)) ^ 2 := by
  have h1 := mri_norm_le_sum A
  have h2 : ‖A‖ ^ 2 ≤ (∑ idx : Fin j → Fin d, |A (mri_e idx)|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h2.trans ?_
  refine (sq_sum_le_card_mul_sum_sq).trans ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  simp [sq_abs]

open HRS.MP.HNegInfra in
theorem mri_phi_add (a b : mhn_Hc d) : mhn_phi (a + b) = mhn_phi a + mhn_phi b := by
  funext x
  apply Complex.ofReal_injective
  have hint : ∀ c : mhn_Hc d, Integrable (fun v : Euc d =>
      Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • c.1 v) volume := by
    intro c
    have hc : Continuous (fun v : Euc d =>
        Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • c.1 v) := by
      have := c.2.1.continuous
      fun_prop
    refine hc.integrable_of_hasCompactSupport (c.2.2.1.mono ?_)
    exact Function.support_smul_subset_right (fun v : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I)) c.1
  rw [mhn_phi_coe, mhn_U_apply, Pi.add_apply, Complex.ofReal_add, mhn_phi_coe, mhn_phi_coe, mhn_U_apply, mhn_U_apply,
    ← integral_add (hint a) (hint b)]
  congr 1; funext v
  simp only [Submodule.coe_add, Pi.add_apply, smul_eq_mul]
  ring

open HRS.MP.HNegInfra in
theorem mri_phi_smul (c : ℝ) (a : mhn_Hc d) : mhn_phi (c • a) = c • mhn_phi a := by
  funext x
  apply Complex.ofReal_injective
  rw [mhn_phi_coe, mhn_U_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [mhn_phi_coe, mhn_U_apply, ← integral_const_mul]
  congr 1; funext v
  simp [Complex.real_smul]
  ring


open HRS.MP.HNegInfra in
theorem mri_parseval_h (Γ : ℝ) : ∃ h : ℕ → mhn_Hc d, ∀ F : HNeg d Γ,
    HasSum (fun n => (inner ℝ (mhn_rep Γ (h n)) F) ^ 2) (‖F‖ ^ 2) := by
  obtain ⟨s, hsR, hs⟩ := mhn_parseval_abstract (LinearMap.range (mhn_rep (d := d) Γ))
    (mhn_range_orth_bot Γ)
  choose h hh using fun n => hsR n
  refine ⟨h, fun F => ?_⟩
  have := hs F
  simpa [hh] using this

open HRS.MP.HNegInfra in
theorem mri_bessel (Γ : ℝ) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d Γ, HasSum (fun n => (inner ℝ (mhn_rep Γ (h n)) F) ^ 2) (‖F‖ ^ 2))
    (Λ : mhn_Hc d →ₗ[ℝ] ℝ) (C : ℝ)
    (hΛ : ∀ g, |Λ g| ≤ C * ‖mhn_rep Γ g‖) (n : ℕ) :
    ∑ l ∈ Finset.range n, (Λ (h l)) ^ 2 ≤ C ^ 2 := by
  set c : ℕ → ℝ := fun l => Λ (h l) with hc
  set S : ℝ := ∑ l ∈ Finset.range n, (c l) ^ 2 with hS
  set g : mhn_Hc d := ∑ l ∈ Finset.range n, c l • h l with hg
  set x : HNeg d Γ := mhn_rep Γ g with hx
  have hx' : x = ∑ l ∈ Finset.range n, c l • mhn_rep Γ (h l) := by
    rw [hx, hg, map_sum]
    simp [map_smul]
  have hLg : Λ g = S := by
    rw [hg, map_sum, hS]
    simp [map_smul, sq, hc]
  have h1 : ‖x‖ ^ 2 = ∑ l ∈ Finset.range n, c l * inner ℝ (mhn_rep Γ (h l)) x := by
    rw [← real_inner_self_eq_norm_sq]
    have e : inner ℝ x x = inner ℝ (∑ l ∈ Finset.range n, c l • mhn_rep Γ (h l)) x := by
      rw [← hx']
    rw [e, sum_inner]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [real_inner_smul_left]
  have h2 : ∑ l ∈ Finset.range n, (inner ℝ (mhn_rep Γ (h l)) x) ^ 2 ≤ ‖x‖ ^ 2 :=
    sum_le_hasSum _ (fun _ _ => sq_nonneg _) (hP x)
  have h3 : (‖x‖ ^ 2) ^ 2 ≤ S * ‖x‖ ^ 2 := by
    calc (‖x‖ ^ 2) ^ 2 = (∑ l ∈ Finset.range n, c l * inner ℝ (mhn_rep Γ (h l)) x) ^ 2 := by rw [← h1]
      _ ≤ (∑ l ∈ Finset.range n, (c l) ^ 2) * ∑ l ∈ Finset.range n, (inner ℝ (mhn_rep Γ (h l)) x) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ S * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h4 : ‖x‖ ^ 2 ≤ S := by
    by_cases hx0 : ‖x‖ ^ 2 = 0
    · rw [hx0]; exact hS0
    · have hpos : 0 < ‖x‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hx0)
      nlinarith
  have h5 : S ≤ C * ‖x‖ := by
    have := hΛ g
    rw [hLg] at this
    exact (le_abs_self _).trans this
  have h6 : S ^ 2 ≤ C ^ 2 * S := by
    calc S ^ 2 ≤ (C * ‖x‖) ^ 2 := pow_le_pow_left₀ hS0 h5 2
      _ = C ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ C ^ 2 * S := mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
  by_cases hS00 : S = 0
  · rw [hS00]; positivity
  · have hpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS00)
    nlinarith


open HRS.PDE.ToolboxRd in
/-- the constant of the cell bound -/
def mriKc (d m : ℕ) (M : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (d : ℝ) ^ j) * (((m + 1 : ℕ) : ℝ) * 4 ^ m * M ^ 2)

theorem mriKc_nonneg (d m : ℕ) (M : ℝ) : 0 ≤ mriKc d m M := by
  unfold mriKc; positivity

open HRS.PDE.ToolboxRd in
theorem mri_cell_bound {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) {M : ℝ} (hM0 : 0 ≤ M)
    (m : ℕ) (hM : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M) {g : Euc d → ℝ} (hg : ContDiff ℝ m g)
    (z : Euc d) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => χ (x - z) * g x) ∧
      0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => χ (x - z) * g x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => χ (x - z) * g x) ≤
        mriKc d m M * ∫ x in Metric.ball z 2, mriG m g x := by
  have hχz : ContDiff ℝ m (fun y => χ (y - z)) :=
    (hχ.1.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have hu : ContDiff ℝ m (fun y => χ (y - z) * g y) := hχz.mul hg
  have hcs : HasCompactSupport (fun y => χ (y - z)) :=
    hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
  have hc : HasCompactSupport (fun y => χ (y - z) * g y) := hcs.mul_right
  obtain ⟨hmem, hsq⟩ := mri_sobolev_deriv hu hc
  refine ⟨hmem, ?_, ?_⟩
  · rw [hsq]
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun idx _ => ?_)
    exact integral_nonneg fun x => sq_nonneg _
  rw [hsq]
  have hGint : IntegrableOn (mriG m g) (Metric.ball z 2) volume :=
    ((mriG_continuous hg).continuousOn.integrableOn_compact (isCompact_closedBall z 2)).mono_set
      Metric.ball_subset_closedBall
  set c0 : ℝ := ((m + 1 : ℕ) : ℝ) * 4 ^ m * M ^ 2 with hc0
  have hterm : ∀ j ≤ m, ∀ idx : Fin j → Fin d,
      ∫ x, (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2 ≤
        c0 * ∫ x in Metric.ball z 2, mriG m g x := by
    intro j hj idx
    obtain ⟨hcont, hcomp⟩ := mri_partial_memLp hu hc (j := j) (by exact_mod_cast hj) idx
    have hLint : Integrable (fun x => (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2) volume := by
      refine (hcont.pow 2).integrable_of_hasCompactSupport ?_
      refine hcomp.mono fun x hx => ?_
      rw [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [h0])
    have hRint : Integrable ((Metric.ball z 2).indicator (fun y => c0 * mriG m g y)) volume :=
      (integrable_indicator_iff measurableSet_ball).2 (hGint.const_mul c0)
    calc ∫ x, (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2
        ≤ ∫ x, (Metric.ball z 2).indicator (fun y => c0 * mriG m g y) x := by
          refine integral_mono hLint hRint fun x => ?_
          have h1 := mri_abs_partialDeriv_le idx (fun y => χ (y - z) * g y) x
          have h2 := mri_leibniz_sq hχ hM0 m hM hg z hj x
          calc (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2
              = |partialDeriv idx (fun y => χ (y - z) * g y) x| ^ 2 := (sq_abs _).symm
            _ ≤ ‖iteratedFDeriv ℝ j (fun y => χ (y - z) * g y) x‖ ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) h1 2
            _ ≤ _ := h2
      _ = c0 * ∫ x in Metric.ball z 2, mriG m g x := by
          rw [integral_indicator measurableSet_ball, integral_const_mul]
  calc ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2
      ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ((d : ℝ) ^ j * (c0 * ∫ x in Metric.ball z 2, mriG m g x)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2
            ≤ ∑ _idx : Fin j → Fin d, c0 * ∫ x in Metric.ball z 2, mriG m g x :=
              Finset.sum_le_sum fun idx _ => hterm j hjm idx
          _ = (d : ℝ) ^ j * (c0 * ∫ x in Metric.ball z 2, mriG m g x) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                Fintype.card_fin, nsmul_eq_mul]
              push_cast; ring
    _ = mriKc d m M * ∫ x in Metric.ball z 2, mriG m g x := by
        have e : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
            ((d : ℝ) ^ j * (c0 * ∫ x in Metric.ball z 2, mriG m g x)) =
            (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (d : ℝ) ^ j) *
              (c0 * ∫ x in Metric.ball z 2, mriG m g x) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e]
        unfold mriKc
        rw [← hc0]
        ring




theorem mri_norm_iter_sq (j : ℕ) (f : Euc d → ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ^ 2 ≤ (d : ℝ) ^ j * ∑ idx : Fin j → Fin d, (partialDeriv idx f x) ^ 2 :=
  mri_norm_sq_le (iteratedFDeriv ℝ j f x)

theorem mri_norm_iter_le (j : ℕ) (f : Euc d → ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ ∑ idx : Fin j → Fin d, |partialDeriv idx f x| :=
  mri_norm_le_sum (iteratedFDeriv ℝ j f x)

theorem mri_Y0 {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) (m : ℕ) {g : Euc d → ℝ}
    (hg : ContDiff ℝ (m + 1 : ℕ) g) (K : ℝ)
    (hK : ∀ l ≤ m + 1, ∀ (idx : Fin l → Fin d) (x : Euc d), |partialDeriv idx g x| ≤ K) :
    HRS.Whole.AppendixA.Y0Class m χ g := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 (by omega) (fun i => i.elim0) 0)
  have hnorm : ∀ i ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ (d : ℝ) ^ i * K := by
    intro i hi x
    refine (mri_norm_iter_le i g x).trans ?_
    calc ∑ idx : Fin i → Fin d, |partialDeriv idx g x| ≤ ∑ _idx : Fin i → Fin d, K :=
          Finset.sum_le_sum fun idx _ => hK i hi idx x
      _ = (d : ℝ) ^ i * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  refine ⟨?_, ⟨K, fun x => ?_⟩, ⟨(d : ℝ) * K, ?_⟩⟩
  · obtain ⟨M, hM0, hM⟩ := mri_cutoff_bound hχ m
    have hgm : ContDiff ℝ m g := hg.of_le (by exact_mod_cast Nat.le_succ m)
    set Gc : ℝ := ∑ i ∈ Finset.range (m + 1), ((d : ℝ) ^ i * K) ^ 2 with hGc
    have hG : ∀ x, mriG m g x ≤ Gc := by
      intro x
      unfold mriG
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm i (by omega) x) 2
    set V0 : ℝ := (volume (Metric.ball (0 : Euc d) 2)).toReal with hV0
    have hbound : ∀ z : Euc d, ∫ x in Metric.ball z 2, mriG m g x ≤ Gc * V0 := by
      intro z
      have hGint : IntegrableOn (mriG m g) (Metric.ball z 2) volume :=
        ((mriG_continuous hgm).continuousOn.integrableOn_compact (isCompact_closedBall z 2)).mono_set
          Metric.ball_subset_closedBall
      have hcint : IntegrableOn (fun _ : Euc d => Gc) (Metric.ball z 2) volume :=
        integrableOn_const measure_ball_lt_top.ne
      calc ∫ x in Metric.ball z 2, mriG m g x ≤ ∫ x in Metric.ball z 2, Gc :=
            setIntegral_mono_on hGint hcint measurableSet_ball fun x _ => hG x
        _ = Gc * V0 := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, Measure.addHaar_ball_center, mul_comm]
    have hlt : ∀ z : Euc d, HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - z) * g x) ≤
        ENNReal.ofReal (Real.sqrt (mriKc d m M * (Gc * V0))) := by
      intro z
      obtain ⟨hmem, -, hle⟩ := mri_cell_bound hχ hM0 m hM hgm z
      unfold HRS.Whole.sobolevNormE
      simp only [hmem, ite_true]
      refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
      exact hle.trans (mul_le_mul_of_nonneg_left (hbound z) (mriKc_nonneg d m M))
    unfold HRS.Whole.AppendixA.ulocNormE
    exact lt_of_le_of_lt (iSup_le hlt) ENNReal.ofReal_lt_top
  · have := hK 0 (by omega) (fun i => i.elim0) x
    simpa [partialDeriv, iteratedFDeriv_zero_apply] using this
  · have hdiff : Differentiable ℝ g := hg.differentiable (by simp)
    have hLip : LipschitzWith (Real.toNNReal ((d : ℝ) * K)) g := by
      refine lipschitzWith_of_nnnorm_fderiv_le hdiff fun x => ?_
      have h1 := hnorm 1 (by omega) x
      have h2 : ‖fderiv ℝ g x‖ = ‖iteratedFDeriv ℝ 1 g x‖ := by
        have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := x) (n := 0)
        rw [norm_iteratedFDeriv_zero] at this
        exact this
      rw [← NNReal.coe_le_coe, coe_nnnorm, h2, Real.coe_toNNReal _ (by positivity)]
      simpa using h1
    intro x y
    have := hLip.dist_le_mul x y
    have hc : ((Real.toNNReal ((d : ℝ) * K) : ℝ≥0) : ℝ) = (d : ℝ) * K := Real.coe_toNNReal _ (by positivity)
    rw [Real.dist_eq, dist_eq_norm, hc] at this
    exact this


theorem mri_jb_sq (x : Euc d) : jbracket x ^ 2 = 1 + ‖x‖ ^ 2 := by
  unfold jbracket; rw [Real.sq_sqrt (by positivity)]

theorem mri_jb_pos (x : Euc d) : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)

theorem mri_jb_ball (z x : Euc d) (hx : x ∈ Metric.ball z 2) : jbracket x ^ 2 ≤ 9 * jbracket z ^ 2 := by
  rw [mri_jb_sq, mri_jb_sq]
  have h1 : ‖x‖ ≤ ‖z‖ + 2 := by
    have : ‖x - z‖ < 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 2 := by linarith
  have h2 : ‖x‖ ^ 2 ≤ (‖z‖ + 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 2)]

theorem mri_jb_ge (x : Euc d) : (1 + ‖x‖) / 2 ≤ jbracket x := by
  unfold jbracket
  apply Real.le_sqrt_of_sq_le
  nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]

theorem mri_lattice_sum :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) *
      jbracket (cellPt d z) ^ 2) < ⊤ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [tsum_eq_single (default : Fin 0 → ℤ) (fun b' hb' => absurd (Subsingleton.elim b' default) hb')]
    exact ENNReal.ofReal_lt_top
  set k : ℝ := (⌈Real.sqrt d⌉ : ℝ) with hk
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1
  have hk1 : (1 : ℝ) ≤ k := by
    have := Int.le_ceil (Real.sqrt d)
    linarith
  have hkpos : 0 < k := by linarith
  set a : ℝ := k⁻¹ with ha
  have hapos : 0 < a := inv_pos.mpr hkpos
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ hk1
  have hnorm : ∀ z : Fin d → ℤ, ‖cellPt d z‖ = a * ‖latticePt z‖ := by
    intro z
    unfold cellPt
    rw [norm_smul, Real.norm_of_nonneg hapos.le]
  have hle : ∀ z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) *
      jbracket (cellPt d z) ^ 2) ≤ ENNReal.ofReal (2 ^ ((d : ℝ) + 1) * a ^ (-((d : ℝ) + 1))) *
        ENNReal.ofReal (HRS.Commutator.Whole.SAMP1.wtK d z) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hj := mri_jb_pos (cellPt d z)
    have e : jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) * jbracket (cellPt d z) ^ 2 =
        jbracket (cellPt d z) ^ (-((d : ℝ) + 1)) := by
      rw [← Real.rpow_two, ← Real.rpow_add hj]
      congr 1; ring
    rw [e]
    have hpos : 0 < (1 + ‖cellPt d z‖) / 2 := by positivity
    have hexp : -((d : ℝ) + 1) ≤ 0 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    have h1 : jbracket (cellPt d z) ^ (-((d : ℝ) + 1)) ≤ ((1 + ‖cellPt d z‖) / 2) ^ (-((d : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_nonpos hpos (mri_jb_ge _) hexp
    refine h1.trans ?_
    have hz0 : 0 ≤ ‖latticePt z‖ := norm_nonneg _
    have hlow : a * (1 + ‖latticePt z‖) ≤ 1 + ‖cellPt d z‖ := by
      rw [hnorm]; nlinarith
    have h2 : (1 + ‖cellPt d z‖) ^ (-((d : ℝ) + 1)) ≤ (a * (1 + ‖latticePt z‖)) ^ (-((d : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlow hexp
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.mul_rpow hapos.le (by positivity)] at h2
    unfold HRS.Commutator.Whole.SAMP1.wtK HRS.Commutator.Whole.SAMP1.latV
    have h3 : ‖(latticePt z : Euc d)‖ = ‖(WithLp.toLp 2 (fun i : Fin d => (z i : ℝ)) : Euc d)‖ := rfl
    rw [← h3]
    have h4 : (2 : ℝ) ^ ((d : ℝ) + 1) * a ^ (-((d : ℝ) + 1)) *
        (1 + ‖latticePt z‖) ^ (-((d : ℝ) + 1)) =
        ((2 : ℝ) ^ ((d : ℝ) + 1))  * (a ^ (-((d : ℝ) + 1)) * (1 + ‖latticePt z‖) ^ (-((d : ℝ) + 1))) := by ring
    rw [h4]
    have h5 : (1 + ‖cellPt d z‖) ^ (-((d : ℝ) + 1)) / ((2 : ℝ) ^ ((d : ℝ) + 1))⁻¹ =
        (2 : ℝ) ^ ((d : ℝ) + 1) * (1 + ‖cellPt d z‖) ^ (-((d : ℝ) + 1)) := by
      rw [div_inv_eq_mul, mul_comm]
    rw [h5]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (HRS.Commutator.Whole.SAMP1.tsum_wtK_lt_top)


theorem mri_varpi_sq (m : ℕ) (χ ψ : Euc d → ℝ) :
    HRS.Whole.AppendixA.varpiNormE m χ ψ ^ 2 = ∑' z : Fin d → ℤ,
      ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d z) * ψ x) ^ 2 := by
  unfold HRS.Whole.AppendixA.varpiNormE
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem mri_ball_sum_bound {m : ℕ} (ψ : ℕ → Euc d → ℝ) (hψ : ∀ ℓ, ContDiff ℝ m (ψ ℓ)) (B0 : ℝ)
    (hB0 : 0 ≤ B0)
    (hB : ∀ (n : ℕ) (x : Euc d), ∑ ℓ ∈ Finset.range n, mriG m (ψ ℓ) x ≤ B0 * jbracket x ^ 2)
    (p : Euc d) (n : ℕ) :
    ∑ ℓ ∈ Finset.range n, ∫ x in Metric.ball p 2, mriG m (ψ ℓ) x ≤
      9 * B0 * jbracket p ^ 2 * (volume (Metric.ball (0 : Euc d) 2)).toReal := by
  have hint : ∀ ℓ, IntegrableOn (mriG m (ψ ℓ)) (Metric.ball p 2) volume := fun ℓ =>
    ((mriG_continuous (hψ ℓ)).continuousOn.integrableOn_compact (isCompact_closedBall p 2)).mono_set
      Metric.ball_subset_closedBall
  rw [← integral_finsetSum _ (fun ℓ _ => hint ℓ)]
  have hsum : IntegrableOn (fun x => ∑ ℓ ∈ Finset.range n, mriG m (ψ ℓ) x) (Metric.ball p 2) volume :=
    integrable_finsetSum _ fun ℓ _ => hint ℓ
  have hcint : IntegrableOn (fun _ : Euc d => 9 * B0 * jbracket p ^ 2) (Metric.ball p 2) volume :=
    integrableOn_const measure_ball_lt_top.ne
  calc ∫ x in Metric.ball p 2, ∑ ℓ ∈ Finset.range n, mriG m (ψ ℓ) x
      ≤ ∫ x in Metric.ball p 2, 9 * B0 * jbracket p ^ 2 := by
        refine setIntegral_mono_on hsum hcint measurableSet_ball fun x hx => ?_
        refine (hB n x).trans ?_
        have := mri_jb_ball p x hx
        nlinarith
    _ = 9 * B0 * jbracket p ^ 2 * (volume (Metric.ball (0 : Euc d) 2)).toReal := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Measure.addHaar_ball_center, mul_comm]

theorem mri_varpi_sum {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) (m : ℕ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ψ : ℕ → Euc d → ℝ), (∀ ℓ, ContDiff ℝ m (ψ ℓ)) → ∀ B0 : ℝ, 0 ≤ B0 →
      (∀ (n : ℕ) (x : Euc d), ∑ ℓ ∈ Finset.range n, mriG m (ψ ℓ) x ≤ B0 * jbracket x ^ 2) →
      ∑' ℓ, HRS.Whole.AppendixA.varpiNormE m χ (ψ ℓ) ^ 2 ≤ ENNReal.ofReal (C0 * B0) := by
  obtain ⟨M, hM0, hM⟩ := mri_cutoff_bound hχ m
  set V0 : ℝ := (volume (Metric.ball (0 : Euc d) 2)).toReal with hV0
  set Slat : ℝ := (∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) *
      jbracket (cellPt d z) ^ 2)).toReal with hSlat
  have hV00 : 0 ≤ V0 := ENNReal.toReal_nonneg
  have hS0 : 0 ≤ Slat := ENNReal.toReal_nonneg
  refine ⟨9 * mriKc d m M * V0 * Slat, by have := mriKc_nonneg d m M; positivity, ?_⟩
  intro ψ hψ B0 hB0 hB
  have hcell : ∀ ℓ, HRS.Whole.AppendixA.varpiNormE m χ (ψ ℓ) ^ 2 ≤ ∑' z : Fin d → ℤ,
      ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (mriKc d m M * ∫ x in Metric.ball (cellPt d z) 2, mriG m (ψ ℓ) x) := by
    intro ℓ
    rw [mri_varpi_sq]
    refine ENNReal.tsum_le_tsum fun z => ?_
    refine mul_le_mul' le_rfl ?_
    obtain ⟨hmem, hnn, hle⟩ := mri_cell_bound hχ hM0 m hM (hψ ℓ) (cellPt d z)
    unfold HRS.Whole.sobolevNormE
    simp only [hmem, ite_true]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hnn]
    exact ENNReal.ofReal_le_ofReal hle
  have hinner : ∀ z : Fin d → ℤ, ∑' ℓ, ENNReal.ofReal (mriKc d m M *
      ∫ x in Metric.ball (cellPt d z) 2, mriG m (ψ ℓ) x) ≤
      ENNReal.ofReal (9 * mriKc d m M * B0 * V0 * jbracket (cellPt d z) ^ 2) := by
    intro z
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun n => ?_
    have hnn : ∀ ℓ, 0 ≤ mriKc d m M * ∫ x in Metric.ball (cellPt d z) 2, mriG m (ψ ℓ) x := fun ℓ =>
      mul_nonneg (mriKc_nonneg d m M) (integral_nonneg fun x => by
        unfold mriG; exact Finset.sum_nonneg fun i _ => sq_nonneg _)
    rw [← ENNReal.ofReal_sum_of_nonneg fun ℓ _ => hnn ℓ]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.mul_sum]
    have := mri_ball_sum_bound ψ hψ B0 hB0 hB (cellPt d z) n
    calc mriKc d m M * ∑ ℓ ∈ Finset.range n, ∫ x in Metric.ball (cellPt d z) 2, mriG m (ψ ℓ) x
        ≤ mriKc d m M * (9 * B0 * jbracket (cellPt d z) ^ 2 * V0) :=
          mul_le_mul_of_nonneg_left this (mriKc_nonneg d m M)
      _ = _ := by ring
  calc ∑' ℓ, HRS.Whole.AppendixA.varpiNormE m χ (ψ ℓ) ^ 2
      ≤ ∑' ℓ, ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (mriKc d m M * ∫ x in Metric.ball (cellPt d z) 2, mriG m (ψ ℓ) x) :=
        ENNReal.tsum_le_tsum hcell
    _ = ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ∑' ℓ, ENNReal.ofReal (mriKc d m M * ∫ x in Metric.ball (cellPt d z) 2, mriG m (ψ ℓ) x) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun z => ?_
        rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
        ENNReal.ofReal (9 * mriKc d m M * B0 * V0 * jbracket (cellPt d z) ^ 2) :=
        ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (hinner z)
    _ = ENNReal.ofReal (9 * mriKc d m M * B0 * V0) *
        ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) *
          jbracket (cellPt d z) ^ 2) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun z => ?_
        have hnn : 0 ≤ jbracket (cellPt d z) ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg (mri_jb_pos _).le _
        have hk := mriKc_nonneg d m M
        rw [← ENNReal.ofReal_mul hnn, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ = ENNReal.ofReal (9 * mriKc d m M * V0 * Slat * B0) := by
        rw [← ENNReal.ofReal_toReal (mri_lattice_sum (d := d)).ne, ← hSlat,
          ← ENNReal.ofReal_mul (by have := mriKc_nonneg d m M; positivity)]
        congr 1; ring


/-! ### The propagator family -/

theorem mri_partialDeriv_add {i : ℕ} {f g : Euc d → ℝ} (hf : ContDiff ℝ i f) (hg : ContDiff ℝ i g)
    (idx : Fin i → Fin d) (x : Euc d) :
    partialDeriv idx (f + g) x = partialDeriv idx f x + partialDeriv idx g x := by
  unfold partialDeriv
  rw [iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]
  rfl

theorem mri_partialDeriv_smul {i : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ i f) (c : ℝ)
    (idx : Fin i → Fin d) (x : Euc d) :
    partialDeriv idx (c • f) x = c * partialDeriv idx f x := by
  unfold partialDeriv
  rw [iteratedFDeriv_const_smul_apply hf.contDiffAt]
  rfl

theorem mri_partialDeriv_sub {i : ℕ} {f g : Euc d → ℝ} (hf : ContDiff ℝ i f) (hg : ContDiff ℝ i g)
    (idx : Fin i → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => f y - g y) x = partialDeriv idx f x - partialDeriv idx g x := by
  have h1 : (fun y => f y - g y) = f + (-1 : ℝ) • g := by
    funext y; simp [sub_eq_add_neg]
  have hg' : ContDiff ℝ i ((-1 : ℝ) • g) := hg.const_smul (-1 : ℝ)
  rw [h1, mri_partialDeriv_add hf hg', mri_partialDeriv_smul hg]
  ring

theorem mri_prop_add {Cf : WholeCoeff d} {T : ℝ} {Γ : ℝ} {j : ℕ} {K : ℝ}
    (hadj : AdjointInputOneD Γ j Cf T K) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {φ φ₂ : Euc d → ℝ}
    (hφ : IsSobolevTest Γ φ) (hφ₂ : IsSobolevTest Γ φ₂) :
    propagatorW Cf 0 t (φ + φ₂) = propagatorW Cf 0 t φ + propagatorW Cf 0 t φ₂ := by
  have := (hadj 0 t le_rfl ht0 htT φ hφ).2.2.1 φ₂ hφ₂ 1
  simpa using this

theorem mri_prop_smul {Cf : WholeCoeff d} {T : ℝ} {Γ : ℝ} {j : ℕ} {K : ℝ}
    (hadj : AdjointInputOneD Γ j Cf T K) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {φ : Euc d → ℝ}
    (hφ : IsSobolevTest Γ φ) (c : ℝ) :
    propagatorW Cf 0 t (c • φ) = c • propagatorW Cf 0 t φ := by
  have := (hadj 0 t le_rfl ht0 htT φ hφ).2.2.1 φ hφ (c - 1)
  have e : φ + (c - 1) • φ = c • φ := by
    funext y; simp; ring
  rw [e] at this
  rw [this]
  funext y; simp; ring

open HRS.MP.HNegInfra in
theorem mri_exists_lam {Cf : WholeCoeff d} {T : ℝ} {q j : ℕ} {K : ℝ}
    (hadj : AdjointInputOneD ((q : ℕ) : ℝ) j Cf T K) {t s' : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hs0 : 0 ≤ s') (hsT : s' ≤ T) {i : ℕ} (hi : i ≤ j) (idx : Fin i → Fin d) (x : Euc d) :
    ∃ Λ : mhn_Hc d →ₗ[ℝ] ℝ, ∀ g, Λ g = partialDeriv idx (fun y =>
      propagatorW Cf 0 t (mhn_phi g) y - propagatorW Cf 0 s' (mhn_phi g) y) x := by
  have hcd : ∀ τ : ℝ, 0 ≤ τ → τ ≤ T → ∀ g : mhn_Hc d, ContDiff ℝ i (propagatorW Cf 0 τ (mhn_phi g)) := by
    intro τ h0 h1 g
    exact ((hadj 0 τ le_rfl h0 h1 _ (mhn_isSobolevTest_phi _ g)).2.1).of_le (by exact_mod_cast hi)
  refine ⟨⟨⟨fun g => partialDeriv idx (fun y =>
      propagatorW Cf 0 t (mhn_phi g) y - propagatorW Cf 0 s' (mhn_phi g) y) x, ?_⟩, ?_⟩, fun g => rfl⟩
  · intro a b
    have e : (fun y => propagatorW Cf 0 t (mhn_phi (a + b)) y - propagatorW Cf 0 s' (mhn_phi (a + b)) y) =
        (fun y => propagatorW Cf 0 t (mhn_phi a) y - propagatorW Cf 0 s' (mhn_phi a) y) +
        (fun y => propagatorW Cf 0 t (mhn_phi b) y - propagatorW Cf 0 s' (mhn_phi b) y) := by
      rw [mri_phi_add, mri_prop_add hadj ht0 htT (mhn_isSobolevTest_phi _ a) (mhn_isSobolevTest_phi _ b),
        mri_prop_add hadj hs0 hsT (mhn_isSobolevTest_phi _ a) (mhn_isSobolevTest_phi _ b)]
      funext y; simp; ring
    show partialDeriv idx _ x = partialDeriv idx _ x + partialDeriv idx _ x
    rw [e, mri_partialDeriv_add]
    · exact (hcd t ht0 htT a).sub (hcd s' hs0 hsT a)
    · exact (hcd t ht0 htT b).sub (hcd s' hs0 hsT b)
  · intro c a
    have e : (fun y => propagatorW Cf 0 t (mhn_phi (c • a)) y - propagatorW Cf 0 s' (mhn_phi (c • a)) y) =
        c • (fun y => propagatorW Cf 0 t (mhn_phi a) y - propagatorW Cf 0 s' (mhn_phi a) y) := by
      rw [mri_phi_smul, mri_prop_smul hadj ht0 htT (mhn_isSobolevTest_phi _ a),
        mri_prop_smul hadj hs0 hsT (mhn_isSobolevTest_phi _ a)]
      funext y; simp; ring
    show partialDeriv idx _ x = c * partialDeriv idx _ x
    rw [e, mri_partialDeriv_smul]
    exact (hcd t ht0 htT a).sub (hcd s' hs0 hsT a)


theorem mri_Y0_prop {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) (m₀ : ℕ)
    {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {K : ℝ}
    (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m₀ + 1) Cf T K) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    {φ : Euc d → ℝ} (hφ : IsSobolevTest ((q : ℕ) : ℝ) φ) :
    HRS.Whole.AppendixA.Y0Class m₀ χ (propagatorW Cf 0 t φ) := by
  obtain ⟨-, hcd, -, hb⟩ := hadj 0 t le_rfl ht0 htT φ hφ
  exact mri_Y0 hχ m₀ hcd (K * HRS.Whole.sobolevNorm ((q : ℕ) : ℝ) φ) fun l hl idx x => hb l hl idx x

theorem mri_Y0_diff {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) (m₀ : ℕ)
    {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {K : ℝ}
    (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m₀ + 1) Cf T K) {s' t : ℝ} (hs0 : 0 ≤ s') (hsT : s' ≤ T)
    (ht0 : 0 ≤ t) (htT : t ≤ T)
    {φ : Euc d → ℝ} (hφ : IsSobolevTest ((q : ℕ) : ℝ) φ) :
    HRS.Whole.AppendixA.Y0Class m₀ χ (fun x => propagatorW Cf 0 t φ x - propagatorW Cf 0 s' φ x) := by
  obtain ⟨-, hcd1, -, hb1⟩ := hadj 0 t le_rfl ht0 htT φ hφ
  obtain ⟨-, hcd2, -, hb2⟩ := hadj 0 s' le_rfl hs0 hsT φ hφ
  refine mri_Y0 hχ m₀ (hcd1.sub hcd2) (2 * (K * HRS.Whole.sobolevNorm ((q : ℕ) : ℝ) φ)) fun l hl idx x => ?_
  rw [mri_partialDeriv_sub (hcd1.of_le (by exact_mod_cast hl)) (hcd2.of_le (by exact_mod_cast hl))]
  have h1 := hb1 l hl idx x
  have h2 := hb2 l hl idx x
  calc |partialDeriv idx (propagatorW Cf 0 t φ) x - partialDeriv idx (propagatorW Cf 0 s' φ) x|
      ≤ |partialDeriv idx (propagatorW Cf 0 t φ) x| + |partialDeriv idx (propagatorW Cf 0 s' φ) x| :=
        abs_sub _ _
    _ ≤ 2 * (K * HRS.Whole.sobolevNorm ((q : ℕ) : ℝ) φ) := by linarith

open HRS.MP.HNegInfra in
theorem mri_core {χ : Euc d → ℝ} (hχ : HRS.Whole.AppendixA.IsUlocCutoff χ) (m₀ : ℕ) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {K C₁ : ℝ} (h : ℕ → mhn_Hc d),
      (∀ F : HNeg d ((q : ℕ) : ℝ),
        HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2)) →
      AdjointInputOneD ((q : ℕ) : ℝ) (m₀ + 1) Cf T K → IncrementBoundRd Cf T q m₀ C₁ →
      ∀ {s' t : ℝ}, 0 ≤ s' → s' ≤ t → t ≤ T →
        ∑' ℓ, HRS.Whole.AppendixA.varpiNormE m₀ χ (fun x => propagatorW Cf 0 t (mhn_phi (h ℓ)) x -
          propagatorW Cf 0 s' (mhn_phi (h ℓ)) x) ^ 2 ≤
          ENNReal.ofReal (C2 * (C₁ ^ 2 * |t - s'| ^ 2)) := by
  obtain ⟨C0, hC0, hvs⟩ := mri_varpi_sum hχ m₀
  set Gs : ℝ := ∑ i ∈ Finset.range (m₀ + 1), ((d : ℝ) ^ i * (d : ℝ) ^ i) with hGs
  have hGs0 : 0 ≤ Gs := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨C0 * Gs, by positivity, ?_⟩
  intro Cf T q K C₁ h hP hadj hinc s' t hs0 hst htT
  have ht0 : 0 ≤ t := hs0.trans hst
  have hsT : s' ≤ T := hst.trans htT
  set B0 : ℝ := Gs * (C₁ * |t - s'|) ^ 2 with hB0
  have hB00 : 0 ≤ B0 := by positivity
  set ψ : ℕ → Euc d → ℝ := fun ℓ x => propagatorW Cf 0 t (mhn_phi (h ℓ)) x -
    propagatorW Cf 0 s' (mhn_phi (h ℓ)) x with hψ
  have hcd : ∀ ℓ, ContDiff ℝ (m₀ + 1 : ℕ) (ψ ℓ) := fun ℓ =>
    ((hadj 0 t le_rfl ht0 htT _ (mhn_isSobolevTest_phi _ (h ℓ))).2.1).sub
      ((hadj 0 s' le_rfl hs0 hsT _ (mhn_isSobolevTest_phi _ (h ℓ))).2.1)
  have hcd' : ∀ ℓ, ContDiff ℝ m₀ (ψ ℓ) := fun ℓ => (hcd ℓ).of_le (by exact_mod_cast Nat.le_succ m₀)
  -- Bessel for each coordinate functional
  have hbes : ∀ (i : ℕ), i ≤ m₀ + 1 → ∀ (idx : Fin i → Fin d) (x : Euc d) (n : ℕ),
      ∑ ℓ ∈ Finset.range n, (partialDeriv idx (ψ ℓ) x) ^ 2 ≤ (C₁ * |t - s'| * jbracket x) ^ 2 := by
    intro i hi idx x n
    obtain ⟨Λ, hΛ⟩ := mri_exists_lam hadj ht0 htT hs0 hsT hi idx x
    have := mri_bessel ((q : ℕ) : ℝ) h hP Λ (C₁ * |t - s'| * jbracket x) (fun g => by
        rw [hΛ g, mhn_norm_rep]
        exact hinc 0 s' t le_rfl hs0 hst htT (mhn_phi g) (mhn_isSobolevTest_phi _ g) i hi idx x) n
    simpa [hΛ, hψ, mhn_phi] using this
  have hB : ∀ (n : ℕ) (x : Euc d), ∑ ℓ ∈ Finset.range n, mriG m₀ (ψ ℓ) x ≤ B0 * jbracket x ^ 2 := by
    intro n x
    have hi : ∀ i ∈ Finset.range (m₀ + 1), ∑ ℓ ∈ Finset.range n, ‖iteratedFDeriv ℝ i (ψ ℓ) x‖ ^ 2 ≤
        ((d : ℝ) ^ i * (d : ℝ) ^ i) * (C₁ * |t - s'| * jbracket x) ^ 2 := by
      intro i hi
      have hi' : i ≤ m₀ + 1 := by have := Finset.mem_range.1 hi; omega
      calc ∑ ℓ ∈ Finset.range n, ‖iteratedFDeriv ℝ i (ψ ℓ) x‖ ^ 2
          ≤ ∑ ℓ ∈ Finset.range n, (d : ℝ) ^ i * ∑ idx : Fin i → Fin d, (partialDeriv idx (ψ ℓ) x) ^ 2 :=
            Finset.sum_le_sum fun ℓ _ => mri_norm_iter_sq i (ψ ℓ) x
        _ = (d : ℝ) ^ i * ∑ idx : Fin i → Fin d, ∑ ℓ ∈ Finset.range n, (partialDeriv idx (ψ ℓ) x) ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ (d : ℝ) ^ i * ∑ _idx : Fin i → Fin d, (C₁ * |t - s'| * jbracket x) ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun idx _ => hbes i hi' idx x n) (by positivity)
        _ = ((d : ℝ) ^ i * (d : ℝ) ^ i) * (C₁ * |t - s'| * jbracket x) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
    calc ∑ ℓ ∈ Finset.range n, mriG m₀ (ψ ℓ) x
        = ∑ i ∈ Finset.range (m₀ + 1), ∑ ℓ ∈ Finset.range n, ‖iteratedFDeriv ℝ i (ψ ℓ) x‖ ^ 2 := by
          unfold mriG; rw [Finset.sum_comm]
      _ ≤ ∑ i ∈ Finset.range (m₀ + 1), ((d : ℝ) ^ i * (d : ℝ) ^ i) * (C₁ * |t - s'| * jbracket x) ^ 2 :=
          Finset.sum_le_sum hi
      _ = B0 * jbracket x ^ 2 := by
          rw [← Finset.sum_mul, hB0, hGs]; ring
  refine (hvs ψ hcd' B0 hB00 hB).trans (le_of_eq ?_)
  congr 1
  rw [hB0]; ring


/-! ### Probabilistic assembly -/

open HRS.MP.HNegInfra in
theorem mri_lintegral_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Γ : ℝ} (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d Γ, HasSum (fun n => (inner ℝ (mhn_rep Γ (h n)) F) ^ 2) (‖F‖ ^ 2))
    (F : Ω → HNeg d Γ) (hF : Measurable F) :
    ∫⁻ ζ, ‖F ζ‖ₑ ^ 2 ∂P =
      ∑' ℓ, ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h ℓ)) (F ζ)) ^ 2) ∂P := by
  have hpair : ∀ ℓ ζ, HNeg.pairing (mhn_phi (h ℓ)) (F ζ) = inner ℝ (mhn_rep Γ (h ℓ)) (F ζ) :=
    fun ℓ ζ => mhn_pairing_phi Γ (h ℓ) (F ζ)
  have h1 : ∀ ζ, ‖F ζ‖ₑ ^ 2 = ∑' ℓ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h ℓ)) (F ζ)) ^ 2) := by
    intro ζ
    have hs := hP (F ζ)
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable]
    simp_rw [hpair]
  simp_rw [h1]
  rw [lintegral_tsum]
  intro ℓ
  have hm : Measurable fun ζ => HNeg.pairing (mhn_phi (h ℓ)) (F ζ) :=
    (mhn_continuous_pairing (mhn_isSobolevTest_phi Γ (h ℓ))).measurable.comp hF
  exact (ENNReal.measurable_ofReal.comp (hm.pow_const 2)).aemeasurable

theorem mri_pair_sub {μ : Measure (Euc d)} [IsFiniteMeasure μ] {f g : Euc d → ℝ}
    (hf : Continuous f) (hg : Continuous g) (Bf Bg : ℝ) (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    HRS.Whole.pair μ (fun x => f x - g x) = HRS.Whole.pair μ f - HRS.Whole.pair μ g := by
  unfold HRS.Whole.pair
  exact integral_sub (Integrable.of_bound hf.aestronglyMeasurable Bf (ae_of_all _ fun x => by
      simpa using hBf x)) (Integrable.of_bound hg.aestronglyMeasurable Bg (ae_of_all _ fun x => by
      simpa using hBg x))

theorem mri_AN_bounds (S : HRS.Whole.AppendixA.WholeMainData d) (N : ℕ) : 0 ≤ S.AN N ∧ S.AN N ≤ 1 := by
  unfold HRS.Whole.AppendixA.WholeMainData.AN Ascale
  have hκ := S.hκ N
  by_cases h0 : S.invβ N = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    unfold sigmaScale
    simp only [h0, ↓reduceIte]
    refine ⟨div_nonneg (le_min hκ.le (Real.sqrt_nonneg _)) hκ.le, ?_⟩
    rw [div_le_one hκ]
    exact min_le_left _ _

theorem mri_ofReal_V_le (m : ℕ) (χ ψ : Euc d → ℝ) :
    ENNReal.ofReal ((HRS.Whole.AppendixA.varpiNormE m χ ψ).toReal ^ 2) ≤
      HRS.Whole.AppendixA.varpiNormE m χ ψ ^ 2 := by
  by_cases h : HRS.Whole.AppendixA.varpiNormE m χ ψ = ⊤
  · rw [h]; simp
  · rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h]


theorem mri_prop_cont_bdd {Cf : WholeCoeff d} {T : ℝ} {Γ : ℝ} {j : ℕ} {K : ℝ}
    (hadj : AdjointInputOneD Γ j Cf T K) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {φ : Euc d → ℝ}
    (hφ : IsSobolevTest Γ φ) :
    Continuous (propagatorW Cf 0 t φ) ∧ ∀ x, |propagatorW Cf 0 t φ x| ≤ K * HRS.Whole.sobolevNorm Γ φ := by
  obtain ⟨-, hcd, -, hb⟩ := hadj 0 t le_rfl ht0 htT φ hφ
  refine ⟨hcd.continuous, fun x => ?_⟩
  have := hb 0 (Nat.zero_le _) (fun i => i.elim0) x
  simpa [partialDeriv, iteratedFDeriv_zero_apply] using this


open HRS.MP.HNegInfra HRS.Whole.AppendixA in
theorem mri_moment_N {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (m₀ : ℕ) (Cin C₁ : ℝ) :
    ∃ C : ℝ, ∀ (Γ : ℕ) (T Kadj : ℝ) (S : WholeMainData d), S.T = T →
      AdjointDerivInput ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj →
      (∀ N : ℕ, 1 ≤ N → IncrementBoundRd (S.coeff N) T (Γ + 2) m₀ C₁) →
      ∀ (R : ∀ N, RealizationRd d N) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Euc d → ℝ)),
        InitialFluctuationRd S R χ m₀ Cin ε Ψ →
      ∀ (Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ)),
        IsInitReprRd S R (Γ + 2) Iq Jq →
        ∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, s' ≤ t →
          ∫⁻ ζ, ‖Iq N t ζ - Iq N s' ζ‖ₑ ^ 2 ∂(R N).P + ∫⁻ ζ, ‖Jq N t ζ - Jq N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
            ENNReal.ofReal (C * |t - s'| ^ 2) := by
  obtain ⟨hC2, hcore⟩ := Classical.choose_spec (mri_core hχ m₀)
  set C2 := Classical.choose (mri_core hχ m₀) with hC2def
  refine ⟨Cin ^ 2 * (C2 * C₁ ^ 2), ?_⟩
  intro Γ T Kadj S hST hadj hinc R ε Ψ hinit Iq Jq hrepr N hN s' hs' t ht hst
  subst hST
  have hadjN : AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (S.coeff N) S.T Kadj := hadj N hN
  obtain ⟨h, hP⟩ := mri_parseval_h (d := d) ((Γ + 2 : ℕ) : ℝ)
  have hsum := hcore h hP hadjN (hinc N hN) hs'.1 hst ht.2
  have hs0 : 0 ≤ s' := hs'.1
  have hsT : s' ≤ S.T := hs'.2
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ S.T := ht.2
  have hMI : Measurable fun ζ => Iq N t ζ - Iq N s' ζ := ((hrepr.1 N hN t).1).sub (hrepr.1 N hN s').1
  have hMJ : Measurable fun ζ => Jq N t ζ - Jq N s' ζ := ((hrepr.1 N hN t).2).sub (hrepr.1 N hN s').2
  rw [mri_lintegral_sq (R N).P h hP _ hMI, mri_lintegral_sq (R N).P h hP _ hMJ, ← ENNReal.tsum_add]
  -- the termwise bound
  have hterm : ∀ ℓ, (∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h ℓ)) (Iq N t ζ - Iq N s' ζ)) ^ 2) ∂(R N).P) +
      (∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h ℓ)) (Jq N t ζ - Jq N s' ζ)) ^ 2) ∂(R N).P) ≤
      ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ (fun x => propagatorW (S.coeff N) 0 t (mhn_phi (h ℓ)) x -
        propagatorW (S.coeff N) 0 s' (mhn_phi (h ℓ)) x)).toReal ^ 2) := by
    intro ℓ
    set e := mhn_phi (h ℓ) with he
    have hte : IsSobolevTest ((Γ + 2 : ℕ) : ℝ) e := mhn_isSobolevTest_phi _ (h ℓ)
    set ψ : Euc d → ℝ := fun x => propagatorW (S.coeff N) 0 t e x - propagatorW (S.coeff N) 0 s' e x with hψ
    have hYt := mri_Y0_prop hχ m₀ hadjN ht0 htT hte
    have hYs := mri_Y0_prop hχ m₀ hadjN hs0 hsT hte
    have hYψ := mri_Y0_diff hχ m₀ hadjN hs0 hsT ht0 htT hte
    obtain ⟨hct, hbt⟩ := mri_prop_cont_bdd hadjN ht0 htT hte
    obtain ⟨hcs, hbs⟩ := mri_prop_cont_bdd hadjN hs0 hsT hte
    have : IsProbabilityMeasure S.μ0 := S.hμ0
    have hae := (hrepr.2 N hN t ht e hte).and (hrepr.2 N hN s' hs' e hte)
    have hI : ∀ᵐ ζ ∂(R N).P, HNeg.pairing e (Iq N t ζ - Iq N s' ζ) = S.AN N * (S.κ N *
        (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) ψ - HRS.Whole.pair S.μ0 ψ)) := by
      filter_upwards [hae] with ζ hζ
      obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hζ
      have hfin : IsFiniteMeasure (HRS.Whole.empirical ((R N).X₀ ζ)) := by
        unfold HRS.Whole.empirical
        have : IsFiniteMeasure (∑ i : Fin N, Measure.dirac ((R N).X₀ ζ i)) := inferInstance
        exact Measure.smul_finite _ (ENNReal.inv_ne_top.2 (by exact_mod_cast (by omega : N ≠ 0)))
      rw [mhn_pairing_sub hte, h1, h2, hψ]
      rw [mri_pair_sub hct hcs _ _ hbt hbs, mri_pair_sub hct hcs _ _ hbt hbs]
      ring
    have hJ : ∀ᵐ ζ ∂(R N).P, HNeg.pairing e (Jq N t ζ - Jq N s' ζ) = S.AN N * (R N).η ζ ψ := by
      filter_upwards [hae] with ζ hζ
      obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := hζ
      rw [mhn_pairing_sub hte, h1, h2]
      have := hinit.linear N ζ (propagatorW (S.coeff N) 0 s' e) (propagatorW (S.coeff N) 0 t e) (-1)
        hYs hYt
      have e2 : (-1 : ℝ) • propagatorW (S.coeff N) 0 s' e + propagatorW (S.coeff N) 0 t e = ψ := by
        funext x; simp [hψ]; ring
      rw [e2] at this
      rw [this]; ring
    have hAN := mri_AN_bounds S N
    have hA2 : ENNReal.ofReal (S.AN N ^ 2) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [hAN.1, hAN.2])
    have e1 : ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing e (Iq N t ζ - Iq N s' ζ)) ^ 2) ∂(R N).P =
        ENNReal.ofReal (S.AN N ^ 2) * ∫⁻ ζ, ENNReal.ofReal ((S.κ N *
          (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) ψ - HRS.Whole.pair S.μ0 ψ)) ^ 2) ∂(R N).P := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr_ae (hI.mono fun ζ hζ => ?_)
      beta_reduce
      rw [hζ, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    have e2 : ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing e (Jq N t ζ - Jq N s' ζ)) ^ 2) ∂(R N).P =
        ENNReal.ofReal (S.AN N ^ 2) * ∫⁻ ζ, ENNReal.ofReal (((R N).η ζ ψ) ^ 2) ∂(R N).P := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr_ae (hJ.mono fun ζ hζ => ?_)
      beta_reduce
      rw [hζ, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    have hI2 := hinit.I2 N hN ψ hYψ
    rw [e1, e2, ← mul_add]
    calc ENNReal.ofReal (S.AN N ^ 2) * (_ + _) ≤ 1 * ENNReal.ofReal (Cin ^ 2 *
          (varpiNormE m₀ χ ψ).toReal ^ 2) := mul_le_mul' hA2 hI2
      _ = _ := one_mul _
  calc ∑' ℓ, (∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h ℓ)) (Iq N t ζ - Iq N s' ζ)) ^ 2) ∂(R N).P +
        ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h ℓ)) (Jq N t ζ - Jq N s' ζ)) ^ 2) ∂(R N).P)
      ≤ ∑' ℓ, ENNReal.ofReal (Cin ^ 2) * varpiNormE m₀ χ (fun x =>
          propagatorW (S.coeff N) 0 t (mhn_phi (h ℓ)) x - propagatorW (S.coeff N) 0 s' (mhn_phi (h ℓ)) x) ^ 2 := by
        refine ENNReal.tsum_le_tsum fun ℓ => (hterm ℓ).trans ?_
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
        exact mul_le_mul' le_rfl (mri_ofReal_V_le _ _ _)
    _ = ENNReal.ofReal (Cin ^ 2) * ∑' ℓ, varpiNormE m₀ χ (fun x =>
          propagatorW (S.coeff N) 0 t (mhn_phi (h ℓ)) x - propagatorW (S.coeff N) 0 s' (mhn_phi (h ℓ)) x) ^ 2 :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (Cin ^ 2) * ENNReal.ofReal (C2 * (C₁ ^ 2 * |t - s'| ^ 2)) :=
        mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (Cin ^ 2 * (C2 * C₁ ^ 2) * |t - s'| ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1; ring


open HRS.MP.HNegInfra HRS.Whole.AppendixA in
/-- Lemma S.A.23 on `ℝ^d` from the increment bound (conditional form of the frozen `path_initial_modulus_rd`):
the hypothesis `PathAdjointInput` of the frozen statement is replaced by the adjoint estimates it contains
(`AdjointDerivInput`, only the `adjoint` field is used; the `weighted` field and `MeanFieldRegularityRd`,
`VHypRd`, `fd.Holds`, `MatBound`, `TransportedInitialFieldRd`, `InitialFieldDist` are not needed once the
increment bound `IncrementBoundRd` (S.A.22(ii), constant `C₁`) is a hypothesis). -/
theorem path_initial_modulus_rd_of_increment (s : ℝ) (fd : FieldDensityRd d s)
    (T Kadj Cin C₁ : ℝ) (m₀ : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.T = T →
      AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj →
      (∀ N : ℕ, 1 ≤ N → IncrementBoundRd (S.coeff N) T (fd.Gamma + 2) m₀ C₁) →
      ∀ (R : ∀ N, RealizationRd d N) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Euc d → ℝ)),
        InitialFluctuationRd S R χ m₀ Cin ε Ψ →
      ∀ (Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        IsInitReprRd S R (fd.Gamma + 2) Iq Jq →
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖Iq N t ζ - Iq N s' ζ‖ₑ ^ 2 ∂(R N).P + ∫⁻ ζ, ‖Jq N t ζ - Jq N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
            ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∃ Zc, ContVersionTight T (fun N => (R N).P) (fun N t ζ => Iq N t ζ) Zc) ∧
        (∃ Zc, ContVersionTight T (fun N => (R N).P) (fun N t ζ => Jq N t ζ) Zc) := by
  obtain ⟨C, hC⟩ := mri_moment_N hχ m₀ Cin C₁
  refine ⟨C, fun S hST hadj hinc R ε Ψ hinit Iq Jq hrepr => ?_⟩
  have hTpos : 0 < T := hST ▸ S.hT
  have hmom : ∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖Iq N t ζ - Iq N s' ζ‖ₑ ^ 2 ∂(R N).P + ∫⁻ ζ, ‖Jq N t ζ - Jq N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
        ENNReal.ofReal (C * |t - s'| ^ 2) := by
    intro N hN s' hs' t ht
    rcases le_total s' t with hst | hts
    · exact hC fd.Gamma T Kadj S hST hadj hinc R ε Ψ hinit Iq Jq hrepr N hN s' hs' t ht hst
    · have := hC fd.Gamma T Kadj S hST hadj hinc R ε Ψ hinit Iq Jq hrepr N hN t ht s' hs' hts
      simp only [enorm_sub_rev (Iq N s' _), enorm_sub_rev (Jq N s' _), abs_sub_comm s' t] at this ⊢
      exact this
  refine ⟨hmom, ?_, ?_⟩
  · obtain ⟨Zc, hZc⟩ := HRS.MP.KC.kolmogorov_modulus_tightness_proof
      (E := HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)) (Ω := fun N => (R N).Ω) T hTpos (fun N => (R N).P)
      (fun N t ζ => Iq N t ζ) (fun N hN t => (hrepr.1 N hN t).1) 2 1 C (by norm_num) (by norm_num)
      (fun N hN s' hs' t ht => by
        have h := hmom N hN s' hs' t ht
        rw [show |t - s'| ^ (1 + (1 : ℝ)) = |t - s'| ^ 2 by
          rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]]
        simp only [ENNReal.rpow_two]
        exact le_trans le_self_add h)
    exact ⟨Zc, hZc⟩
  · obtain ⟨Zc, hZc⟩ := HRS.MP.KC.kolmogorov_modulus_tightness_proof
      (E := HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)) (Ω := fun N => (R N).Ω) T hTpos (fun N => (R N).P)
      (fun N t ζ => Jq N t ζ) (fun N hN t => (hrepr.1 N hN t).2) 2 1 C (by norm_num) (by norm_num)
      (fun N hN s' hs' t ht => by
        have h := hmom N hN s' hs' t ht
        rw [show |t - s'| ^ (1 + (1 : ℝ)) = |t - s'| ^ 2 by
          rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]]
        simp only [ENNReal.rpow_two]
        exact le_trans le_add_self h)
    exact ⟨Zc, hZc⟩


open HRS.MP.HNegInfra HRS.Whole.AppendixA in
theorem mri_limit_moment {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (m₀ : ℕ) (Cin C₁ : ℝ) :
    ∃ C : ℝ, ∀ (Γ : ℕ) (T Kadj : ℝ) (S : WholeMainData d) (L : LimitCoeffsRd d), S.T = T →
      AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj →
      IncrementBoundRd (L.coeff S) T (Γ + 2) m₀ C₁ → L.A ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Ω → (Euc d → ℝ) → ℝ),
      (∀ (ψ ψ' : Euc d → ℝ) (c : ℝ), Y0Class m₀ χ ψ → Y0Class m₀ χ ψ' →
        ∀ᵐ ζ ∂P, η ζ (c • ψ + ψ') = c * η ζ ψ + η ζ ψ') →
      (∀ ψ : Euc d → ℝ, Y0Class m₀ χ ψ → ∫⁻ ζ, ENNReal.ofReal ((η ζ ψ) ^ 2) ∂P ≤
        ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ ψ).toReal ^ 2)) →
      ∀ J : ℝ → Ω → HNeg d ((Γ + 2 : ℕ) : ℝ), (∀ t, Measurable (J t)) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsSobolevTest ((Γ + 2 : ℕ) : ℝ) φ →
          ∀ᵐ ζ ∂P, HNeg.pairing φ (J t ζ) = L.A * η ζ (propagatorW (L.coeff S) 0 t φ)) →
        ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, s' ≤ t →
          ∫⁻ ζ, ‖J t ζ - J s' ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C * |t - s'| ^ 2) := by
  obtain ⟨hC2, hcore⟩ := Classical.choose_spec (mri_core hχ m₀)
  set C2 := Classical.choose (mri_core hχ m₀) with hC2def
  refine ⟨Cin ^ 2 * (C2 * C₁ ^ 2), ?_⟩
  intro Γ T Kadj S L hST hadj hinc hA1 Ω _ P _ η hlin hη J hJm hJrep s' hs' t ht hst
  subst hST
  obtain ⟨h, hP⟩ := mri_parseval_h (d := d) ((Γ + 2 : ℕ) : ℝ)
  have hsum := hcore h hP hadj hinc hs'.1 hst ht.2
  have hs0 : 0 ≤ s' := hs'.1
  have hsT : s' ≤ S.T := hs'.2
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ S.T := ht.2
  have hMJ : Measurable fun ζ => J t ζ - J s' ζ := (hJm t).sub (hJm s')
  rw [mri_lintegral_sq P h hP _ hMJ]
  have hterm : ∀ ℓ, (∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h ℓ)) (J t ζ - J s' ζ)) ^ 2) ∂P) ≤
      ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ (fun x => propagatorW (L.coeff S) 0 t (mhn_phi (h ℓ)) x -
        propagatorW (L.coeff S) 0 s' (mhn_phi (h ℓ)) x)).toReal ^ 2) := by
    intro ℓ
    set e := mhn_phi (h ℓ) with he
    have hte : IsSobolevTest ((Γ + 2 : ℕ) : ℝ) e := mhn_isSobolevTest_phi _ (h ℓ)
    set ψ : Euc d → ℝ := fun x => propagatorW (L.coeff S) 0 t e x - propagatorW (L.coeff S) 0 s' e x with hψ
    have hYt := mri_Y0_prop hχ m₀ hadj ht0 htT hte
    have hYs := mri_Y0_prop hχ m₀ hadj hs0 hsT hte
    have hYψ := mri_Y0_diff hχ m₀ hadj hs0 hsT ht0 htT hte
    have hae := (hJrep t ht e hte).and (hJrep s' hs' e hte)
    have hJ : ∀ᵐ ζ ∂P, HNeg.pairing e (J t ζ - J s' ζ) = L.A * η ζ ψ := by
      filter_upwards [hae, hlin (propagatorW (L.coeff S) 0 s' e) (propagatorW (L.coeff S) 0 t e) (-1) hYs hYt]
        with ζ hζ this
      obtain ⟨h1, h2⟩ := hζ
      rw [mhn_pairing_sub hte, h1, h2]
      have e2 : (-1 : ℝ) • propagatorW (L.coeff S) 0 s' e + propagatorW (L.coeff S) 0 t e = ψ := by
        funext x; simp [hψ]; ring
      rw [e2] at this
      rw [this]; ring
    have hA2 : ENNReal.ofReal (L.A ^ 2) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [L.hA, hA1])
    have e2 : ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing e (J t ζ - J s' ζ)) ^ 2) ∂P =
        ENNReal.ofReal (L.A ^ 2) * ∫⁻ ζ, ENNReal.ofReal ((η ζ ψ) ^ 2) ∂P := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr_ae (hJ.mono fun ζ hζ => ?_)
      beta_reduce
      rw [hζ, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [e2]
    calc ENNReal.ofReal (L.A ^ 2) * ∫⁻ ζ, ENNReal.ofReal ((η ζ ψ) ^ 2) ∂P
        ≤ 1 * ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ ψ).toReal ^ 2) :=
          mul_le_mul' hA2 (hη ψ hYψ)
      _ = _ := one_mul _
  calc ∑' ℓ, ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h ℓ)) (J t ζ - J s' ζ)) ^ 2) ∂P
      ≤ ∑' ℓ, ENNReal.ofReal (Cin ^ 2) * varpiNormE m₀ χ (fun x =>
          propagatorW (L.coeff S) 0 t (mhn_phi (h ℓ)) x - propagatorW (L.coeff S) 0 s' (mhn_phi (h ℓ)) x) ^ 2 := by
        refine ENNReal.tsum_le_tsum fun ℓ => (hterm ℓ).trans ?_
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
        exact mul_le_mul' le_rfl (mri_ofReal_V_le _ _ _)
    _ = ENNReal.ofReal (Cin ^ 2) * ∑' ℓ, varpiNormE m₀ χ (fun x =>
          propagatorW (L.coeff S) 0 t (mhn_phi (h ℓ)) x - propagatorW (L.coeff S) 0 s' (mhn_phi (h ℓ)) x) ^ 2 :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (Cin ^ 2) * ENNReal.ofReal (C2 * (C₁ ^ 2 * |t - s'| ^ 2)) :=
        mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (Cin ^ 2 * (C2 * C₁ ^ 2) * |t - s'| ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1; ring

open HRS.MP.HNegInfra HRS.Whole.AppendixA in
/-- Lemma S.A.23, the limiting transported initial field on `ℝ^d`, conditional on the increment bound for the
limiting propagator (conditional form of the repaired `StatementRepairsRd.path_initial_modulus_rd_limit'`).
`LimitPathHyp` is replaced by the adjoint estimates it contains; `MatBound`, `VHypRd`, `L.invβ ≤ νbar` are not
needed. The hypothesis `hlin` (almost-sure linearity of `η` on `Y_0`, the analogue of the `linear` field of
`InitialFluctuationRd`) is used to identify `η(U^{0,t}φ) - η(U^{0,s}φ) = η(U^{0,t}φ - U^{0,s}φ)` almost surely;
it is applied to countably many triples, one per Parseval index and fixed `(s', t)`, so the almost-sure form
suffices. The conclusion is not provable from the second-moment hypothesis alone. -/
theorem path_initial_modulus_rd_limit'_of_increment (s : ℝ) (fd : FieldDensityRd d s)
    (T Kadj Cin C₁ : ℝ) (m₀ : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.T = T → ∀ L : LimitCoeffsRd d,
      AdjointInputOneD ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj →
      IncrementBoundRd (L.coeff S) T (fd.Gamma + 2) m₀ C₁ → L.A ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Ω → (Euc d → ℝ) → ℝ),
      (∀ (ψ ψ' : Euc d → ℝ) (c : ℝ), Y0Class m₀ χ ψ → Y0Class m₀ χ ψ' →
        ∀ᵐ ζ ∂P, η ζ (c • ψ + ψ') = c * η ζ ψ + η ζ ψ') →
      (∀ ψ : Euc d → ℝ, Y0Class m₀ χ ψ → ∫⁻ ζ, ENNReal.ofReal ((η ζ ψ) ^ 2) ∂P ≤
        ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ ψ).toReal ^ 2)) →
      ∀ J : ℝ → Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ), (∀ t, Measurable (J t)) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsSobolevTest ((fd.Gamma + 2 : ℕ) : ℝ) φ →
          ∀ᵐ ζ ∂P, HNeg.pairing φ (J t ζ) = L.A * η ζ (propagatorW (L.coeff S) 0 t φ)) →
        (∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖J t ζ - J s' ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        ∃ Zc, ContVersionTight (Ω := fun _ : ℕ => Ω) T (fun _ => P) (fun _ t ζ => J t ζ) Zc := by
  obtain ⟨C, hC⟩ := mri_limit_moment hχ m₀ Cin C₁
  refine ⟨C, fun S hST L hadj hinc hA1 Ω _ P _ η hlin hη J hJm hJrep => ?_⟩
  have hTpos : 0 < T := hST ▸ S.hT
  have hmom : ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖J t ζ - J s' ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C * |t - s'| ^ 2) := by
    intro s' hs' t ht
    rcases le_total s' t with hst | hts
    · exact hC fd.Gamma T Kadj S L hST hadj hinc hA1 P η hlin hη J hJm hJrep s' hs' t ht hst
    · have := hC fd.Gamma T Kadj S L hST hadj hinc hA1 P η hlin hη J hJm hJrep t ht s' hs' hts
      simp only [enorm_sub_rev (J s' _), abs_sub_comm s' t] at this ⊢
      exact this
  refine ⟨hmom, ?_⟩
  obtain ⟨Zc, hZc⟩ := HRS.MP.KC.kolmogorov_modulus_tightness_proof
    (E := HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)) (Ω := fun _ : ℕ => Ω) T hTpos (fun _ => P)
    (fun _ t ζ => J t ζ) (fun _ _ t => hJm t) 2 1 C (by norm_num) (by norm_num)
    (fun N hN s' hs' t ht => by
      have h := hmom s' hs' t ht
      rw [show |t - s'| ^ (1 + (1 : ℝ)) = |t - s'| ^ 2 by
        rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]]
      simp only [ENNReal.rpow_two]
      exact h)
  exact ⟨Zc, hZc⟩


end HRS.MP.RdInit
