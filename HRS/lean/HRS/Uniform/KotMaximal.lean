import HRS.Uniform.KotTransform
import HRS.Uniform.KotDilation
import HRS.Prob.HilbertBDG

/-!
# Lemma 3.17, dissipative alternative: maximal inequality for discrete convolutions (packet KOTELENEZ)

For a quasi-contractive evolution `V` and a Hilbert martingale `N` with covariation, every Riemann-type convolution
`X_τ = ∑_l V(τ, s_l ∧ τ)(N_{c_l(τ)} - N_{s_l})` over a partition `s` satisfies
`E sup_τ ‖X_τ‖^p ≤ C(p,K,T) E (∫ Tr Σ)^{p/2}`, uniformly in the partition.  The proof dilates the time-ordered products of the
(rescaled) contractions `V(s_{l+1}, s_l)` (`Kot.exists_dilation_aux`), so that `X_{s_k}` is a contraction of a martingale
transform of `N` (`isHMC_stepT`), and applies the dimension-free BDG inequality to it.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS
namespace Uniform
namespace Kot

section Det

variable {Ω : Type*} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Riemann-type convolution of `N` against `V` along the partition `s`. -/
def rsProc (V : ℝ → ℝ → H →L[ℝ] H) (N : ℝ → Ω → H) (s : ℕ → ℝ) (n : ℕ) (τ : ℝ) (ω : Ω) : H :=
  ∑ l ∈ Finset.range n, V τ (min (s l) τ) (N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω)

/-- Quasi-contractivity, cocycle and normalisation of an evolution family on `[0,T]`. -/
structure EvolBound (V : ℝ → ℝ → H →L[ℝ] H) (K T : ℝ) : Prop where
  norm_le : ∀ r t, 0 ≤ r → r ≤ t → t ≤ T → ‖V t r‖ ≤ Real.exp (K * (t - r) / 2)
  comp : ∀ r t u, 0 ≤ r → r ≤ t → t ≤ u → u ≤ T → V u t * V t r = V u r
  self : ∀ t, 0 ≤ t → t ≤ T → V t t = 1

variable {V : ℝ → ℝ → H →L[ℝ] H} {N : ℝ → Ω → H} {s : ℕ → ℝ} {n : ℕ}

theorem rsProc_node (hs : Monotone s) {k : ℕ} (hk : k ≤ n) (ω : Ω) :
    rsProc V N s n (s k) ω =
      ∑ j ∈ Finset.range k, V (s k) (s j) (N (s (j + 1)) ω - N (s j) ω) := by
  unfold rsProc
  rw [← Finset.sum_range_add_sum_Ico _ hk]
  have h1 : ∑ j ∈ Finset.Ico k n, V (s k) (min (s j) (s k))
      (N (clampI (s j) (s (j + 1)) (s k)) ω - N (s j) ω) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [clampI_of_le_left (hs (Finset.mem_Ico.1 hj).1)]
    simp
  rw [h1, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j < k := Finset.mem_range.1 hj
  rw [min_eq_left (hs hjk.le), clampI_of_right_le (hs (Nat.le_succ j)) (hs hjk)]

theorem rsProc_of_le (hs : Monotone s) {τ : ℝ} (hτ : τ ≤ s 0) (ω : Ω) : rsProc V N s n τ ω = 0 := by
  unfold rsProc
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [clampI_of_le_left (hτ.trans (hs (Nat.zero_le l)))]
  simp

theorem rsProc_step {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0) {k : ℕ}
    (hk : k ≤ n) {τ : ℝ} (hkτ : s k ≤ τ) (hτT : τ ≤ T) (hafter : ∀ l, k < l → l ≤ n → τ ≤ s l)
    (ω : Ω) :
    rsProc V N s n τ ω =
      V τ (s k) (rsProc V N s n (s k) ω + if k < n then N τ ω - N (s k) ω else 0) := by
  have hnn : ∀ l, 0 ≤ s l := fun l => h0.trans (hs (Nat.zero_le l))
  rw [rsProc_node hs hk ω]
  conv_lhs => unfold rsProc
  rw [← Finset.sum_range_add_sum_Ico _ hk]
  have hfirst : ∑ l ∈ Finset.range k, V τ (min (s l) τ) (N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω) =
      V τ (s k) (∑ l ∈ Finset.range k, V (s k) (s l) (N (s (l + 1)) ω - N (s l) ω)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlk : l < k := Finset.mem_range.1 hl
    have h1 : s l ≤ s k := hs hlk.le
    have h2 : s (l + 1) ≤ s k := hs hlk
    rw [min_eq_left (h1.trans hkτ), clampI_of_right_le (hs (Nat.le_succ l)) (h2.trans hkτ)]
    have hc := hV.comp (s l) (s k) τ (hnn l) h1 hkτ hτT
    rw [← hc]
    rfl
  rw [hfirst]
  by_cases hkn : k < n
  · rw [if_pos hkn, map_add]
    congr 1
    rw [Finset.sum_eq_sum_Ico_succ_bot hkn]
    have htail : ∑ l ∈ Finset.Ico (k + 1) n, V τ (min (s l) τ)
        (N (clampI (s l) (s (l + 1)) τ) ω - N (s l) ω) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' := Finset.mem_Ico.1 hl
      rw [clampI_of_le_left (hafter l (by omega) hl'.2.le)]
      simp
    rw [htail, add_zero]
    have hτs : τ ≤ s (k + 1) := hafter (k + 1) (Nat.lt_succ_self k) hkn
    rw [min_eq_left hkτ, clampI_of_mem hkτ hτs]
  · rw [if_neg hkn, add_zero]
    have hkn' : k = n := le_antisymm hk (not_lt.1 hkn)
    subst hkn'
    simp

theorem exp_le_of_le {K T a : ℝ} (ha0 : 0 ≤ a) (haT : a ≤ T) :
    Real.exp (K * a / 2) ≤ Real.exp (|K| * T / 2) := by
  apply Real.exp_le_exp.2
  have h1 : K * a ≤ |K| * a := mul_le_mul_of_nonneg_right (le_abs_self K) ha0
  have h2 : |K| * a ≤ |K| * T := mul_le_mul_of_nonneg_left haT (abs_nonneg K)
  linarith

theorem rsProc_norm_le {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0)
    (hsn : s n ≤ T) {τ : ℝ} (hτ : τ ∈ Icc 0 T) (ω : Ω) :
    ∃ k ≤ n, ‖rsProc V N s n τ ω‖ ≤
      Real.exp (|K| * T / 2) * (‖rsProc V N s n (s k) ω‖ + ‖N τ ω - N (s k) ω‖) := by
  have hnn : ∀ l, 0 ≤ s l := fun l => h0.trans (hs (Nat.zero_le l))
  by_cases hτ0 : τ ≤ s 0
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [rsProc_of_le hs hτ0]
    simp only [norm_zero]
    positivity
  · rw [not_le] at hτ0
    set k := Nat.findGreatest (fun k => s k ≤ τ) n with hkdef
    have hk : k ≤ n := Nat.findGreatest_le n
    have hkτ : s k ≤ τ := Nat.findGreatest_spec (P := fun k => s k ≤ τ) (Nat.zero_le n) hτ0.le
    have hafter : ∀ l, k < l → l ≤ n → τ ≤ s l := fun l hl hln =>
      (not_le.1 (Nat.findGreatest_is_greatest (P := fun k => s k ≤ τ) hl hln)).le
    refine ⟨k, hk, ?_⟩
    rw [rsProc_step hV hs h0 hk hkτ hτ.2 hafter ω]
    have hsk : s k ≤ T := (hs hk).trans hsn
    have hVn : ‖V τ (s k)‖ ≤ Real.exp (|K| * T / 2) := by
      refine (hV.norm_le (s k) τ (hnn k) hkτ hτ.2).trans ?_
      refine exp_le_of_le (sub_nonneg.2 hkτ) ?_
      linarith [hnn k, hτ.2]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right hVn (norm_nonneg _)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine (norm_add_le _ _).trans ?_
    gcongr
    by_cases hkn : k < n
    · rw [if_pos hkn]
    · rw [if_neg hkn, norm_zero]; exact norm_nonneg _

/-- Rescaled one-step contractions. -/
def Cstep (V : ℝ → ℝ → H →L[ℝ] H) (K : ℝ) (s : ℕ → ℝ) (n : ℕ) (i : ℕ) : H →L[ℝ] H :=
  if i < n then Real.exp (-K * (s (i + 1) - s i) / 2) • V (s (i + 1)) (s i) else 0

/-- Rescaled time-ordered products. -/
def Pstep (V : ℝ → ℝ → H →L[ℝ] H) (K : ℝ) (s : ℕ → ℝ) (k i : ℕ) : H →L[ℝ] H :=
  Real.exp (-K * (s k - s i) / 2) • V (s k) (s i)

theorem Cstep_norm_le {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0)
    (hsn : s n ≤ T) {i : ℕ} (hi : i < n) : ‖Cstep V K s n i‖ ≤ 1 := by
  have hnn : ∀ l, 0 ≤ s l := fun l => h0.trans (hs (Nat.zero_le l))
  unfold Cstep
  rw [if_pos hi, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 := hV.norm_le (s i) (s (i + 1)) (hnn i) (hs (Nat.le_succ i)) ((hs (Nat.succ_le_of_lt hi)).trans hsn)
  calc Real.exp (-K * (s (i + 1) - s i) / 2) * ‖V (s (i + 1)) (s i)‖
      ≤ Real.exp (-K * (s (i + 1) - s i) / 2) * Real.exp (K * (s (i + 1) - s i) / 2) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; ring_nf; simp

theorem Pstep_self {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0)
    (hsn : s n ≤ T) {k : ℕ} (hk : k ≤ n) : Pstep V K s k k = 1 := by
  have hnn : 0 ≤ s k := h0.trans (hs (Nat.zero_le k))
  unfold Pstep
  rw [hV.self (s k) hnn ((hs hk).trans hsn)]
  simp

theorem Pstep_succ {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0)
    (hsn : s n ≤ T) {i k : ℕ} (hik : i < k) (hk : k ≤ n) :
    Pstep V K s k i = Pstep V K s k (i + 1) * Cstep V K s n i := by
  have hnn : ∀ l, 0 ≤ s l := fun l => h0.trans (hs (Nat.zero_le l))
  have hin : i < n := lt_of_lt_of_le hik hk
  unfold Pstep Cstep
  rw [if_pos hin, smul_mul_smul_comm, ← Real.exp_add]
  have hc := hV.comp (s i) (s (i + 1)) (s k) (hnn i) (hs (Nat.le_succ i)) (hs hik) ((hs hk).trans hsn)
  rw [hc]
  congr 2
  ring

theorem stepT_node {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℝ K'] [CompleteSpace K']
    {A : ℕ → H →L[ℝ] K'} (hs : Monotone s) {k : ℕ} (hk : k ≤ n) (ω : Ω) :
    stepT N s n A (s k) ω = ∑ j ∈ Finset.range k, A j (N (s (j + 1)) ω - N (s j) ω) := by
  unfold stepT
  rw [← Finset.sum_range_add_sum_Ico _ hk]
  have h1 : ∑ j ∈ Finset.Ico k n, A j (N (clampI (s j) (s (j + 1)) (s k)) ω - N (s j) ω) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [clampI_of_le_left (hs (Finset.mem_Ico.1 hj).1)]
    simp
  rw [h1, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j < k := Finset.mem_range.1 hj
  rw [clampI_of_right_le (hs (Nat.le_succ j)) (hs hjk)]

/-- The operators of the dilated martingale transform. -/
def Ahat (V : ℝ → ℝ → H →L[ℝ] H) (K : ℝ) (s : ℕ → ℝ) (n : ℕ) (l : ℕ) :
    H →L[ℝ] DSpace H n :=
  Real.exp (-K * s l / 2) • Bop (Cstep V K s n) (Pstep V K s) n l

theorem Ahat_norm_le {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0)
    (hsn : s n ≤ T) {l : ℕ} (hl : l < n) : ‖Ahat V K s n l‖ ≤ Real.exp (|K| * T / 2) := by
  have hnn : ∀ l, 0 ≤ s l := fun l => h0.trans (hs (Nat.zero_le l))
  obtain ⟨-, hiso, -⟩ := exists_dilation_aux (Cstep V K s n) (Pstep V K s) n
    (fun i hi => Cstep_norm_le hV hs h0 hsn hi) (fun k hk => Pstep_self hV hs h0 hsn hk)
    (fun i k hik hk => Pstep_succ hV hs h0 hsn hik hk)
  have hB : ‖Bop (Cstep V K s n) (Pstep V K s) n l‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => ?_
    rw [hiso l hl.le h, one_mul]
  unfold Ahat
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsl : s l ≤ T := (hs hl.le).trans hsn
  calc Real.exp (-K * s l / 2) * ‖Bop (Cstep V K s n) (Pstep V K s) n l‖
      ≤ Real.exp (-K * s l / 2) * 1 := mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
    _ ≤ Real.exp (|K| * T / 2) := by
        rw [mul_one]
        have := exp_le_of_le (K := -K) (hnn l) hsl
        simpa [abs_neg] using this

theorem rsProc_node_dil {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0)
    (hsn : s n ≤ T) {k : ℕ} (hk : k ≤ n) (ω : Ω) :
    ‖rsProc V N s n (s k) ω‖ ≤
      Real.exp (|K| * T / 2) * ‖stepT N s n (Ahat V K s n) (s k) ω‖ := by
  have hnn : ∀ l, 0 ≤ s l := fun l => h0.trans (hs (Nat.zero_le l))
  obtain ⟨hQB, -, hQc⟩ := exists_dilation_aux (Cstep V K s n) (Pstep V K s) n
    (fun i hi => Cstep_norm_le hV hs h0 hsn hi) (fun k hk => Pstep_self hV hs h0 hsn hk)
    (fun i k hik hk => Pstep_succ hV hs h0 hsn hik hk)
  have hQ : Qop (Cstep V K s n) (Pstep V K s) n k (stepT N s n (Ahat V K s n) (s k) ω) =
      Real.exp (-K * s k / 2) • rsProc V N s n (s k) ω := by
    rw [stepT_node hs hk, rsProc_node hs hk, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.1 hj
    unfold Ahat
    rw [ContinuousLinearMap.smul_apply, map_smul, hQB j k hjk.le hk]
    unfold Pstep
    rw [ContinuousLinearMap.smul_apply, smul_smul, ← Real.exp_add]
    congr 2
    ring
  have hX : rsProc V N s n (s k) ω =
      Real.exp (K * s k / 2) • Qop (Cstep V K s n) (Pstep V K s) n k (stepT N s n (Ahat V K s n) (s k) ω) := by
    rw [hQ, smul_smul, ← Real.exp_add]
    have : K * s k / 2 + -K * s k / 2 = 0 := by ring
    rw [this]; simp
  rw [hX, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsk : s k ≤ T := (hs hk).trans hsn
  calc Real.exp (K * s k / 2) * ‖Qop (Cstep V K s n) (Pstep V K s) n k (stepT N s n (Ahat V K s n) (s k) ω)‖
      ≤ Real.exp (|K| * T / 2) * ‖stepT N s n (Ahat V K s n) (s k) ω‖ :=
        mul_le_mul (exp_le_of_le (hnn k) hsk) (hQc k hk _) (norm_nonneg _) (Real.exp_pos _).le

theorem sup_rsProc_le {K T : ℝ} (hV : EvolBound V K T) (hs : Monotone s) (h0 : 0 ≤ s 0)
    (hsn : s n ≤ T) (ω : Ω) :
    (⨆ τ ∈ Icc 0 T, ‖rsProc V N s n τ ω‖ₑ) ≤
      ENNReal.ofReal (Real.exp (|K| * T / 2)) *
        (ENNReal.ofReal (Real.exp (|K| * T / 2)) *
            (⨆ σ ∈ Icc 0 T, ‖stepT N s n (Ahat V K s n) σ ω‖ₑ) +
          2 * ⨆ σ ∈ Icc 0 T, ‖N σ ω‖ₑ) := by
  have hnn : ∀ l, 0 ≤ s l := fun l => h0.trans (hs (Nat.zero_le l))
  set E := Real.exp (|K| * T / 2) with hE
  set S1 := ⨆ σ ∈ Icc 0 T, ‖stepT N s n (Ahat V K s n) σ ω‖ₑ with hS1
  set S2 := ⨆ σ ∈ Icc 0 T, ‖N σ ω‖ₑ with hS2
  refine iSup₂_le fun τ hτ => ?_
  obtain ⟨k, hk, hbd⟩ := rsProc_norm_le (N := N) hV hs h0 hsn hτ ω
  have hsk : s k ∈ Icc 0 T := ⟨hnn k, (hs hk).trans hsn⟩
  have h1 : ‖rsProc V N s n τ ω‖ₑ ≤ ENNReal.ofReal E *
      (‖rsProc V N s n (s k) ω‖ₑ + ‖N τ ω - N (s k) ω‖ₑ) := by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hbd
  have h2 : ‖rsProc V N s n (s k) ω‖ₑ ≤ ENNReal.ofReal E * S1 := by
    have := rsProc_node_dil (N := N) hV hs h0 hsn hk ω
    calc ‖rsProc V N s n (s k) ω‖ₑ ≤ ENNReal.ofReal E *
          ‖stepT N s n (Ahat V K s n) (s k) ω‖ₑ := by
          rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          exact ENNReal.ofReal_le_ofReal this
      _ ≤ ENNReal.ofReal E * S1 := by
          gcongr
          exact le_iSup₂ (f := fun σ (_ : σ ∈ Icc 0 T) => ‖stepT N s n (Ahat V K s n) σ ω‖ₑ) (s k) hsk
  have h3 : ‖N τ ω - N (s k) ω‖ₑ ≤ 2 * S2 := by
    calc ‖N τ ω - N (s k) ω‖ₑ ≤ ‖N τ ω‖ₑ + ‖N (s k) ω‖ₑ := enorm_sub_le
      _ ≤ S2 + S2 := by
          gcongr
          · exact le_iSup₂ (f := fun σ (_ : σ ∈ Icc 0 T) => ‖N σ ω‖ₑ) τ hτ
          · exact le_iSup₂ (f := fun σ (_ : σ ∈ Icc 0 T) => ‖N σ ω‖ₑ) (s k) hsk
      _ = 2 * S2 := by rw [two_mul]
  calc ‖rsProc V N s n τ ω‖ₑ ≤ ENNReal.ofReal E * (‖rsProc V N s n (s k) ω‖ₑ + ‖N τ ω - N (s k) ω‖ₑ) := h1
    _ ≤ ENNReal.ofReal E * (ENNReal.ofReal E * S1 + 2 * S2) := by gcongr

end Det

section Util

/-- Rational points of `[0,T]`. -/
def ratSet (T : ℝ) : Set ℝ := Icc 0 T ∩ range ((↑) : ℚ → ℝ)

theorem countable_ratSet (T : ℝ) : (ratSet T).Countable :=
  (countable_range _).mono inter_subset_right

theorem Icc_subset_closure_ratSet {T : ℝ} (hT : 0 ≤ T) : Icc 0 T ⊆ closure (ratSet T) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    exact subset_closure ⟨⟨le_rfl, hT⟩, (0 : ℚ), by simp⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (t - ε) < t from max_lt hpos (by linarith))
    refine ⟨q, ⟨⟨(le_max_left _ _).trans hq1.le, hq2.le.trans ht.2⟩, q, rfl⟩, ?_⟩
    have hq3 : t - ε < q := (le_max_right _ _).trans_lt hq1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

theorem iSup_Icc_le_iSup_ratSet {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) :
    (⨆ t ∈ Icc 0 T, ‖f t‖ₑ) ≤ ⨆ q ∈ ratSet T, ‖f q‖ₑ := by
  set c := ⨆ q ∈ ratSet T, ‖f q‖ₑ with hc
  set g : ℝ → E := fun t => f (clampI 0 T t) with hg
  have hgc : Continuous g := hf.comp_continuous (continuous_clampI 0 T) (fun t => clampI_mem hT t)
  have hclosed : IsClosed {x | ‖g x‖ₑ ≤ c} := isClosed_le (continuous_enorm.comp hgc) continuous_const
  have hsub : ratSet T ⊆ {x | ‖g x‖ₑ ≤ c} := by
    intro q hq
    have : g q = f q := by simp only [hg]; rw [clampI_of_mem hq.1.1 hq.1.2]
    show ‖g q‖ₑ ≤ c
    rw [this]
    exact le_iSup₂ (f := fun q (_ : q ∈ ratSet T) => ‖f q‖ₑ) q hq
  refine iSup₂_le fun t ht => ?_
  have h1 : t ∈ closure (ratSet T) := Icc_subset_closure_ratSet hT ht
  have h2 := closure_minimal hsub hclosed h1
  have : g t = f t := by simp only [hg]; rw [clampI_of_mem ht.1 ht.2]
  rw [← this]
  exact h2

end Util

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {K' : Type} [NormedAddCommGroup K'] [InnerProductSpace ℝ K'] [CompleteSpace K']
  [MeasurableSpace K'] [BorelSpace K'] [SecondCountableTopology K']

theorem aemeasurable_sup_rat {G : Type} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {T : ℝ} {X : ℝ → Ω → G} (hX : ∀ q ∈ ratSet T, AEMeasurable (X q) P) :
    AEMeasurable (fun ω => ⨆ q ∈ ratSet T, ‖X q ω‖ₑ) P :=
  AEMeasurable.biSup (ratSet T) (countable_ratSet T) fun q hq => (hX q hq).enorm

/-- The pathwise sup over `[0,T]` is bounded by the countable sup (a.e.), by a.e. continuity. -/
theorem ae_sup_le_sup_rat {T : ℝ} (hT : 0 ≤ T) {G : Type} [NormedAddCommGroup G] {X : ℝ → Ω → G}
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Icc 0 T)) :
    ∀ᵐ ω ∂P, (⨆ t ∈ Icc 0 T, ‖X t ω‖ₑ) ≤ ⨆ q ∈ ratSet T, ‖X q ω‖ₑ := by
  filter_upwards [hc] with ω hω
  exact iSup_Icc_le_iSup_ratSet hT hω

theorem lintegral_stepSg_le {T : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ} (hs : Monotone s) {n : ℕ}
    (A : ℕ → H →L[ℝ] K') {cA : ℝ} (hA : ∀ l < n, ‖A l‖ ≤ cA) :
    ∀ᵐ ω ∂P, ∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (stepSg Sg s n A r ω)) ≤
      ENNReal.ofReal (cA ^ 2) * ∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω)) := by
  filter_upwards [pathint_stepSg hM hs A hA] with ω hω
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hω.2 r hr)

theorem lintegral_rpow_stepSg_le {T : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {s : ℕ → ℝ} (hs : Monotone s) {n : ℕ}
    (A : ℕ → H →L[ℝ] K') {cA : ℝ} (hA : ∀ l < n, ‖A l‖ ≤ cA) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (stepSg Sg s n A r ω))) ^ p ∂P ≤
      ENNReal.ofReal (cA ^ 2) ^ p *
        ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ p ∂P := by
  rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)]
  refine lintegral_mono_ae ?_
  filter_upwards [lintegral_stepSg_le hM hs A hA] with ω hω
  calc (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (stepSg Sg s n A r ω))) ^ p
      ≤ (ENNReal.ofReal (cA ^ 2) * ∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ p :=
        ENNReal.rpow_le_rpow hω hp
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ hp

/-- The constant of the maximal inequality. -/
def CD (p K T : ℝ) : ℝ :=
  Real.exp (|K| * T / 2) ^ p * 2 ^ (p - 1) *
    (Real.exp (|K| * T / 2) ^ p * (HilbertBDG.bdgConst p * (Real.exp (|K| * T / 2) ^ 2) ^ (p / 2)) +
      2 ^ p * HilbertBDG.bdgConst p)

theorem CD_nonneg (p K T : ℝ) : 0 ≤ CD p K T := by
  unfold CD
  have := HilbertBDG.bdgConst_nonneg p
  positivity

variable {V : ℝ → ℝ → H →L[ℝ] H} {N : ℝ → Ω → H} {s : ℕ → ℝ} {n : ℕ} {T K : ℝ}
  {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}

/-- **Maximal inequality for discrete stochastic convolutions** (Kotelenez), uniform in the partition. -/
theorem maximal_rs (hcomp : IsCompleteFiltration P ℱ)
    (hN : IsHilbertMartingaleWithCovariation P ℱ T N Sg) (hV : EvolBound V K T) (hs : Monotone s)
    (h0 : 0 ≤ s 0) (hsn : s n ≤ T) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, (⨆ τ ∈ Icc 0 T, ‖rsProc V N s n τ ω‖ₑ) ^ p ∂P ≤
      ENNReal.ofReal (CD p K T) *
        ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P := by
  have hp0 : 0 < p := by linarith
  have hT : 0 ≤ T := h0.trans ((hs (Nat.zero_le n)).trans hsn)
  set E := Real.exp (|K| * T / 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set R := ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P with hR
  have hNh := isHMC_stepT hcomp hN hs h0 hsn (Ahat V K s n) (cA := E)
    (fun l hl => Ahat_norm_le hV hs h0 hsn hl)
  -- BDG for the dilated martingale and for `N`
  have hb1 := HilbertBDG.hilbert_bdg_aux hNh hp0
  have hb2 := HilbertBDG.hilbert_bdg_aux hN hp0
  have hR1 := lintegral_rpow_stepSg_le hN hs (Ahat V K s n) (cA := E)
    (fun l hl => Ahat_norm_le hV hs h0 hsn hl) (p := p / 2) (by positivity)
  set S1 : Ω → ℝ≥0∞ := fun ω => ⨆ σ ∈ Icc 0 T, ‖stepT N s n (Ahat V K s n) σ ω‖ₑ with hS1
  set S2 : Ω → ℝ≥0∞ := fun ω => ⨆ σ ∈ Icc 0 T, ‖N σ ω‖ₑ with hS2
  set S1' : Ω → ℝ≥0∞ := fun ω => ⨆ q ∈ ratSet T, ‖stepT N s n (Ahat V K s n) q ω‖ₑ with hS1'
  set S2' : Ω → ℝ≥0∞ := fun ω => ⨆ q ∈ ratSet T, ‖N q ω‖ₑ with hS2'
  have hS1ae : ∀ᵐ ω ∂P, S1 ω ≤ S1' ω := ae_sup_le_sup_rat hT hNh.cont
  have hS2ae : ∀ᵐ ω ∂P, S2 ω ≤ S2' ω := ae_sup_le_sup_rat hT hN.cont
  have hS1m : AEMeasurable S1' P := aemeasurable_sup_rat fun q hq =>
    (hNh.sq_int q ⟨hq.1.1, hq.1.2⟩).aestronglyMeasurable.aemeasurable
  have hS2m : AEMeasurable S2' P := aemeasurable_sup_rat fun q hq =>
    (hN.sq_int q ⟨hq.1.1, hq.1.2⟩).aestronglyMeasurable.aemeasurable
  have hS1le : ∀ ω, S1' ω ≤ S1 ω := fun ω =>
    iSup₂_le fun q hq => le_iSup₂ (f := fun σ (_ : σ ∈ Icc 0 T) => ‖stepT N s n (Ahat V K s n) σ ω‖ₑ) q hq.1
  have hS2le : ∀ ω, S2' ω ≤ S2 ω := fun ω =>
    iSup₂_le fun q hq => le_iSup₂ (f := fun σ (_ : σ ∈ Icc 0 T) => ‖N σ ω‖ₑ) q hq.1
  have hpt : ∀ᵐ ω ∂P, (⨆ τ ∈ Icc 0 T, ‖rsProc V N s n τ ω‖ₑ) ≤
      ENNReal.ofReal E * (ENNReal.ofReal E * S1' ω + 2 * S2' ω) := by
    filter_upwards [hS1ae, hS2ae] with ω h1 h2
    refine (sup_rsProc_le hV hs h0 hsn ω).trans ?_
    gcongr
  set A := ENNReal.ofReal E with hA
  set Cb := ENNReal.ofReal (HilbertBDG.bdgConst p) with hCb
  have hAp : A ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have h2p : (2 : ℝ≥0∞) ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le (by norm_num)
  -- the two BDG terms
  have hT1 : ∫⁻ ω, S1' ω ^ p ∂P ≤ Cb * (ENNReal.ofReal (E ^ 2) ^ (p / 2) * R) := by
    calc ∫⁻ ω, S1' ω ^ p ∂P ≤ ∫⁻ ω, S1 ω ^ p ∂P :=
          lintegral_mono fun ω => ENNReal.rpow_le_rpow (hS1le ω) hp0.le
      _ ≤ Cb * ∫⁻ ω, (∫⁻ r in Icc 0 T, ENNReal.ofReal
            (traceNormForm (stepSg Sg s n (Ahat V K s n) r ω))) ^ (p / 2) ∂P := hb1
      _ ≤ Cb * (ENNReal.ofReal (E ^ 2) ^ (p / 2) * R) := by gcongr
  have hT2 : ∫⁻ ω, S2' ω ^ p ∂P ≤ Cb * R := by
    calc ∫⁻ ω, S2' ω ^ p ∂P ≤ ∫⁻ ω, S2 ω ^ p ∂P :=
          lintegral_mono fun ω => ENNReal.rpow_le_rpow (hS2le ω) hp0.le
      _ ≤ Cb * R := hb2
  have hmeasA : AEMeasurable (fun ω => (A * S1' ω) ^ p) P :=
    (hS1m.const_mul A).pow_const p
  calc ∫⁻ ω, (⨆ τ ∈ Icc 0 T, ‖rsProc V N s n τ ω‖ₑ) ^ p ∂P
      ≤ ∫⁻ ω, (A * (A * S1' ω + 2 * S2' ω)) ^ p ∂P :=
        lintegral_mono_ae (hpt.mono fun ω hω => ENNReal.rpow_le_rpow hω hp0.le)
    _ = A ^ p * ∫⁻ ω, (A * S1' ω + 2 * S2' ω) ^ p ∂P := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        exact lintegral_const_mul' _ _ hAp
    _ ≤ A ^ p * ∫⁻ ω, (2 : ℝ≥0∞) ^ (p - 1) * ((A * S1' ω) ^ p + (2 * S2' ω) ^ p) ∂P := by
        gcongr with ω
        exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ = A ^ p * ((2 : ℝ≥0∞) ^ (p - 1) * (∫⁻ ω, (A * S1' ω) ^ p ∂P + ∫⁻ ω, (2 * S2' ω) ^ p ∂P)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
          lintegral_add_left' hmeasA]
    _ = A ^ p * ((2 : ℝ≥0∞) ^ (p - 1) * (A ^ p * ∫⁻ ω, S1' ω ^ p ∂P + 2 ^ p * ∫⁻ ω, S2' ω ^ p ∂P)) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rw [lintegral_const_mul' _ _ hAp, lintegral_const_mul' _ _ h2p]
    _ ≤ A ^ p * ((2 : ℝ≥0∞) ^ (p - 1) * (A ^ p * (Cb * (ENNReal.ofReal (E ^ 2) ^ (p / 2) * R)) +
          2 ^ p * (Cb * R))) := by gcongr
    _ = ENNReal.ofReal (CD p K T) * R := by
        have hc : ENNReal.ofReal (CD p K T) = A ^ p * ((2 : ℝ≥0∞) ^ (p - 1) *
            (A ^ p * (Cb * ENNReal.ofReal (E ^ 2) ^ (p / 2)) + 2 ^ p * Cb)) := by
          have hb0 := HilbertBDG.bdgConst_nonneg p
          have e2 : ∀ q : ℝ, 0 ≤ q → (2 : ℝ≥0∞) ^ q = ENNReal.ofReal ((2 : ℝ) ^ q) := fun q hq => by
            rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hq]; simp
          have eA : ∀ q : ℝ, 0 ≤ q → A ^ q = ENNReal.ofReal (E ^ q) := fun q hq => by
            rw [hA, ENNReal.ofReal_rpow_of_nonneg hE0.le hq]
          have eE2 : ENNReal.ofReal (E ^ 2) ^ (p / 2) = ENNReal.ofReal ((E ^ 2) ^ (p / 2)) :=
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)
          rw [eA p hp0.le, e2 (p - 1) (by linarith), e2 p hp0.le, eE2, hCb]
          unfold CD
          rw [← hE]
          have h1 : 0 ≤ E ^ p := by positivity
          have h2 : 0 ≤ (2 : ℝ) ^ (p - 1) := by positivity
          have h3 : 0 ≤ (E ^ 2) ^ (p / 2) := by positivity
          have h4 : 0 ≤ (2 : ℝ) ^ p := by positivity
          rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h4,
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul h2,
            ← ENNReal.ofReal_mul h1]
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          rw [mul_assoc, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h1]
        rw [hc]
        ring

end Prob

end Kot
end Uniform
end HRS
