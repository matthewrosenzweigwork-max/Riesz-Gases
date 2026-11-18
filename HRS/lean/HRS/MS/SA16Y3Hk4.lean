import HRS.MS.SA16Y3Hk3
import HRS.MS.SA16Y3L2a
import HRS.MS.SA16Y3Sk4
import HRS.MS.SA16Y3Mem2

/-!
# S.A.16 (SA16Y3) Hk4: the level-`j` pairing of the skew operator at `p = 2` (packet P7, Hilbert corner)

`sa16y3_Q_half_Cb`: `|∫ w Q^i(a w)| ≤ K0 Λ ∫ w²` for `|a| ≤ Λ`, `‖∇a‖ ≤ Λ`.
`sa16y3_PA_pd`: `∂^idx(P^A_μ φ) = -∑ A_{ji} (Q^i(∂_jμ ∂^idxφ) + R_j)`.
`sa16y3_hilbert_term`: `|∫ ∂^idxφ ∂^idx(P^A_μφ)| ≤ C AB Λ ∑_{k ≤ j} ‖|D^kφ|‖_2²`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hk4
variable {d : ℕ} {s : ℝ}

lemma sa16y3_kk_le (hs0 : 0 ≤ s) {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (z : Euc d) :
    sa16y3_kk s B L z ≤ (B + L) * sa16y3_kk s 1 1 z := by
  have hc := HRS.CZ.Hls.hlsg_c_nonneg hs0
  have hX : 0 ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s) := by positivity
  have hY : 0 ≤ HRS.CZ.Hls.hlsg_c s * 2 * (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1)) := by positivity
  unfold sa16y3_kk
  have e1 : HRS.CZ.Hls.hlsg_c s * L * ‖z‖ ^ (-s) = L * (HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s)) := by ring
  have e2 : HRS.CZ.Hls.hlsg_c s * (2 * B) * (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1)) =
      B * (HRS.CZ.Hls.hlsg_c s * 2 * (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1))) := by ring
  have e3 : HRS.CZ.Hls.hlsg_c s * 1 * ‖z‖ ^ (-s) = HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s) := by ring
  have e4 : HRS.CZ.Hls.hlsg_c s * (2 * 1) * (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1)) =
      HRS.CZ.Hls.hlsg_c s * 2 * (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1)) := by ring
  by_cases hz : z ∈ ball (0 : Euc d) 1
  · simp only [indicator_of_mem hz]
    rw [e1, e2, e3, e4]
    nlinarith [mul_nonneg hB hY, mul_nonneg hL hX, mul_nonneg hL hY, mul_nonneg hB hX]
  · simp only [indicator_of_notMem hz]
    rw [e2, e4]
    nlinarith [mul_nonneg hB hY, mul_nonneg hL hY]

lemma sa16y3_kk_int_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : (d : ℝ) < s + 1) {B L : ℝ} (hB : 0 ≤ B)
    (hL : 0 ≤ L) :
    ∫ z : Euc d, sa16y3_kk s B L z ≤ (B + L) * ∫ z : Euc d, sa16y3_kk s 1 1 z := by
  rw [← integral_const_mul]
  exact integral_mono (sa16y3_kk_integrable hd hs0 hsd hθ B L)
    ((sa16y3_kk_integrable hd hs0 hsd hθ 1 1).const_mul _) fun z => sa16y3_kk_le hs0 hB hL z

theorem sa16y3_Q_half_Cb (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : (d : ℝ) < s + 1) {a w : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : IsCcInfty w) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hB : ∀ y, |a y| ≤ Λ)
    (hL : ∀ y, ‖fderiv ℝ a y‖ ≤ Λ) (i : Fin d) :
    |∫ x, w x * sa16y3_Q s i (fun y => a y * w y) x| ≤
      (∫ z : Euc d, sa16y3_kk s 1 1 z) * Λ * ∫ x, w x ^ 2 := by
  refine (sa16y3_Q_half hd hs0 hsd hθ ha hw hΛ hΛ hB hL i).trans ?_
  have h1 := sa16y3_kk_int_le hd hs0 hsd hθ hΛ hΛ (s := s) (d := d)
  have h2 : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

lemma sa16y3_PA_pd (hs0 : 0 ≤ s) (hsd : s < d) {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = -A)
    {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) {j : ℕ} (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (sa16y3_PA s A μ φ) x = -∑ i : Fin d, ∑ j' : Fin d, A j' i *
      (sa16y3_Q s i (fun y => sa16z_dm μ j' y * partialDeriv idx φ y) x +
        sa16y3_R s i (sa16z_dm μ j') φ j idx x) := by
  have hfun : sa16y3_PA s A μ φ = fun y => (-1 : ℝ) * ∑ i : Fin d, ∑ j' : Fin d,
      A j' i * sa16y3_Q s i (fun z => sa16z_dm μ j' z * φ z) y := by
    funext y
    rw [sa16y3_PA_skew hs0 hsd hA hμ hφ y]; ring
  have hQs : ∀ i j' : Fin d, ContDiff ℝ ∞ (sa16y3_Q s i (fun z => sa16z_dm μ j' z * φ z)) := fun i j' =>
    sa16y3_Q_smooth hs0 hsd (sa16y3_dm_mul_cc hμ hφ j') i
  have hS1 : ∀ i : Fin d, ContDiff ℝ ∞ (fun y => ∑ j' : Fin d,
      A j' i * sa16y3_Q s i (fun z => sa16z_dm μ j' z * φ z) y) := fun i =>
    ContDiff.sum fun j' _ => contDiff_const.mul (hQs i j')
  rw [hfun, sa16sy_pd_cmul (ContDiff.sum fun i _ => hS1 i) (-1)]
  rw [sa16sy_pd_sum _ (fun i _ => hS1 i)]
  simp only [neg_mul, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sa16sy_pd_sum _ (fun j' _ => contDiff_const.mul (hQs i j'))]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [sa16sy_pd_cmul (hQs i j')]
  congr 1
  unfold sa16y3_R
  ring

lemma sa16y3_memLp2_cc {f : Euc d → ℝ} (hf : IsCcInfty f) : MemLp f (ENNReal.ofReal 2) volume :=
  hf.1.continuous.memLp_of_hasCompactSupport hf.2

lemma sa16y3_N2_mono {f g : Euc d → ℝ} (hf : AEStronglyMeasurable f volume)
    (hg : MemLp g (ENNReal.ofReal 2) volume) (h : ∀ x, |f x| ≤ |g x|) :
    sa16y3_N2 f volume ≤ sa16y3_N2 g volume := by
  unfold sa16y3_N2
  exact ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono hf (fun x => by simpa [Real.norm_eq_abs] using h x))

/-- `‖|D^kφ|‖_{L²}` as a real number -/
def sa16y3_ee (φ : Euc d → ℝ) (k : ℕ) : ℝ := sa16y3_N2 (sa16sz_vn φ k) volume

theorem sa16y3_hilbert_term (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : Matrix (Fin d) (Fin d) ℝ}, A.transpose = -A → ∀ {AB : ℝ}, 0 ≤ AB →
      (∀ a b, |A a b| ≤ AB) → ∀ {μ φ : Euc d → ℝ}, ContDiff ℝ ∞ μ → IsCcInfty φ → ∀ {Λ : ℝ}, 0 ≤ Λ →
      sa16z_Cb (j + 2) Λ μ → ∀ idx : Fin j → Fin d,
      |∫ x, partialDeriv idx φ x * partialDeriv idx (sa16y3_PA s A μ φ) x| ≤
        C * AB * Λ * ∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k ^ 2 := by
  have hθ : (d : ℝ) < s + 1 := by linarith
  haveI : Fact ((2 : ℝ) ≤ 2) := ⟨le_rfl⟩
  choose KR hKR0 hKR using fun i : Fin d => sa16y3_R_bound (s := s) hd hs0 hsd hθ1 (p := 2) (by norm_num) i j
  set K0 : ℝ := ∫ z : Euc d, sa16y3_kk s 1 1 z with hK0def
  have hK0 : 0 ≤ K0 := integral_nonneg fun z => sa16y3_kk_nonneg hs0 zero_le_one zero_le_one z
  refine ⟨(d : ℝ) ^ 2 * K0 + (d : ℝ) * (j + 1) * ∑ i : Fin d, KR i,
    add_nonneg (by positivity) (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hKR0 i)), ?_⟩
  intro A hA AB hAB hAab μ φ hμ hφ Λ hΛ hCb idx
  have hwcc : IsCcInfty (partialDeriv idx φ) := sa16s_cc_partialDeriv hφ idx
  set E : ℝ := ∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k ^ 2 with hE
  have he0 : ∀ k, 0 ≤ sa16y3_ee φ k := fun k => sa16y3_N2_nonneg _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hvnMem : ∀ k, MemLp (sa16sz_vn φ k) (ENNReal.ofReal 2) volume := fun k =>
    (sa16sz_vn_cont φ hφ.1 k).memLp_of_hasCompactSupport (sa16sz_vn_cs hφ k)
  have hjmem : j ∈ Finset.range (j + 1) := Finset.mem_range.2 (Nat.lt_succ_self j)
  have hwj : sa16y3_N2 (partialDeriv idx φ) volume ≤ sa16y3_ee φ j :=
    sa16y3_N2_mono hwcc.1.continuous.aestronglyMeasurable (hvnMem j) (fun x => by
      rw [abs_of_nonneg (sa16sz_vn_nonneg φ j x)]; exact sa16sz_abs_le_vn φ j idx x)
  have hej : sa16y3_ee φ j ≤ ∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k :=
    Finset.single_le_sum (f := fun k => sa16y3_ee φ k) (fun k _ => he0 k) hjmem
  have hw2 : ∫ x, (partialDeriv idx φ) x ^ 2 ≤ E := by
    rw [sa16y3_N2_sq (sa16y3_memLp2_cc hwcc)]
    calc sa16y3_N2 (partialDeriv idx φ) volume ^ 2 ≤ sa16y3_ee φ j ^ 2 := pow_le_pow_left₀ (sa16y3_N2_nonneg _) hwj 2
      _ ≤ E := Finset.single_le_sum (f := fun k => sa16y3_ee φ k ^ 2) (fun k _ => sq_nonneg _) hjmem
  have hSlt : sa16z_S 2 φ j < ⊤ := sa16y3_S_lt_top hφ j
  have hSreal : (sa16z_S 2 φ j).toReal = ∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k := by
    unfold sa16z_S sa16z_JJ
    rw [ENNReal.toReal_sum (fun k _ => (hvnMem k).eLpNorm_ne_top)]
    rfl
  have hsq : (∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k) ^ 2 ≤ (j + 1) * E := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := fun k => sa16y3_ee φ k)
    simpa [Finset.card_range] using this
  -- per-term bounds
  have hterm : ∀ i j' : Fin d,
      |∫ x, (partialDeriv idx φ) x * sa16y3_Q s i (fun y => sa16z_dm μ j' y * (partialDeriv idx φ) y) x| + |∫ x, (partialDeriv idx φ) x * sa16y3_R s i (sa16z_dm μ j') φ j idx x| ≤
        (K0 + KR i * (j + 1)) * Λ * E := by
    intro i j'
    have hb : ContDiff ℝ ∞ (sa16z_dm μ j') := sa16z_dm_smooth hμ j'
    have hCbb : sa16z_Cb (j + 1) Λ (sa16z_dm μ j') := sa16z_Cb_dm hμ hCb j'
    have hC0 : sa16z_Cb 0 Λ (sa16z_dm μ j') := sa16z_Cb_mono (Nat.zero_le _) hCbb
    have hC1 : sa16z_Cb 1 Λ (sa16z_dm μ j') := sa16z_Cb_mono (by omega) hCbb
    have t1 := sa16y3_Q_half_Cb hd hs0 hsd hθ hb hwcc hΛ (sa16z_Cb_abs hC0) (sa16z_Cb_fderiv hC1) i
    have t1' : |∫ x, (partialDeriv idx φ) x * sa16y3_Q s i (fun y => sa16z_dm μ j' y * (partialDeriv idx φ) y) x| ≤ K0 * Λ * E :=
      t1.trans (mul_le_mul_of_nonneg_left hw2 (mul_nonneg hK0 hΛ))
    have hR := hKR i hb hφ hΛ hCbb idx
    have hRmem : MemLp (fun x => sa16y3_R s i (sa16z_dm μ j') φ j idx x) (ENNReal.ofReal 2) volume :=
      lt_of_le_of_lt hR (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSlt)
    have hRN : sa16y3_N2 (fun x => sa16y3_R s i (sa16z_dm μ j') φ j idx x) volume ≤
        KR i * Λ * ∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k := by
      unfold sa16y3_N2
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSlt.ne) hR
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (hKR0 i) hΛ), hSreal] at this
      exact this
    have t2 := sa16y3_cs (sa16y3_memLp2_cc hwcc) hRmem
    have hSnn : 0 ≤ ∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k := Finset.sum_nonneg fun k _ => he0 k
    have t2' : |∫ x, (partialDeriv idx φ) x * sa16y3_R s i (sa16z_dm μ j') φ j idx x| ≤ KR i * Λ * ((j + 1) * E) := by
      refine t2.trans ?_
      calc sa16y3_N2 (partialDeriv idx φ) volume * sa16y3_N2 (fun x => sa16y3_R s i (sa16z_dm μ j') φ j idx x) volume
          ≤ (∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k) * (KR i * Λ * ∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k) :=
            mul_le_mul (hwj.trans hej) hRN (sa16y3_N2_nonneg _) hSnn
        _ = KR i * Λ * (∑ k ∈ Finset.range (j + 1), sa16y3_ee φ k) ^ 2 := by ring
        _ ≤ KR i * Λ * ((j + 1) * E) := mul_le_mul_of_nonneg_left hsq (mul_nonneg (hKR0 i) hΛ)
    nlinarith
  -- decomposition of the integral
  have hQs : ∀ i j' : Fin d, ContDiff ℝ ∞ (sa16y3_Q s i (fun y => sa16z_dm μ j' y * (partialDeriv idx φ) y)) := fun i j' =>
    sa16y3_Q_smooth hs0 hsd (sa16y3_bmul_cc (sa16z_dm_smooth hμ j') hwcc) i
  have hRc : ∀ i j' : Fin d, Continuous (fun x => sa16y3_R s i (sa16z_dm μ j') φ j idx x) := fun i j' => by
    unfold sa16y3_R
    exact ((sa16j_pd_smooth (sa16y3_Q_smooth hs0 hsd (sa16y3_bmul_cc (sa16z_dm_smooth hμ j') hφ) i) idx).continuous).sub
      (sa16y3_Q_smooth hs0 hsd (sa16y3_bmul_cc (sa16z_dm_smooth hμ j') (sa16s_cc_partialDeriv hφ idx)) i).continuous
  have hI1 : ∀ i j' : Fin d, Integrable (fun x => (partialDeriv idx φ) x * sa16y3_Q s i (fun y => sa16z_dm μ j' y * (partialDeriv idx φ) y) x) :=
    fun i j' => (hwcc.1.continuous.mul (hQs i j').continuous).integrable_of_hasCompactSupport hwcc.2.mul_right
  have hI2 : ∀ i j' : Fin d, Integrable (fun x => (partialDeriv idx φ) x * sa16y3_R s i (sa16z_dm μ j') φ j idx x) :=
    fun i j' => (hwcc.1.continuous.mul (hRc i j')).integrable_of_hasCompactSupport hwcc.2.mul_right
  have hfun : (fun x => (partialDeriv idx φ) x * partialDeriv idx (sa16y3_PA s A μ φ) x) = fun x => ∑ i : Fin d, ∑ j' : Fin d,
      (-A j' i) * ((partialDeriv idx φ) x * sa16y3_Q s i (fun y => sa16z_dm μ j' y * (partialDeriv idx φ) y) x +
        (partialDeriv idx φ) x * sa16y3_R s i (sa16z_dm μ j') φ j idx x) := by
    funext x
    rw [sa16y3_PA_pd hs0 hsd hA hμ hφ idx x, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    ring
  have hint : ∫ x, (partialDeriv idx φ) x * partialDeriv idx (sa16y3_PA s A μ φ) x = ∑ i : Fin d, ∑ j' : Fin d, (-A j' i) *
      ((∫ x, (partialDeriv idx φ) x * sa16y3_Q s i (fun y => sa16z_dm μ j' y * (partialDeriv idx φ) y) x) +
        ∫ x, (partialDeriv idx φ) x * sa16y3_R s i (sa16z_dm μ j') φ j idx x) := by
    rw [hfun]
    refine (integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j' _ =>
      ((hI1 i j').add (hI2 i j')).const_mul _).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (integral_finsetSum _ fun j' _ => ((hI1 i j').add (hI2 i j')).const_mul _).trans ?_
    refine Finset.sum_congr rfl fun j' _ => ?_
    exact (integral_const_mul _ _).trans (congrArg (fun t => (-A j' i) * t) (integral_add (hI1 i j') (hI2 i j')))
  show |∫ x, (partialDeriv idx φ) x * partialDeriv idx (sa16y3_PA s A μ φ) x| ≤ _
  rw [hint]
  calc |∑ i : Fin d, ∑ j' : Fin d, (-A j' i) * ((∫ x, (partialDeriv idx φ) x * sa16y3_Q s i (fun y => sa16z_dm μ j' y * (partialDeriv idx φ) y) x) +
        ∫ x, (partialDeriv idx φ) x * sa16y3_R s i (sa16z_dm μ j') φ j idx x)|
      ≤ ∑ i : Fin d, ∑ j' : Fin d, AB * ((K0 + KR i * (j + 1)) * Λ * E) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j' _ => ?_)
        rw [abs_mul, abs_neg]
        refine mul_le_mul (hAab _ _) (((abs_add_le _ _).trans (hterm i j'))) (abs_nonneg _) hAB
    _ = ∑ i : Fin d, (d : ℝ) * (AB * ((K0 + KR i * (j + 1)) * Λ * E)) := by simp
    _ = (d : ℝ) * AB * Λ * E * ∑ i : Fin d, (K0 + KR i * (j + 1)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = ((d : ℝ) ^ 2 * K0 + (d : ℝ) * (j + 1) * ∑ i : Fin d, KR i) * AB * Λ * E := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Hk4

end HRS.Whole.AppendixA.Phase2SA16R
