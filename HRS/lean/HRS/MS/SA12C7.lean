import HRS.MS.SA12C6

/-!
# S.A.12(c), packet E7.06 (part 5): the integrated rate of one jet over the period box

For an `L`-periodic smooth `F`, periodic `C^{m+1}` drift `b` with bounded derivatives `1 ≤ k ≤ m+1` and smooth `G`:
`∫_{Q_L} 2 ∂^α F ∂^α(νΔF + b·∇F + G) ≤ -2ν ∑_i ∫_{Q_L}(∂_i∂^α F)² + K ∫_{Q_L} Y + ∫_{Q_L} 2 ∂^αF ∂^αG`
with `K = d C_b + 1 + (d C_b 2^m)² c_T` (periodic integration by parts: no cutoff, exact diffusion coefficient `2ν`;
the transport term uses only `div b` and the commutator uses only derivatives of `b`).
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3
open HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

/-- The rate constant of one jet. -/
def sa12cK (d m : ℕ) (Cb : ℝ) : ℝ := d * Cb + 1 + ((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_cT d m

theorem sa12cK_nonneg (d m : ℕ) {Cb : ℝ} (hCb : 0 ≤ Cb) : 0 ≤ sa12cK d m Cb := by
  unfold sa12cK
  have := sa12z3_cT_nonneg d m
  positivity

theorem sa12c_rate_idx {m n : ℕ} (hn : n ≤ m) {L : ℝ} (hL : 0 < L)
    {F G : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x)
    {b : Euc d → Euc d} {Cb : ℝ} (hbC : ContDiff ℝ (m + 1) b)
    (hbp : ∀ (x : Euc d) (k : Fin d → ℤ), b (x + L • latticePt k) = b x)
    (hbb : ∀ k, 1 ≤ k → k ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ Cb) (ν : ℝ) (idx : Fin n → Fin d) :
    ∫ x in periodBox d L, 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) ≤
      -(2 * ν * ∑ i : Fin d, ∫ x in periodBox d L,
          (partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2) +
        sa12cK d m Cb * (∫ x in periodBox d L, sa12z3_Y m F x) +
        ∫ x in periodBox d L, 2 * (partialDeriv idx F x * partialDeriv idx G x) := by
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hbb 1 le_rfl (by omega) 0)
  have hWi : ContDiff ℝ ∞ (partialDeriv idx F) := sa12z3_pd_contDiff_inf hF idx
  have hWp := sa12c_pd_periodic hFp idx
  have hFn : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F := hF.of_le (sa12x2_le_top _)
  have hbi : ∀ i : Fin d, ContDiff ℝ n (fun y => b y i) := fun i =>
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hbC).of_le (by exact_mod_cast (by omega : n ≤ m + 1))
  have hinC : ContDiff ℝ n (fun y => inner ℝ (b y) (gradient F y)) := by
    have : (fun y => inner ℝ (b y) (gradient F y)) = fun y => ∑ i : Fin d, b y i * D1 i F y := by
      funext y; rw [sa12x3_inner_grad]
    rw [this]
    exact ContDiff.sum fun i _ => (hbi i).mul (sa12z3_cd_of_inf (sa12y_D1_contDiff hF i) n)
  have hQc : Continuous (partialDeriv idx (fun y => inner ℝ (b y) (gradient F y))) :=
    (sa12x2_pd_cd (k := 0) (by simpa using hinC) idx).continuous
  have hpGc : Continuous (partialDeriv idx G) := (sa12z3_pd_contDiff_inf hG idx).continuous
  have hcomm : ∀ x, |partialDeriv idx (fun y => inner ℝ (b y) (gradient F y)) x -
      fderiv ℝ (partialDeriv idx F) x (b x)| ≤ d * (Cb * 2 ^ m * sa12z3_T m F x) :=
    fun x => sa12x3_comm_pt hn hbC (fun k hk1 hkm => hbb k hk1 hkm) hF idx x
  have hsq : ∀ x, partialDeriv idx F x ^ 2 ≤ sa12z3_Y m F x := fun x => sa12x2_sq_le_Y hn F idx x
  have hsn : ∀ (i : Fin d) (x : Euc d), partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x =
      D1 i (partialDeriv idx F) x := fun i x => (sa12x2_pd_snoc n F hFn idx i x).symm
  have hdec : ∀ x, 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) =
      (∑ i : Fin d, ν * (2 * (partialDeriv idx F x * D1 i (D1 i (partialDeriv idx F)) x))) +
      2 * (partialDeriv idx F x * fderiv ℝ (partialDeriv idx F) x (b x)) +
      2 * (partialDeriv idx F x * (partialDeriv idx (fun y => inner ℝ (b y) (gradient F y)) x -
        fderiv ℝ (partialDeriv idx F) x (b x))) +
      2 * (partialDeriv idx F x * partialDeriv idx G x) := by
    intro x
    rw [sa12x3_pd_rate hn hbC hF hG ν idx x]
    have : ∑ i : Fin d, ν * (2 * (partialDeriv idx F x * D1 i (D1 i (partialDeriv idx F)) x)) =
        2 * (partialDeriv idx F x * (ν * ∑ i : Fin d, D1 i (D1 i (partialDeriv idx F)) x)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    ring
  -- abstract the jet
  generalize hW : partialDeriv idx F = W at *
  set Cm : Euc d → ℝ := fun x => partialDeriv idx (fun y => inner ℝ (b y) (gradient F y)) x -
    fderiv ℝ W x (b x) with hCm
  set Q : Euc d → ℝ := partialDeriv idx (fun y => inner ℝ (b y) (gradient F y)) with hQ
  set pG : Euc d → ℝ := partialDeriv idx G with hpG
  have hWc : Continuous W := hWi.continuous
  have hW1 : ContDiff ℝ 1 W := sa12z3_cd_of_inf hWi 1
  have hbC1 : ContDiff ℝ 1 b := hbC.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hbfd : Continuous (fun x => fderiv ℝ W x (b x)) :=
    (hW1.continuous_fderiv one_ne_zero).clm_apply hbC1.continuous
  have hCmc : Continuous Cm := hQc.sub hbfd
  have hDDW : ∀ i : Fin d, Continuous (fun x => D1 i (D1 i W) x) := fun i =>
    (sa12y_D1_contDiff (sa12y_D1_contDiff hWi i) i).continuous
  have hQI : ∀ f : Euc d → ℝ, Continuous f → IntegrableOn f (periodBox d L) :=
    fun f hf => sa12v_integrableOn_box L hf
  have hc1 : ∀ i : Fin d, Continuous (fun x => ν * (2 * (W x * D1 i (D1 i W) x))) := fun i =>
    continuous_const.mul (continuous_const.mul (hWc.mul (hDDW i)))
  have hc2 : Continuous (fun x => 2 * (W x * fderiv ℝ W x (b x))) :=
    continuous_const.mul (hWc.mul hbfd)
  have hc3 : Continuous (fun x => 2 * (W x * Cm x)) := continuous_const.mul (hWc.mul hCmc)
  have hc4 : Continuous (fun x => 2 * (W x * pG x)) := continuous_const.mul (hWc.mul hpGc)
  have hsplit : ∫ x in periodBox d L, 2 * (W x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) =
      (∑ i : Fin d, ν * ∫ x in periodBox d L, 2 * (W x * D1 i (D1 i W) x)) +
      (∫ x in periodBox d L, 2 * (W x * fderiv ℝ W x (b x))) +
      (∫ x in periodBox d L, 2 * (W x * Cm x)) + ∫ x in periodBox d L, 2 * (W x * pG x) := by
    have hfun : (fun x => 2 * (W x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x)) =
        fun x => (∑ i : Fin d, ν * (2 * (W x * D1 i (D1 i W) x))) +
          2 * (W x * fderiv ℝ W x (b x)) + 2 * (W x * Cm x) + 2 * (W x * pG x) := funext hdec
    have hIs : IntegrableOn (fun x => ∑ i : Fin d, ν * (2 * (W x * D1 i (D1 i W) x))) (periodBox d L) :=
      integrable_finset_sum _ fun i _ => hQI _ (hc1 i)
    have hc12 : Continuous (fun x => (∑ i : Fin d, ν * (2 * (W x * D1 i (D1 i W) x))) +
        2 * (W x * fderiv ℝ W x (b x))) := (continuous_finsetSum _ fun i _ => hc1 i).add hc2
    have hc123 : Continuous (fun x => (∑ i : Fin d, ν * (2 * (W x * D1 i (D1 i W) x))) +
        2 * (W x * fderiv ℝ W x (b x)) + 2 * (W x * Cm x)) := hc12.add hc3
    rw [hfun, integral_add (hQI _ hc123) (hQI _ hc4), integral_add (hQI _ hc12) (hQI _ hc3),
      integral_add hIs (hQI _ hc2), integral_finset_sum _ fun i _ => hQI _ (hc1 i)]
    simp only [integral_const_mul]
  -- diffusion
  have hD : (∑ i : Fin d, ν * ∫ x in periodBox d L, 2 * (W x * D1 i (D1 i W) x)) =
      -(2 * ν * ∑ i : Fin d, ∫ x in periodBox d L, (partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2) := by
    have h1 : ∀ i : Fin d, ν * ∫ x in periodBox d L, 2 * (W x * D1 i (D1 i W) x) =
        -(2 * ν * ∫ x in periodBox d L, (partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x) ^ 2) := by
      intro i
      rw [sa12c_diffusion_idx hL hWi hWp i]
      have : ∀ x, partialDeriv (Fin.snoc idx i : Fin (n + 1) → Fin d) F x = D1 i W x := fun x => by
        rw [hsn i x]
      simp_rw [this]
      ring
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_neg_distrib, ← Finset.mul_sum]
  -- transport
  have hT := sa12c_transport_idx hL hbC hbp hbb hWi hWp
  have hWY : ∫ x in periodBox d L, W x ^ 2 ≤ ∫ x in periodBox d L, sa12z3_Y m F x :=
    integral_mono (hQI _ (hWc.pow 2)) (hQI _ (sa12c_Y_cont hF m)) fun x => hsq x
  have hY0 : 0 ≤ ∫ x in periodBox d L, sa12z3_Y m F x :=
    setIntegral_nonneg (sa12c20_box_meas L) fun x _ => sa12z3_Y_nonneg m F x
  have hdCb : 0 ≤ (d : ℝ) * Cb := by positivity
  have hT2 : ∫ x in periodBox d L, 2 * (W x * fderiv ℝ W x (b x)) ≤
      (d * Cb) * ∫ x in periodBox d L, sa12z3_Y m F x :=
    hT.trans (mul_le_mul_of_nonneg_left hWY hdCb)
  -- commutator
  have hCm2 : ∫ x in periodBox d L, Cm x ^ 2 ≤
      (((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_cT d m) * ∫ x in periodBox d L, sa12z3_Y m F x := by
    rw [← integral_const_mul]
    refine integral_mono (hQI _ (hCmc.pow 2)) ((hQI _ (sa12c_Y_cont hF m)).const_mul _) fun x => ?_
    have h1 := hcomm x
    have hT := sa12z3_T_sq (d := d) m F x
    have hcT := sa12z3_cT_nonneg d m
    have hY := sa12z3_Y_nonneg m F x
    calc Cm x ^ 2 = |Cm x| ^ 2 := (sq_abs _).symm
      _ ≤ (d * (Cb * 2 ^ m * sa12z3_T m F x)) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          exact h1
      _ = ((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_T m F x ^ 2 := by ring
      _ ≤ ((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * (sa12z3_cT d m * sa12z3_Y m F x) := by gcongr
      _ = _ := by ring
  have hP3 : ∫ x in periodBox d L, 2 * (W x * Cm x) ≤
      (∫ x in periodBox d L, W x ^ 2) + ∫ x in periodBox d L, Cm x ^ 2 := by
    have hsum : ∫ x in periodBox d L, (W x ^ 2 + Cm x ^ 2) =
        (∫ x in periodBox d L, W x ^ 2) + ∫ x in periodBox d L, Cm x ^ 2 :=
      integral_add (f := fun x => W x ^ 2) (g := fun x => Cm x ^ 2) (hQI _ (hWc.pow 2)) (hQI _ (hCmc.pow 2))
    rw [← hsum]
    exact integral_mono (hQI _ hc3) (hQI (fun x => W x ^ 2 + Cm x ^ 2) ((hWc.pow 2).add (hCmc.pow 2)))
      fun x => by nlinarith [sq_nonneg (W x - Cm x)]
  have hmain : (∫ x in periodBox d L, 2 * (W x * fderiv ℝ W x (b x))) +
      (∫ x in periodBox d L, 2 * (W x * Cm x)) ≤
      sa12cK d m Cb * ∫ x in periodBox d L, sa12z3_Y m F x := by
    unfold sa12cK
    have hfin : ((d : ℝ) * Cb + 1 + ((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_cT d m) *
        ∫ x in periodBox d L, sa12z3_Y m F x =
        (d * Cb) * (∫ x in periodBox d L, sa12z3_Y m F x) + (∫ x in periodBox d L, sa12z3_Y m F x) +
        (((d : ℝ) * (Cb * 2 ^ m)) ^ 2 * sa12z3_cT d m) * ∫ x in periodBox d L, sa12z3_Y m F x := by ring
    linarith [hT2, hP3, hCm2, hWY, hfin]
  rw [hsplit, hD]
  have key : ∀ A I4 : ℝ, A + (∫ x in periodBox d L, 2 * (W x * fderiv ℝ W x (b x))) +
      (∫ x in periodBox d L, 2 * (W x * Cm x)) + I4 ≤
      A + sa12cK d m Cb * (∫ x in periodBox d L, sa12z3_Y m F x) + I4 := fun A I4 => by linarith [hmain]
  exact key _ _

end HRS.MH.AdjointRd.Phase2SA12C
