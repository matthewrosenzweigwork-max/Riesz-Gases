import HRS.MS.SA12Z3NearN4B
import HRS.MS.SA12CellR35

/-!
# S.A.12 N4 (SA12Z3), part C: the commutator bound

For `f, h ∈ C¹_c` and `a ∈ C¹_b`:
`|∫ (f a) T h + ∫ (h a) T f| ≤ σ ‖a‖_{C¹_b} (∫κ) (∫f² + ∫h²)/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12z3_prod_integrable (s : ℝ) (i : Fin d) {ε : ℝ} (hε : 0 < ε) {u v : Euc d → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun p : Euc d × Euc d => u p.1 *
      movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * v p.2) (volume.prod volume) := by
  have hDc := sa12z2_dEps_cont (d := d) s hε i
  refine Continuous.integrable_of_hasCompactSupport (f := fun p : Euc d × Euc d => u p.1 *
      movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * v p.2)
    (((hu.comp continuous_fst).mul (hDc.comp (continuous_fst.sub continuous_snd))).mul
      (hv.comp continuous_snd)) ?_
  refine HasCompactSupport.intro (K := tsupport u ×ˢ tsupport v) (huc.prod hvc) (fun p hp => ?_)
  have : p.1 ∉ tsupport u ∨ p.2 ∉ tsupport v := by
    by_contra h
    push_neg at h
    exact hp (Set.mem_prod.2 h)
  rcases this with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

theorem sa12z3_comm_eps (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    (i : Fin d) {ε : ℝ} (hε : 0 < ε) {f h a : Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h) (ha : MemCb 1 a) :
    |sa12z3_S d s i ε (fun x => f x * a x) h - sa12z3_S d s i ε f (fun x => a x * h x)| ≤
      movtr_sigma s * cbNorm 1 a * ((∫ z, sa12z3_kap d s z) * ((∫ x, f x ^ 2) + ∫ x, h x ^ 2) / 2) := by
  have hsig : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have hcb : 0 ≤ cbNorm 1 a := HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_cb_nonneg ha
  have hac : Continuous a := ha.1.continuous
  have hI1 : Integrable (fun p : Euc d × Euc d => f p.1 * a p.1 *
      movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * h p.2) (volume.prod volume) :=
    sa12z3_prod_integrable s i hε (hf.mul hac) (hfc.mul_right) hh hhc
  have hI2 : Integrable (fun p : Euc d × Euc d => f p.1 *
      movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * (a p.2 * h p.2)) (volume.prod volume) :=
    sa12z3_prod_integrable s i hε hf hfc (hac.mul hh) (hhc.mul_left)
  unfold sa12z3_S
  beta_reduce
  rw [← integral_sub hI1 hI2]
  obtain ⟨hint, hy⟩ := sa12z3_young2 hd hs0 hsd hs1 hf hfc hh hhc
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hint.const_mul (movtr_sigma s * cbNorm 1 a)) ?_).trans ?_
  · refine Eventually.of_forall fun p => ?_
    have hnn : 0 ≤ movtr_sigma s * cbNorm 1 a * (|f p.1| * |h p.2| * sa12z3_kap d s (p.1 - p.2)) :=
      mul_nonneg (mul_nonneg hsig hcb) (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (sa12z3_kap_nonneg _ _))
    by_cases hz : p.1 - p.2 = 0
    · have hp : p.1 = p.2 := sub_eq_zero.1 hz
      have : f p.1 * a p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * h p.2 -
          f p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * (a p.2 * h p.2) = 0 := by
        rw [hp]; ring
      rw [this, norm_zero]; exact hnn
    · have hez : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ 1 := by simp
      have hD := movtr_dEps_abs_le_z hs0 hε.le (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) hez hz
      have hlip := HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_lip_of_cb (r := 1) le_rfl ha p.1 p.2
      have hsup : ∀ x, |a x| ≤ cbNorm 1 a := fun x => by
        have := HRS.MH.AdjointRd.Phase2SA12.sa12r35_single_le_cb ha (Nat.zero_le 1) x
        rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      have h2 : |a p.1 - a p.2| ≤ 2 * cbNorm 1 a := by
        have := abs_sub (a p.1) (a p.2)
        linarith [hsup p.1, hsup p.2]
      have hmin : |a p.1 - a p.2| ≤ cbNorm 1 a * min ‖p.1 - p.2‖ 2 := by
        rcases le_total ‖p.1 - p.2‖ 2 with h | h
        · rw [min_eq_left h]; exact hlip
        · rw [min_eq_right h]; linarith
      have e : f p.1 * a p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * h p.2 -
          f p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) * (a p.2 * h p.2) =
          f p.1 * movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2) *
            ((a p.1 - a p.2) * h p.2) := by ring
      rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      unfold sa12z3_kap
      have hk0 : 0 ≤ ‖p.1 - p.2‖ ^ (-s - 1) := Real.rpow_nonneg (norm_nonneg _) _
      have hmin0 : 0 ≤ min ‖p.1 - p.2‖ 2 := le_min (norm_nonneg _) (by norm_num)
      calc |f p.1| * |movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (p.1 - p.2)| *
            (|a p.1 - a p.2| * |h p.2|)
          ≤ |f p.1| * (movtr_sigma s * ‖p.1 - p.2‖ ^ (-s - 1)) * ((cbNorm 1 a * min ‖p.1 - p.2‖ 2) * |h p.2|) := by
            gcongr
        _ = movtr_sigma s * cbNorm 1 a * (|f p.1| * |h p.2| * (min ‖p.1 - p.2‖ 2 * ‖p.1 - p.2‖ ^ (-s - 1))) := by
            ring
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hy (mul_nonneg hsig hcb)

theorem sa12z3_comm_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    (i : Fin d) {f h a : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h) (ha : MemCb 1 a) :
    |(∫ x, (f x * a x) * firstRiesz d s i h x) + ∫ x, (h x * a x) * firstRiesz d s i f x| ≤
      movtr_sigma s * cbNorm 1 a * ((∫ z, sa12z3_kap d s z) * ((∫ x, f x ^ 2) + ∫ x, h x ^ 2) / 2) := by
  have hac : Continuous a := ha.1.continuous
  have hfa : Continuous (fun x => f x * a x) := hf.continuous.mul hac
  have hha : Continuous (fun x => h x * a x) := hh.continuous.mul hac
  have l1 := sa12z3_S_lim hd hs0 hsd i hfa (hfc.mul_right) hh hhc
  have l2 := sa12z3_S_lim hd hs0 hsd i hha (hhc.mul_right) hf hfc
  refine le_of_tendsto (l1.add l2).abs ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have e : sa12z3_S d s i ε (fun x => f x * a x) h + sa12z3_S d s i ε (fun x => h x * a x) f =
      sa12z3_S d s i ε (fun x => f x * a x) h - sa12z3_S d s i ε f (fun x => a x * h x) := by
    have := sa12z3_S_skew s i ε f (fun x => h x * a x)
    have e2 : (fun x => h x * a x) = fun x => a x * h x := funext fun x => mul_comm _ _
    rw [e2] at this
    have e3 := sa12z3_S_skew s i ε (fun x => h x * a x) f
    rw [e2] at e3 ⊢
    linarith
  simp only [e]
  exact sa12z3_comm_eps hd hs0 hsd hs1 i hε' hf.continuous hfc hh.continuous hhc ha

end HRS.MH.AdjointRd.Phase2SA12Near
