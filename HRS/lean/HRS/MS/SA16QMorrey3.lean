import HRS.MS.SA16QMorrey2

/-!
# S.A.16 (SA16Q), E11 part 3: the averaged Taylor estimate

`sa16q_morrey_key`: for `p > 1` and `n ≥ 1` with `n p > d`, a smooth `v : ℝ^d → F` satisfies
`‖v x‖ ≤ C ∑_{k ≤ n} ‖D^k v‖_{L^p}` (in `ℝ≥0∞`), with `C` independent of `v, x, F`.

Proof: average the Taylor formula of `sa16q_taylor_pt` over `z` in the annulus `1 < |z| < 2`;
the remainder is rescaled `z ↦ t z` and the `L^p` norm of `D^n v` appears with the factor
`t^{-d/p}`, integrable against `t^{n-1}` exactly when `n > d/p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Nat

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Key
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma sa16q_meas_D {v : Euc d → F} (hv : ContDiff ℝ ∞ v) (k : ℕ) :
    Measurable (fun y : Euc d => ‖iteratedFDeriv ℝ k v y‖ₑ) :=
  (continuous_enorm.comp (hv.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top))).measurable

lemma sa16q_pt_enorm {v : Euc d → F} (hv : ContDiff ℝ ∞ v) (x z : Euc d) (hz : z ∈ sa16q_A d)
    (N : ℕ) :
    ‖v x‖ₑ ≤ ∑ k ∈ Finset.range (N + 1),
        ENNReal.ofReal (2 ^ k / (k ! : ℝ)) * ‖iteratedFDeriv ℝ k v (x + z)‖ₑ +
      ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) *
        ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ N) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ := by
  obtain ⟨hz1, hz2⟩ := sa16q_A_mem hz
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hT := sa16q_taylor_pt hv x z N
  set S : ℝ := ∑ k ∈ Finset.range (N + 1),
    ‖z‖ ^ k / (k ! : ℝ) * ‖iteratedFDeriv ℝ k v (x + z)‖ with hS
  set I : ℝ := ∫ t in (0 : ℝ)..1, t ^ N / (N ! : ℝ) *
    (‖z‖ ^ (N + 1) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖) with hI
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  have hcont : Continuous (fun t : ℝ => ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖) :=
    ((hv.continuous_iteratedFDeriv (m := N + 1) (by exact_mod_cast le_top)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).norm
  have hcont2 : Continuous (fun t : ℝ => t ^ N / (N ! : ℝ) *
      (‖z‖ ^ (N + 1) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖)) := by fun_prop
  have hint := hcont2.intervalIntegrable (μ := volume) 0 1
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by norm_num) (fun t ht => by
    have := ht.1; positivity)
  calc ‖v x‖ₑ = ENNReal.ofReal ‖v x‖ := (ofReal_norm_eq_enorm _).symm
    _ ≤ ENNReal.ofReal (S + I) := ENNReal.ofReal_le_ofReal hT
    _ = ENNReal.ofReal S + ENNReal.ofReal I := ENNReal.ofReal_add hS0 hI0
    _ ≤ _ := by
      refine add_le_add ?_ ?_
      · rw [hS, ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm]
        have hz2' : ‖z‖ ≤ 2 := hz2.le
        gcongr
      · have hnn : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ t ^ N / (N ! : ℝ) *
            (‖z‖ ^ (N + 1) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖) := fun t ht => by
          have := ht.1; positivity
        rw [hI, intervalIntegral.integral_of_le zero_le_one,
          ofReal_integral_eq_lintegral_ofReal
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hint)
            (ae_restrict_of_forall_mem measurableSet_Ioc hnn),
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        have ht0 : 0 ≤ t := ht.1.le
        have hD0 : 0 ≤ ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ := norm_nonneg _
        have hzp : ‖z‖ ^ (N + 1) ≤ 2 ^ (N + 1) := pow_le_pow_left₀ hz0 hz2.le _
        have hreal : t ^ N / (N ! : ℝ) * (‖z‖ ^ (N + 1) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖) ≤
            2 ^ (N + 1) / (N ! : ℝ) * (t ^ N * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖) := by
          have hf : (0 : ℝ) < (N ! : ℝ) := by exact_mod_cast Nat.factorial_pos N
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hf]
          have htN : 0 ≤ t ^ N := pow_nonneg ht0 N
          nlinarith [mul_nonneg htN hD0, mul_le_mul_of_nonneg_left hzp (mul_nonneg htN hD0)]
        calc ENNReal.ofReal (t ^ N / (N ! : ℝ) *
              (‖z‖ ^ (N + 1) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖))
            ≤ ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ) *
                (t ^ N * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖)) := ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) *
                (ENNReal.ofReal (t ^ N) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (pow_nonneg ht0 N),
                ofReal_norm_eq_enorm]

lemma sa16q_pow_comb {t : ℝ} (ht : 0 < t) (N d : ℕ) (p : ℝ) :
    t ^ N * ((t ^ d)⁻¹) ^ (1 / p) = t ^ ((N : ℝ) - d / p) := by
  have h1 : ((t ^ d)⁻¹) ^ (1 / p) = (t ^ ((d : ℝ) / p))⁻¹ := by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 2
    ring
  rw [h1, Real.rpow_sub ht, Real.rpow_natCast]
  exact (div_eq_mul_inv _ _).symm

/-- the lower-order terms -/
lemma sa16q_low (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) {v : Euc d → F} (hv : ContDiff ℝ ∞ v) (x : Euc d)
    (k : ℕ) :
    ∫⁻ z in sa16q_A d, ‖iteratedFDeriv ℝ k v (x + z)‖ₑ ≤
      volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
        (∫⁻ y, ‖iteratedFDeriv ℝ k v y‖ₑ ^ p) ^ (1 / p) := by
  have h := sa16q_annulus_holder hd hp (t := 1) one_pos x (sa16q_meas_D hv k)
  simpa using h

/-- the remainder term -/
lemma sa16q_rem (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) {N : ℕ} {v : Euc d → F} (hv : ContDiff ℝ ∞ v)
    (x : Euc d) :
    ∫⁻ z in sa16q_A d, ∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal (t ^ N) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ ≤
      volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
        ((∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ ((N : ℝ) - d / p))) *
          (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p)) := by
  have hDm := sa16q_meas_D hv
  have hjm : Measurable (Function.uncurry fun (z : Euc d) (t : ℝ) =>
      ENNReal.ofReal (t ^ N) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ) := by
    refine (ENNReal.measurable_ofReal.comp ((measurable_snd).pow_const N)).mul ?_
    exact (hDm (N + 1)).comp (continuous_const.add (continuous_snd.smul continuous_fst)).measurable
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  have hinner : ∀ t ∈ Ioc (0 : ℝ) 1,
      ∫⁻ z in sa16q_A d, ENNReal.ofReal (t ^ N) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ ≤
        volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
          (ENNReal.ofReal (t ^ ((N : ℝ) - d / p)) *
            (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hm : Measurable (fun z : Euc d => ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ) :=
      (hDm (N + 1)).comp ((measurable_const_add x).comp (measurable_const_smul t))
    rw [lintegral_const_mul _ hm]
    have h := sa16q_annulus_holder hd hp ht0 x (hDm (N + 1))
    have hc := sa16q_pow_comb ht0 N d p
    calc ENNReal.ofReal (t ^ N) * ∫⁻ z in sa16q_A d, ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ
        ≤ ENNReal.ofReal (t ^ N) * (volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
            (ENNReal.ofReal (((t ^ d)⁻¹) ^ (1 / p)) *
              (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p))) := by gcongr
      _ = volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
            (ENNReal.ofReal (t ^ N * ((t ^ d)⁻¹) ^ (1 / p)) *
              (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p)) := by
          rw [ENNReal.ofReal_mul (pow_nonneg ht0.le N)]; ring
      _ = _ := by rw [hc]
  have hg : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ ((N : ℝ) - d / p))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  calc ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in sa16q_A d, ENNReal.ofReal (t ^ N) *
          ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ
      ≤ ∫⁻ t in Ioc (0 : ℝ) 1, volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
          (ENNReal.ofReal (t ^ ((N : ℝ) - d / p)) *
            (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p)) :=
        setLIntegral_mono' measurableSet_Ioc hinner
    _ = _ := by
        have hgH : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ ((N : ℝ) - d / p)) *
            (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p)) := hg.mul measurable_const
        rw [lintegral_const_mul _ hgH, lintegral_mul_const'' _ hg.aemeasurable]

/-- the integrated estimate over the annulus -/
lemma sa16q_key_int (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) {N : ℕ}
    {v : Euc d → F} (hv : ContDiff ℝ ∞ v) (x : Euc d) :
    volume (sa16q_A d) * ‖v x‖ₑ ≤ volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
      (∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (2 ^ k / (k ! : ℝ)) *
          (∫⁻ y, ‖iteratedFDeriv ℝ k v y‖ₑ ^ p) ^ (1 / p) +
        ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) *
          ((∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ ((N : ℝ) - d / p))) *
            (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p))) := by
  have hDm := sa16q_meas_D hv
  have hS1m : Measurable (fun z : Euc d => ∑ k ∈ Finset.range (N + 1),
      ENNReal.ofReal (2 ^ k / (k ! : ℝ)) * ‖iteratedFDeriv ℝ k v (x + z)‖ₑ) := by
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (measurable_const.mul ((hDm k).comp (measurable_const_add x)))
  calc volume (sa16q_A d) * ‖v x‖ₑ = ∫⁻ z in sa16q_A d, ‖v x‖ₑ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ z in sa16q_A d, (∑ k ∈ Finset.range (N + 1),
          ENNReal.ofReal (2 ^ k / (k ! : ℝ)) * ‖iteratedFDeriv ℝ k v (x + z)‖ₑ +
        ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) * ∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (t ^ N) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ) :=
        setLIntegral_mono' (sa16q_A_meas d) fun z hz => sa16q_pt_enorm hv x z hz N
    _ = (∫⁻ z in sa16q_A d, ∑ k ∈ Finset.range (N + 1),
          ENNReal.ofReal (2 ^ k / (k ! : ℝ)) * ‖iteratedFDeriv ℝ k v (x + z)‖ₑ) +
        ∫⁻ z in sa16q_A d, ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) * ∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (t ^ N) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ :=
        lintegral_add_left hS1m _
    _ ≤ volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
          ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (2 ^ k / (k ! : ℝ)) *
            (∫⁻ y, ‖iteratedFDeriv ℝ k v y‖ₑ ^ p) ^ (1 / p) +
        volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
          (ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) *
            ((∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ ((N : ℝ) - d / p))) *
              (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p))) := by
        refine add_le_add ?_ ?_
        · calc ∫⁻ z in sa16q_A d, ∑ k ∈ Finset.range (N + 1),
                ENNReal.ofReal (2 ^ k / (k ! : ℝ)) * ‖iteratedFDeriv ℝ k v (x + z)‖ₑ
              = ∑ k ∈ Finset.range (N + 1), ∫⁻ z in sa16q_A d,
                ENNReal.ofReal (2 ^ k / (k ! : ℝ)) * ‖iteratedFDeriv ℝ k v (x + z)‖ₑ :=
                lintegral_finset_sum _ (fun k _ => measurable_const.mul
                  ((hDm k).comp (measurable_const_add x)))
            _ ≤ ∑ k ∈ Finset.range (N + 1), volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
                (ENNReal.ofReal (2 ^ k / (k ! : ℝ)) *
                  (∫⁻ y, ‖iteratedFDeriv ℝ k v y‖ₑ ^ p) ^ (1 / p)) := by
                refine Finset.sum_le_sum fun k _ => ?_
                have hmk : Measurable (fun z : Euc d => ‖iteratedFDeriv ℝ k v (x + z)‖ₑ) :=
                  (hDm k).comp (measurable_const_add x)
                rw [lintegral_const_mul _ hmk]
                calc ENNReal.ofReal (2 ^ k / (k ! : ℝ)) * ∫⁻ z in sa16q_A d,
                      ‖iteratedFDeriv ℝ k v (x + z)‖ₑ
                    ≤ ENNReal.ofReal (2 ^ k / (k ! : ℝ)) * (volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
                        (∫⁻ y, ‖iteratedFDeriv ℝ k v y‖ₑ ^ p) ^ (1 / p)) := by
                      gcongr
                      exact sa16q_low hd hp hv x k
                  _ = _ := by ring
            _ = _ := by rw [Finset.mul_sum]
        · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          calc ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) * ∫⁻ z in sa16q_A d, ∫⁻ t in Ioc (0 : ℝ) 1,
                ENNReal.ofReal (t ^ N) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ₑ
              ≤ ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) * (volume (sa16q_A d) ^ (1 / Real.conjExponent p) *
                  ((∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ ((N : ℝ) - d / p))) *
                    (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p))) := by
                gcongr
                exact sa16q_rem hd hp hv x
            _ = _ := by ring
    _ = _ := by rw [← mul_add]

lemma sa16q_H_eq {v : Euc d → F} (hv : ContDiff ℝ ∞ v) (k : ℕ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ y, ‖iteratedFDeriv ℝ k v y‖ₑ ^ p) ^ (1 / p) =
      eLpNorm (fun y => ‖iteratedFDeriv ℝ k v y‖) (ENNReal.ofReal p) volume := by
  have hm : AEStronglyMeasurable (fun y => ‖iteratedFDeriv ℝ k v y‖) volume :=
    ((hv.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).norm).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hp.le]
  simp only [enorm_norm]

lemma sa16q_Ka_lt (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) {N : ℕ} (hNp : (d : ℝ) / p < N + 1) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ ((N : ℝ) - d / p)) < ⊤ := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ ((N : ℝ) - d / p)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hint
  have h2 : ∀ t ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ ((N : ℝ) - d / p)) = ‖t ^ ((N : ℝ) - d / p)‖ₑ := by
    intro t ht
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  rw [setLIntegral_congr_fun measurableSet_Ioc h2]
  exact h1.2

theorem sa16q_morrey_key (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n)
    (hnp : (d : ℝ) / p < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (v : Euc d → F), ContDiff ℝ ∞ v → ∀ x : Euc d,
      ‖v x‖ₑ ≤ ENNReal.ofReal C * ∑ k ∈ Finset.range (n + 1),
        eLpNorm (fun y => ‖iteratedFDeriv ℝ k v y‖) (ENNReal.ofReal p) volume := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hNp : (d : ℝ) / p < N + 1 := by exact_mod_cast hnp
  have hp0 : 0 < p := by linarith
  set K := ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ ((N : ℝ) - d / p)) with hK
  have hKt : K < ⊤ := sa16q_Ka_lt hd hp hNp
  set B : ℝ≥0∞ := ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (2 ^ k / (k ! : ℝ)) +
    ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) * K with hB
  have hBt : B ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨?_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKt.ne⟩
    exact (ENNReal.sum_lt_top.2 fun k _ => ENNReal.ofReal_lt_top).ne
  set VA := volume (sa16q_A d) with hVA
  have hVA0 : VA ≠ 0 := (sa16q_A_pos hd).ne'
  have hVAt : VA ≠ ⊤ := (sa16q_A_fin d).ne
  have hVq : VA ^ (1 / Real.conjExponent p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by
      have := (Real.HolderConjugate.conjExponent hp).symm.pos
      positivity) hVAt
  set C0 : ℝ≥0∞ := VA⁻¹ * (VA ^ (1 / Real.conjExponent p) * B) with hC0
  have hC0t : C0 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hVA0) (ENNReal.mul_ne_top hVq hBt)
  refine ⟨C0.toReal + 1, by positivity, fun F _ _ _ v hv x => ?_⟩
  set Hs : ℝ≥0∞ := ∑ k ∈ Finset.range (N + 1 + 1),
    eLpNorm (fun y => ‖iteratedFDeriv ℝ k v y‖) (ENNReal.ofReal p) volume with hHs
  have hH : ∀ k ≤ N + 1, (∫⁻ y, ‖iteratedFDeriv ℝ k v y‖ₑ ^ p) ^ (1 / p) ≤ Hs := by
    intro k hk
    rw [sa16q_H_eq hv k hp0]
    exact Finset.single_le_sum (f := fun k => eLpNorm (fun y => ‖iteratedFDeriv ℝ k v y‖)
      (ENNReal.ofReal p) volume) (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))
  have hkey := sa16q_key_int hd hp (N := N) hv x
  have hinner : ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (2 ^ k / (k ! : ℝ)) *
          (∫⁻ y, ‖iteratedFDeriv ℝ k v y‖ₑ ^ p) ^ (1 / p) +
        ENNReal.ofReal (2 ^ (N + 1) / (N ! : ℝ)) *
          (K * (∫⁻ y, ‖iteratedFDeriv ℝ (N + 1) v y‖ₑ ^ p) ^ (1 / p)) ≤ B * Hs := by
    rw [hB, add_mul, Finset.sum_mul]
    refine add_le_add (Finset.sum_le_sum fun k hk => ?_) ?_
    · exact sa16q_mul_le (hH k (by have := Finset.mem_range.1 hk; omega))
    · rw [← mul_assoc]
      exact sa16q_mul_le (hH (N + 1) le_rfl)
  have hfin : ‖v x‖ₑ = VA⁻¹ * (VA * ‖v x‖ₑ) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hVA0 hVAt, one_mul]
  calc ‖v x‖ₑ = VA⁻¹ * (VA * ‖v x‖ₑ) := hfin
    _ ≤ VA⁻¹ * (VA ^ (1 / Real.conjExponent p) * (B * Hs)) := by
        exact sa16q_mul_le (hkey.trans (sa16q_mul_le hinner))
    _ = C0 * Hs := by rw [hC0]; ring
    _ ≤ ENNReal.ofReal (C0.toReal + 1) * Hs := by
        gcongr
        calc C0 = ENNReal.ofReal C0.toReal := (ENNReal.ofReal_toReal hC0t).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

end Key

end HRS.Whole.AppendixA.Phase2SA16Q
