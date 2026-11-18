import HRS.MS.MfeConfAux9
import HRS.MH.DualityRdB2Aux

/-!
# S.B.1, packet F1 (part 5): sup-norm Lipschitz continuity in time and `C²`-continuity of the trajectory

* `sb1_pair_approx`: for a slice `h`, `|⟨h, η_n(x-·)⟩ - h(x)| ≤ C r_n`.
* `sb1_rho_lip_time`: `|ρ_b(x) - ρ_a(x)| ≤ K_A |b - a|` for all `x` (weak interval identity + approximate identity).
* `sb1_rho_C2_time`: `sup_x ‖D^l(ρ_b - ρ_a)(x)‖ ≤ ε` for `l = 1, 2` as soon as `|b - a|` is small (Landau-Kolmogorov
  `sb1_lk_first`, `sb1_lk_second`, with the slice bounds on `D²ρ`, `D³ρ`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.RdGen HRS.MH.DualityRd

variable {d : ℕ}

theorem sb1_slice_lip {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (x y : Euc d) :
    |h y - h x| ≤ C * ‖y - x‖ := by
  obtain ⟨hc3, -, -, h1', -, -⟩ := sb1_slice_facts S
  exact db2_lip_of (hc3.of_le (by norm_num)) h1' y x

theorem sb1_pair_approx {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (x : Euc d) (n : ℕ) :
    |Whole.pair (Whole.withDensityReal h) (fun y => db2_eta (d := d) n (x - y)) - h x|
      ≤ C * (db1_bump d n).rOut := by
  have hρ := S.dens
  have hρc : Continuous h := S.decay.1.continuous
  have hΛ := S.C_nonneg
  have hρb : ∀ y, h y ≤ C := fun y =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact (sb1_slice_facts S).2.2.2.2.2 y)
  have hint : ∫ y, h x * db2_eta (d := d) n (x - y) = h x := by
    rw [integral_const_mul, integral_sub_left_eq_self (fun z => db2_eta (d := d) n z) volume x,
      db2_eta_integral, mul_one]
  have hi1 : Integrable (fun y => h y * db2_eta (d := d) n (x - y)) := by
    refine ((db2_eta_shift_int n x).const_mul C).mono'
      (hρc.measurable.mul ((db2_eta_cont n).measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg y) (db2_eta_nonneg n _))]
    exact mul_le_mul_of_nonneg_right (hρb y) (db2_eta_nonneg n _)
  have hi2 : Integrable (fun y => h x * db2_eta (d := d) n (x - y)) :=
    (db2_eta_shift_int n x).const_mul _
  have hsub : ∫ y, (h y * db2_eta (d := d) n (x - y) - h x * db2_eta (d := d) n (x - y))
      = (∫ y, h y * db2_eta (d := d) n (x - y)) - ∫ y, h x * db2_eta (d := d) n (x - y) :=
    integral_sub hi1 hi2
  have hpt : (fun y => h y * db2_eta (d := d) n (x - y) - h x * db2_eta (d := d) n (x - y))
      = fun y => (h y - h x) * db2_eta (d := d) n (x - y) := funext fun y => by ring
  rw [hpt, hint] at hsub
  have key : Whole.pair (Whole.withDensityReal h) (fun y => db2_eta (d := d) n (x - y)) - h x
      = ∫ y, (h y - h x) * db2_eta (d := d) n (x - y) := by
    rw [Whole.Q09A.pair_withDensityReal hρ]
    linarith
  rw [key, ← Real.norm_eq_abs]
  have hgi : Integrable (fun y => C * (db1_bump d n).rOut * db2_eta (d := d) n (x - y)) :=
    (db2_eta_shift_int n x).const_mul _
  calc ‖∫ y, (h y - h x) * db2_eta (d := d) n (x - y)‖
      ≤ ∫ y, C * (db1_bump d n).rOut * db2_eta (d := d) n (x - y) := by
        refine norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (db2_eta_nonneg n _)]
        by_cases hlt : ‖x - y‖ < (db1_bump d n).rOut
        · have hl := sb1_slice_lip S x y
          have : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
          rw [this] at hl
          have h1 : |h y - h x| ≤ C * (db1_bump d n).rOut :=
            hl.trans (mul_le_mul_of_nonneg_left hlt.le hΛ)
          exact mul_le_mul_of_nonneg_right h1 (db2_eta_nonneg n _)
        · rw [db2_eta_zero n (not_lt.1 hlt)]
          simp
    _ = C * (db1_bump d n).rOut := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun z => db2_eta (d := d) n z) volume x,
          db2_eta_integral, mul_one]

theorem sb1_eta_l1 (x : Euc d) (n : ℕ) : ∫ y, |db2_eta (d := d) n (x - y)| = 1 := by
  have : (fun y => |db2_eta (d := d) n (x - y)|) = fun y => db2_eta (d := d) n (x - y) :=
    funext fun y => abs_of_nonneg (db2_eta_nonneg n _)
  rw [this, integral_sub_left_eq_self (fun z => db2_eta (d := d) n z) volume x, db2_eta_integral]

variable {D : Whole.WholeDyn d} {T C B : ℝ} {ρ : ℝ → Euc d → ℝ}

/-- Sup-norm Lipschitz continuity in time. -/
theorem sb1_rho_lip_time (H : Sb1Traj D T C B ρ) (x : Euc d) {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) T)
    (hb : b ∈ Set.Icc (0 : ℝ) T) : |ρ b x - ρ a x| ≤ H.KA * |b - a| := by
  have hT : 0 ≤ T := ha.1.trans ha.2
  -- pairings are Lipschitz in time
  have hpair : ∀ n : ℕ, ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) T → b ∈ Set.Icc (0 : ℝ) T → a ≤ b →
      |Whole.pair (Whole.withDensityReal (ρ b)) (fun y => db2_eta (d := d) n (x - y)) -
        Whole.pair (Whole.withDensityReal (ρ a)) (fun y => db2_eta (d := d) n (x - y))| ≤
        H.KA * |b - a| := by
    intro n a b ha hb hab
    have ht := sb1_bump_test n x
    obtain ⟨-, hw⟩ := sb1_weak_interval H ht.1 ht.2
    have hbd := sb1_gen_bound H ht.1 ht.2
    have hw' : Whole.pair (Whole.withDensityReal (ρ b)) (fun y => db2_eta (d := d) n (x - y)) -
        Whole.pair (Whole.withDensityReal (ρ a)) (fun y => db2_eta (d := d) n (x - y)) =
        ∫ r in a..b, mfGen D (fun y => db2_eta (d := d) n (x - y)) (ρ r) := hw a b ha.1 hab hb.2
    rw [hw', ← Real.norm_eq_abs]
    have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := H.KA)
      (f := fun r => mfGen D (fun y => db2_eta (d := d) n (x - y)) (ρ r)) (fun r hr => by
        rw [Set.uIoc_of_le hab] at hr
        rw [Real.norm_eq_abs]
        have := hbd r ⟨ha.1.trans hr.1.le, hr.2.trans hb.2⟩
        have e : ∫ y, |((db1_bump d n).normed volume) (x - y)| = 1 := sb1_eta_l1 x n
        rw [e, mul_one] at this
        exact this)
    exact key
  have hlim : ∀ n : ℕ, |ρ b x - ρ a x| ≤ 2 * (C * (db1_bump d n).rOut) + H.KA * |b - a| := by
    intro n
    have e1 := sb1_pair_approx (H.slice b hb) x n
    have e2 := sb1_pair_approx (H.slice a ha) x n
    have e3 : |Whole.pair (Whole.withDensityReal (ρ b)) (fun y => db2_eta (d := d) n (x - y)) -
        Whole.pair (Whole.withDensityReal (ρ a)) (fun y => db2_eta (d := d) n (x - y))| ≤
        H.KA * |b - a| := by
      rcases le_total a b with hab | hab
      · exact hpair n a b ha hb hab
      · have := hpair n b a hb ha hab
        rwa [abs_sub_comm, abs_sub_comm b a]
    set Pb := Whole.pair (Whole.withDensityReal (ρ b)) (fun y => db2_eta (d := d) n (x - y))
    set Pa := Whole.pair (Whole.withDensityReal (ρ a)) (fun y => db2_eta (d := d) n (x - y))
    have : ρ b x - ρ a x = (ρ b x - Pb) + (Pb - Pa) + (Pa - ρ a x) := by ring
    rw [this]
    calc |(ρ b x - Pb) + (Pb - Pa) + (Pa - ρ a x)| ≤ |ρ b x - Pb| + |Pb - Pa| + |Pa - ρ a x| := by
          refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ C * (db1_bump d n).rOut + H.KA * |b - a| + C * (db1_bump d n).rOut := by
          refine add_le_add (add_le_add ?_ e3) ?_
          · rw [abs_sub_comm]; exact e1
          · exact e2
      _ = _ := by ring
  have hlim' : Tendsto (fun n : ℕ => 2 * (C * (db1_bump d n).rOut) + H.KA * |b - a|) atTop
      (𝓝 (2 * (C * 0) + H.KA * |b - a|)) :=
    (((db1_bump_tendsto (d := d)).const_mul C).const_mul 2).add_const _
  have := ge_of_tendsto' hlim' hlim
  simpa using this


theorem sb1_slice_D23 {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (y : Euc d) :
    ‖iteratedFDeriv ℝ 2 h y‖ ≤ C ∧ ‖iteratedFDeriv ℝ 3 h y‖ ≤ C := by
  have hw : (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  exact ⟨(S.decay.2 2 (by norm_num) y).trans (mul_le_of_le_one_right S.C_nonneg hw),
    (S.decay.2 3 le_rfl y).trans (mul_le_of_le_one_right S.C_nonneg hw)⟩

/-- `C²`-continuity of the trajectory in time, uniform in space. -/
theorem sb1_rho_C2_time (H : Sb1Traj D T C B ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ Set.Icc (0 : ℝ) T, ∀ b ∈ Set.Icc (0 : ℝ) T, |b - a| < δ → ∀ x : Euc d,
      ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j (ρ b) x - iteratedFDeriv ℝ j (ρ a) x‖ ≤ ε := by
  have hC := H.hC
  have hKA := H.KA_nonneg
  set h₀ : ℝ := ε / (2 * (8 * C + 1)) with hh₀
  have hh₀pos : 0 < h₀ := by positivity
  set δ₀ : ℝ := min (min (ε * h₀ / 4) (ε * h₀ ^ 2 / 8)) ε with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (lt_min (by positivity) (by positivity)) hε
  refine ⟨δ₀ / (H.KA + 1), by positivity, ?_⟩
  intro a ha b hb hab x j hj
  have hsup : ∀ y, |(ρ b - ρ a) y| ≤ δ₀ := fun y => by
    refine (sb1_rho_lip_time H y ha hb).trans ?_
    calc H.KA * |b - a| ≤ H.KA * (δ₀ / (H.KA + 1)) := mul_le_mul_of_nonneg_left hab.le hKA
      _ ≤ δ₀ := by
          rw [mul_div_assoc']
          exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have hSb := H.slice b hb
  have hSa := H.slice a ha
  have hfC : ContDiff ℝ 3 (ρ b - ρ a) := hSb.decay.1.sub hSa.decay.1
  have hsub : ∀ n : ℕ, n ≤ 3 → ∀ y, iteratedFDeriv ℝ n (ρ b - ρ a) y =
      iteratedFDeriv ℝ n (ρ b) y - iteratedFDeriv ℝ n (ρ a) y := fun n hn y =>
    iteratedFDeriv_sub_apply (hSb.decay.1.contDiffAt.of_le (by exact_mod_cast hn))
      (hSa.decay.1.contDiffAt.of_le (by exact_mod_cast hn))
  have hD2 : ∀ y, ‖iteratedFDeriv ℝ 2 (ρ b - ρ a) y‖ ≤ 2 * C := fun y => by
    rw [hsub 2 (by norm_num)]
    calc _ ≤ ‖iteratedFDeriv ℝ 2 (ρ b) y‖ + ‖iteratedFDeriv ℝ 2 (ρ a) y‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (sb1_slice_D23 hSb y).1 (sb1_slice_D23 hSa y).1
      _ = 2 * C := by ring
  have hD3 : ∀ y, ‖iteratedFDeriv ℝ 3 (ρ b - ρ a) y‖ ≤ 2 * C := fun y => by
    rw [hsub 3 le_rfl]
    calc _ ≤ ‖iteratedFDeriv ℝ 3 (ρ b) y‖ + ‖iteratedFDeriv ℝ 3 (ρ a) y‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (sb1_slice_D23 hSb y).2 (sb1_slice_D23 hSa y).2
      _ = 2 * C := by ring
  have e1 := sb1_lk_first (hfC.of_le (by norm_num)) hh₀pos hsup hD2 x
  have e2 := sb1_lk_second hfC hh₀pos hsup hD3 x
  have hCh : C * h₀ ≤ ε / 16 := by
    rw [hh₀, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hd1 : δ₀ ≤ ε * h₀ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : δ₀ ≤ ε * h₀ ^ 2 / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : δ₀ ≤ ε := min_le_right _ _
  have t1 : 2 * δ₀ / h₀ ≤ ε / 2 := by
    rw [div_le_iff₀ hh₀pos]; nlinarith
  have t2 : 4 * δ₀ / h₀ ^ 2 ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rw [← hsub j (by omega)]
  interval_cases j
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact (hsup x).trans hd3
  · rw [norm_iteratedFDeriv_one]
    refine e1.trans ?_
    nlinarith
  · refine e2.trans ?_
    nlinarith

theorem sb1_rho_C1_time (H : Sb1Traj D T C B ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ Set.Icc (0 : ℝ) T, ∀ b ∈ Set.Icc (0 : ℝ) T, |b - a| < δ → ∀ x : Euc d,
      ‖fderiv ℝ (ρ b) x - fderiv ℝ (ρ a) x‖ ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := sb1_rho_C2_time H hε
  refine ⟨δ, hδ, fun a ha b hb hab x => ?_⟩
  have := h a ha b hb hab x 1 (by norm_num)
  have e : iteratedFDeriv ℝ 1 (ρ b) x - iteratedFDeriv ℝ 1 (ρ a) x = iteratedFDeriv ℝ 1 (ρ b - ρ a) x :=
    (iteratedFDeriv_sub_apply ((H.slice b hb).decay.1.contDiffAt.of_le (by norm_num))
      ((H.slice a ha).decay.1.contDiffAt.of_le (by norm_num))).symm
  rw [e, norm_iteratedFDeriv_one,
    fderiv_sub ((H.slice b hb).decay.1.differentiable (by norm_num) x)
      ((H.slice a ha).decay.1.differentiable (by norm_num) x)] at this
  exact this

end HRS.MS.MfeConf
