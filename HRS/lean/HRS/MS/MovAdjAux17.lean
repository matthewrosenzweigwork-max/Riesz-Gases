import HRS.MS.MovAdjAux16

/-!
# S6.7 (packet P4, part 3): the truncated Duhamel formula

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_duhamel_n`: `hs_duhamel` applied to the truncations `(s67v, s67a', s67F)` of `S67DuhData`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB HRS.MS.PoisSg

universe u'

variable {d : ℕ} {q : ℝ} {B : Euc d → Euc d} {T : ℝ} {u a S : ℝ → Euc d → ℝ}

theorem S67DuhData.v_eq (T : ℝ) (u : ℝ → Euc d → ℝ) (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    s67v T u n s = fun y => hsCut n y * u s y := by
  funext y
  unfold s67v
  rw [clampT_of_mem hs]

theorem S67DuhData.v_hv2 (h : S67DuhData q B T u a S) (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ 2 (s67v T u n s) ∧ ∃ M1 M2 : ℝ, (∀ y, ‖fderiv ℝ (s67v T u n s) y‖ ≤ M1) ∧
      ∀ y, ‖iteratedFDeriv ℝ 2 (s67v T u n s) y‖ ≤ M2 := by
  rw [S67DuhData.v_eq T u n hs]
  have hc : ContDiff ℝ 2 (fun y => hsCut (d := d) n y * u s y) :=
    ((hs_cut_contDiff (d := d) n).of_le (by simp)).mul (h.c2 s hs)
  have hcs : HasCompactSupport (fun y => hsCut (d := d) n y * u s y) :=
    (hs_cut_support (d := d) n).mul_right
  refine ⟨hc, ?_⟩
  obtain ⟨M1, hM1⟩ := (hcs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hc.continuous_fderiv (by norm_num))
  obtain ⟨M2, hM2⟩ := (hcs.iteratedFDeriv (𝕜 := ℝ) 2).exists_bound_of_continuous
    (hc.continuous_iteratedFDeriv (m := 2) le_rfl)
  exact ⟨M1, M2, hM1, hM2⟩

theorem S67DuhData.v_hint (h : S67DuhData q B T u a S) (n : ℕ) {s s0 : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hs0 : s0 ∈ Icc (0 : ℝ) T) (y : Euc d) :
    s67v T u n s y - s67v T u n s0 y = ∫ r in s0..s, s67a' T a n r y := by
  have hsub : uIcc s0 s ⊆ Icc (0 : ℝ) T := by
    intro r hr
    rw [mem_uIcc] at hr
    rcases hr with hr | hr
    · exact ⟨hs0.1.trans hr.1, hr.2.trans hs.2⟩
    · exact ⟨hs.1.trans hr.1, hr.2.trans hs0.2⟩
  have e : ∀ r ∈ uIcc s0 s, s67a' T a n r y = hsCut n y * a r y := by
    intro r hr
    unfold s67a'
    rw [clampT_of_mem (hsub hr)]
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul, ← h.hint s hs s0 hs0 y]
  rw [S67DuhData.v_eq T u n hs, S67DuhData.v_eq T u n hs0]
  ring

theorem S67DuhData.v_hL (h : S67DuhData q B T u a S) (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (y : Euc d) :
    kolmL q B (s67v T u n s) y = s67a' T a n s y - s67F q B T u S n s y := by
  rw [S67DuhData.v_eq T u n hs]
  have hχ2 : ContDiff ℝ 2 (hsCut (d := d) n) := (hs_cut_contDiff (d := d) n).of_le (by simp)
  have hprod := s67_kolmL_mul (q := q) (B := B) hχ2 (h.c2 s hs) y
  have hL := h.hL s hs y
  have hcl : clampT T s = s := clampT_of_mem hs
  unfold s67a' s67F
  rw [hcl]
  have hin : inner ℝ (gradient (hsCut n) y) (gradient (u s) y) = fderiv ℝ (u s) y (gradient (hsCut n) y) :=
    kl_inner_gradient (u s) y _
  rw [hprod, hin]
  have : kolmL q B (u s) y = a s y - S s y := by linarith
  rw [this]
  ring

universe w

set_option maxHeartbeats 1600000 in
theorem s67_duhamel_n {Ω : Type w} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W)
    {Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) (hBm : HasCbBound m Mb B)
    (h : S67DuhData q B T u a S) (hT : 0 < T) (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Euc d) :
    s67v T u n t x = sg P W q B t (s67v T u n 0) x +
      ∫ s in (0 : ℝ)..t, sg P W q B (t - s) (s67F q B T u S n s) x := by
  have hT0 : 0 ≤ T := hT.le
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hBm.2 0 (Nat.zero_le _) y
  obtain ⟨K0, hK0⟩ := h.v_bound hT0
  obtain ⟨Ka', hKa'⟩ := h.a_bound hT0 n
  obtain ⟨KF, hKF⟩ := h.F_bound hT0 hBb
  exact hs_duhamel hW hq hm hBm hT (v := s67v T u n) (a := s67a' T a n) (F := s67F q B T u S n)
    (h.v_cont hT0 n) (h.a_cont hT0 n) (h.F_cont hT0 hBm.1.continuous n)
    (Kv := K0) (Ka := Ka') (KF := KF) (fun r y => hK0 n r y) (fun r y => hKa' r y) (fun r y => hKF n r y)
    (fun s hs => h.v_hv2 n hs) (fun s hs s0 hs0 y => h.v_hint n hs hs0 y)
    (fun s hs y => h.v_hL n hs y) ht x

end HRS.MS.MovAdj
