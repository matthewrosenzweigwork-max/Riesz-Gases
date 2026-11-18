import HRS.MS.SA12X2X

/-!
# S.A.12 N8 (SA12X2), part Y: the tuple bound for skew `M`, `d - 1 < s < d`
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_tv_reg {m : ℕ} {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a)
    (hac : HasCompactSupport a) (hF : ContDiff ℝ ∞ F) (j : Fin d) (τ : SA12X2Term d)
    (hτ : τ.r + 1 ≤ m) :
    ContDiff ℝ 1 (sa12x2_tv a F j τ) ∧ HasCompactSupport (sa12x2_tv a F j τ) := by
  have hDa : ContDiff ℝ m (D1 τ.l a) :=
    (ha.fderiv_right (m := m) (by push_cast; rfl)).clm_apply contDiff_const
  have hG : ContDiff ℝ ∞ (partialDeriv τ.t F) := sa12z3_pd_contDiff_inf hF τ.t
  have hK : ContDiff ℝ m (D1 j (partialDeriv τ.t F)) :=
    sa12z3_cd_of_inf ((hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) m
  have hP : ContDiff ℝ m (fun z => D1 τ.l a z * D1 j (partialDeriv τ.t F) z) := hDa.mul hK
  have hPc : HasCompactSupport (fun z => D1 τ.l a z * D1 j (partialDeriv τ.t F) z) :=
    (D1_supp hac τ.l).mul_right
  refine ⟨?_, sa12z3_pd_compact hPc τ.σ⟩
  have := sa12z3_pd_contDiff (k := m) (n := τ.r) hP (by omega) τ.σ
  exact this.of_le (by exact_mod_cast (by omega : 1 ≤ m - τ.r))


theorem sa12x2_idx_hard (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    (m : ℕ) (hm : 1 ≤ m) (MB Ka Kw Ke Kp R : ℝ) (hKa : 0 ≤ Ka) (hKw : 0 ≤ Kw) (hKe : 0 ≤ Ke)
    (hKp : 0 ≤ Kp) (hR : 1 ≤ R) :
    ∃ A2 : ℝ, 0 ≤ A2 ∧ ∀ (c0 : Euc d) (om η a μ W F : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
      (∀ i j, |M i j| ≤ MB) → Torus.symPart M = 0 →
      ContDiff ℝ 2 om → HasCompactSupport om → (∀ x, |om x| ≤ 1) →
      (∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k om x‖ ≤ Kw) → Function.support om ⊆ closedBall c0 R →
      ContDiff ℝ 2 η → HasCompactSupport η → Function.support η ⊆ closedBall c0 R → (∀ x, η x ≤ 1) →
      (∀ k ≤ 1, ∀ x, ‖iteratedFDeriv ℝ k η x‖ ≤ Ke) →
      (∀ x, om x ≠ 0 → η x = 1) → (∀ x ∈ tsupport a, η x = 1) →
      Continuous W → HasCompactSupport W → (∀ y, 0 ≤ W y) → (∀ y ∈ tsupport om, 1 ≤ W y) →
      (∀ y ∈ tsupport η, 1 ≤ W y) →
      ContDiff ℝ (m + 1) a → Function.support a ⊆ closedBall c0 R →
      (∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka) →
      ContDiff ℝ 3 μ → (∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k μ x‖ ≤ Kp) →
      (∀ l x, om x ^ 2 * D1 l a x = om x ^ 2 * D1 l μ x) → ContDiff ℝ ∞ F →
      ∀ (n : ℕ), n ≤ m → ∀ (idx : Fin n → Fin d),
        -(∫ x, om x ^ 2 * (partialDeriv idx F x * partialDeriv idx (eucNonlocal s M a F) x)) ≤
          A2 * ∫ x, W x * sa12z3_Y m F x := by
  obtain ⟨K2, hK20, hK2⟩ := sa12x2_T2 hd hs0 hsd R (2 * Ka) Ka (3 * Kw) hR (by positivity) hKa
    (by positivity)
  obtain ⟨Kt, hKt0, hKt⟩ := sa12x2_term hd hs0 hsd hs1 m Ka Kw Ke Kp R hKa hKw hKe hKp hR
  set cT := sa12z3_cT d m with hcT
  have hcT0 : 0 ≤ cT := sa12z3_cT_nonneg d m
  set MB' : ℝ := max MB 0 with hMB'
  have hMB0 : 0 ≤ MB' := le_max_right _ _
  refine ⟨(d : ℝ) * d * MB' * (K2 * cT + m * Kt), by positivity, ?_⟩
  intro c0 om η a μ W F M hM hsk hom homc hom1 hKwb homs hη hηc hηs hηle hηb hηom hηa hW hWcs hW0
    hWo hWη ha hasup hKab hμ hμb hamu hF n hn idx
  have hac : HasCompactSupport a :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hasup
  have ha2 : ContDiff ℝ 2 a := ha.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hu_inf : ContDiff ℝ ∞ (partialDeriv idx F) := sa12z3_pd_contDiff_inf hF idx
  have hu2 : ContDiff ℝ 2 (partialDeriv idx F) := sa12z3_cd_of_inf hu_inf 2
  set u : Euc d → ℝ := partialDeriv idx F with hu
  have he0 : 0 ≤ ∫ x, W x * sa12z3_Y m F x :=
    integral_nonneg fun x => mul_nonneg (hW0 x) (sa12z3_Y_nonneg _ _ _)
  set e : ℝ := ∫ x, W x * sa12z3_Y m F x with he
  have hdec := sa12x2_decomp hs0 hsd hm hsk ha hac hF hom.continuous homc hn idx
  rw [hdec]
  -- the pointwise bound of `u`
  have hKt' : ∀ y, 0 ≤ sa12z3_T m F y := fun y => sa12z3_T_nonneg m F y
  have hu0 : ∀ y, |u y| ≤ sa12z3_T m F y := fun y =>
    (sa12z3_pd_le_norm _ y idx).trans (sa12x2_iter_le_T _ hn y)
  have hWa : ∀ y ∈ tsupport a, 1 ≤ W y := fun y hy =>
    hWη y (subset_tsupport η (fun h0 => by have := hηa y hy; rw [h0] at this; exact zero_ne_one this))
  -- the first-order term
  have hDja : ∀ j, ContDiff ℝ 1 (D1 j a) := fun j => D1_contDiff ha2 j
  have hDjs : ∀ j y, D1 j a y ≠ 0 → y ∈ tsupport a := fun j y hy => by
    have : fderiv ℝ a y ≠ 0 := fun h0 => hy (by simp [D1, h0])
    exact support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 this)
  have hDjb : ∀ j y, |D1 j a y| ≤ Ka := fun j y => by
    refine (sa12z3_D1_le j a y).trans ?_
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact hKab 1 (by omega) y
  have hA : ∀ j i : Fin d, |∫ x, om x ^ 2 * (u x * firstRiesz d s i (fun y => D1 j a y * u y) x)| ≤
      K2 * (cT * e) := by
    intro j i
    have hcbom : cbNorm 2 om ≤ 3 * Kw := by
      refine (sa12x2_cb_le hKwb).trans (le_of_eq ?_); push_cast; ring
    have hbm : MemCb 1 (D1 j a) := sa12z3_memCb_of_cc (hDja j) (D1_supp hac j)
    have hbn : cbNorm 1 (D1 j a) ≤ 2 * Ka := by
      refine (sa12x2_cb_le (K := Ka) (fun k hk x => ?_)).trans (le_of_eq ?_)
      · exact (sa12x2_norm_D1' (k := k) (ha.of_le (by exact_mod_cast (by omega : k + 1 ≤ m + 1))) j x).trans
          (hKab (k + 1) (by omega) x)
      · push_cast; ring
    have hbs : Function.support (D1 j a) ⊆ closedBall c0 R := fun y hy =>
      (closure_minimal hasup isClosed_closedBall) (hDjs j y (Function.mem_support.1 hy))
    have g1 := sa12x2_wl2 (m := m) (K := 1) hW hWcs hF (hom.continuous.mul hu2.continuous)
      (homc.mul_right) (fun y hy => hWo y (subset_tsupport om (left_ne_zero_of_mul hy)))
      (fun y => by
        show |om y * u y| ≤ 1 * sa12z3_T m F y
        rw [abs_mul, one_mul]
        have := mul_le_mul (hom1 y) (hu0 y) (abs_nonneg _) zero_le_one
        linarith) hW0
    have g2 := sa12x2_wl2 (m := m) (K := Ka) hW hWcs hF ((hDja j).continuous.mul hu2.continuous)
      ((D1_supp hac j).mul_right) (fun y hy => hWa y (hDjs j y (left_ne_zero_of_mul hy)))
      (fun y => by
        show |D1 j a y * u y| ≤ Ka * sa12z3_T m F y
        rw [abs_mul]
        have := mul_le_mul (hDjb j y) (hu0 y) (abs_nonneg _) hKa
        linarith) hW0
    exact hK2 c0 om (D1 j a) u i (cT * e) (sa12z3_memCb_of_cc hom homc) hcbom homc homs hbm hbn hbs
      hu2 (by positivity) (by simpa using g1)
      (by simpa [mul_assoc] using g2)
  -- the remainder
  have hB : ∀ j i : Fin d, |∫ x, om x ^ 2 * (u x * firstRiesz d s i (sa12z3_Rj a F idx j) x)| ≤
      m * Kt * e := by
    intro j i
    obtain ⟨L, hlen, hrs, hF2, hR⟩ := sa12x2_tel ha hF j n hn idx
    have hfun : sa12z3_Rj a F idx j = fun y => (L.map (fun τ => sa12x2_tv a F j τ y)).sum :=
      funext hR
    rw [hfun]
    have hreg := fun τ (hτ : τ ∈ L) => sa12x2_tv_reg ha hac hF j τ (by have := hrs τ hτ; omega)
    have hlist := sa12x2_list_bound hs0 hsd i (w := fun x => om x ^ 2 * u x)
      ((hom.continuous.pow 2).mul hu2.continuous)
      ((homc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right)
      (fun τ => sa12x2_tv a F j τ) (Kt * e) L (fun τ hτ => (hreg τ hτ).1)
      (fun τ hτ => (hreg τ hτ).2) (fun τ hτ => by
        have hτ' := hrs τ hτ
        have hl := hKt c0 om η a μ W F i τ.l j τ.r τ.s τ.σ τ.t (by omega) hom homc hom1 hKwb homs hη
          hηc hηs hηle hηb hηom hηa hW hWcs hW0 hWo hWη ha hasup hKab hμ hμb (hamu τ.l) hF
        have hueq : ∀ x, u x = D1 τ.l (partialDeriv τ.σ (partialDeriv τ.t F)) x := fun x => by
          rw [hu, hF2 τ hτ x]
          exact sa12z3_pd_D1_comm τ.l τ.r (partialDeriv τ.t F)
            (sa12z3_cd_of_inf (sa12z3_pd_contDiff_inf hF τ.t) _) τ.σ x
        refine le_trans (le_of_eq ?_) hl
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hueq x])
    have : ∫ x, om x ^ 2 * (u x * firstRiesz d s i (fun y => (L.map (fun τ => sa12x2_tv a F j τ y)).sum) x) =
        ∫ x, om x ^ 2 * u x * firstRiesz d s i (fun y => (L.map (fun τ => sa12x2_tv a F j τ y)).sum) x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [mul_assoc]
    rw [this]
    refine hlist.trans ?_
    rw [hlen]
    have : (n : ℝ) ≤ m := by exact_mod_cast hn
    nlinarith [mul_nonneg hKt0 he0]
  -- assembly
  have hterm : ∀ i j : Fin d, |M j i * (-(∫ x, om x ^ 2 * (u x * firstRiesz d s i (fun y => D1 j a y * u y) x)) +
      ∫ x, om x ^ 2 * (u x * firstRiesz d s i (sa12z3_Rj a F idx j) x))| ≤
      MB' * (K2 * (cT * e) + m * Kt * e) := by
    intro i j
    rw [abs_mul]
    refine mul_le_mul ((hM j i).trans (le_max_left _ _)) ?_ (abs_nonneg _) hMB0
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    exact add_le_add (hA j i) (hB j i)
  have hsum := Finset.abs_sum_le_sum_abs (fun i : Fin d => ∑ j : Fin d, M j i * (-(∫ x, om x ^ 2 *
      (u x * firstRiesz d s i (fun y => D1 j a y * u y) x)) +
      ∫ x, om x ^ 2 * (u x * firstRiesz d s i (sa12z3_Rj a F idx j) x))) Finset.univ
  have hin : ∀ i : Fin d, |∑ j : Fin d, M j i * (-(∫ x, om x ^ 2 *
      (u x * firstRiesz d s i (fun y => D1 j a y * u y) x)) +
      ∫ x, om x ^ 2 * (u x * firstRiesz d s i (sa12z3_Rj a F idx j) x))| ≤
      d * (MB' * (K2 * (cT * e) + m * Kt * e)) := fun i =>
    (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum fun j _ => hterm i j).trans (by
      simp)
  refine (neg_le_abs _).trans ((hsum.trans (Finset.sum_le_sum fun i _ => hin i)).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end HRS.MH.AdjointRd.Phase2SA12Near
