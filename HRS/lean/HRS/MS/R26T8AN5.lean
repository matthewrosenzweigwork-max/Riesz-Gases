import HRS.MS.R26T8AN4
import HRS.MS.R26T8AN0
import HRS.MS.R26T8AP06tb
import HRS.MS.R26T8AP07

/-!
# S8.2 local Newton layer, packet T8A.P07, case `sigma < 0` (Taylor split)
`r26t8a_raw_newton_smooth_conormal`: the raw Newton integral of a smooth pair function with bounded jets is conormal (any order).
`r26t8a_raw_newton_bound_neg`: for `sigma < 0`, `m < -sigma <= m+1`: `Conormal (k+1+m+1) b M sigma A F` implies integrability and
`Conormal k (b+1) M (sigma-2) (C*A) (rawNewton nu chi F)`  (regularity as in S82PB's contract-defect note; NOT the contract verbatim).
`r26t8a_raw_newton_bound_full`: both signs, hypothesis `Conormal (r26t8a_gainReg k sigma) b M sigma A F`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_N5_rawNewton_contDiff (hd : 2 ≤ d) (k : ℕ) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    {P : Euc d → Euc d → ℝ} (hP : ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry P)) :
    ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry (rawNewton nu chi P)) := by
  have hL : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2)) :=
    (contDiff_fst.add (contDiff_snd.const_smul _)).prodMk (contDiff_fst.sub (contDiff_snd.const_smul _))
  have hMid : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) := hP.comp hL
  have hSc : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => chi Yw.2 * midPair P Yw.1 Yw.2) :=
    ((contDiff_infty.1 hchi.1 k).comp contDiff_snd).mul hMid
  have hSv : ∀ Y w : Euc d, 2 < ‖w‖ → chi w * midPair P Y w = 0 := fun Y w hw => by
    rw [hchi.2.2.2.2 w hw.le, zero_mul]
  have hNc : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d =>
      ∫ u, newtonKernel d nu u * (chi (Yw.2 - u) * midPair P Yw.1 (Yw.2 - u))) :=
    r26t8a_N1_conv_contDiff (r26t8a_N2_locInt fun r => r26t8a_K_integrableOn hd nu r) hSc 2 hSv
  have hΦ : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => chi Yw.2 *
      ∫ u, newtonKernel d nu u * (chi (Yw.2 - u) * midPair P Yw.1 (Yw.2 - u))) :=
    ((contDiff_infty.1 hchi.1 k).comp contDiff_snd).mul hNc
  have hL2 : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ((1 / 2 : ℝ) • (p.1 + p.2), p.1 - p.2)) :=
    (((contDiff_fst.add contDiff_snd).const_smul _)).prodMk (contDiff_fst.sub contDiff_snd)
  have hmid : ∀ p : Euc d × Euc d, rawNewton nu chi P p.1 p.2 =
      chi (p.1 - p.2) * ∫ u, newtonKernel d nu u *
        (chi ((p.1 - p.2) - u) * midPair P ((1 / 2 : ℝ) • (p.1 + p.2)) ((p.1 - p.2) - u)) := by
    intro p
    have e1 : (1 / 2 : ℝ) • (p.1 + p.2) + (1 / 2 : ℝ) • (p.1 - p.2) = p.1 := by module
    have e2 : (1 / 2 : ℝ) • (p.1 + p.2) - (1 / 2 : ℝ) • (p.1 - p.2) = p.2 := by module
    have hdef : rawNewton nu chi P p.1 p.2 = midPair (rawNewton nu chi P) ((1 / 2 : ℝ) • (p.1 + p.2)) (p.1 - p.2) := by
      unfold midPair; rw [e1, e2]
    rw [hdef, r26t8a_N4_mid_eq]
  have hfun : Function.uncurry (rawNewton nu chi P) = fun p : Euc d × Euc d =>
      chi (p.1 - p.2) * ∫ u, newtonKernel d nu u *
        (chi ((p.1 - p.2) - u) * midPair P ((1 / 2 : ℝ) • (p.1 + p.2)) ((p.1 - p.2) - u)) := funext hmid
  rw [hfun]
  exact hΦ.comp hL2

theorem r26t8a_N5_integrable (hd : 2 ≤ d) (nu : ℝ) {g : Euc d → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g)
    (w : Euc d) : Integrable (fun z => newtonKernel d nu (w - z) * g z) := by
  have hloc := r26t8a_N2_locInt (fun r => r26t8a_K_integrableOn hd nu r)
  have hcont : Continuous (fun u : Euc d => g (w - u)) := hg.comp (continuous_const.sub continuous_id)
  have hcs' : HasCompactSupport (fun u : Euc d => g (w - u)) := hcs.comp_homeomorph (Homeomorph.subLeft w)
  have h1 : Integrable (fun u => newtonKernel d nu u * g (w - u)) :=
    hloc.integrable_smul_right_of_hasCompactSupport hcont hcs'
  have h2 := h1.comp_sub_left w
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [sub_sub_cancel]

theorem r26t8a_raw_newton_bound_neg (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (nu M sigma : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M)
    (hσ : sigma < 0) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (m : ℕ) (hm : (m : ℝ) < -sigma)
    (hm1 : -sigma ≤ (m : ℝ) + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal (k + 1 + m + 1) b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
        midPair F ((1 / 2 : ℝ) • (x + y)) z)) ∧
      Conormal k (b + 1) M (sigma - 2) (C * A) (rawNewton nu chi F) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hσd : sigma < d := lt_trans hσ hd0
  obtain ⟨Ct, hCt0, hCt⟩ := r26t8a_taylor_split hd hchi k b M sigma hM hσ m hm hm1
  obtain ⟨Cg, hCg0, hCg⟩ := r26t8a_raw_newton_boundP d hd k b nu M sigma hnu hM hσd chi hchi
  obtain ⟨Cq, hCq0, hCq⟩ := r26t8a_rawNewton_smooth_jets hd k nu M hM hchi
  refine ⟨(Cg + Cq) * Ct, by positivity, ?_⟩
  intro F A hA hF
  obtain ⟨P, hPcd, hFP, hPjet⟩ := hCt A hA F hF
  have hA1 : 0 ≤ Ct * A := mul_nonneg hCt0 hA
  have hpw0 : ∀ X z : Euc d, 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := fun X z =>
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hPcd' : ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry P) := hPcd.of_le (by exact_mod_cast Nat.le_succ k)
  obtain ⟨hint1, hCon1⟩ := hCg (fun x y => F x y - P x y) (Ct * A) hA1 hFP
  have hLPsm := r26t8a_N5_rawNewton_contDiff hd k nu hchi hPcd'
  have hLP : Conormal k (b + 1) M (sigma - 2) (Cq * (Ct * A)) (rawNewton nu chi P) := by
    refine And.intro hLPsm.contDiffOn fun p q hpq X z hz => ?_
    have h := hCq (Ct * A) hA1 P hPcd' hPjet p q hpq X z
    show ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (rawNewton nu chi P) Yw.1 Yw.2) X z‖ ≤ _
    refine h.trans ?_
    have h0 : 0 ≤ Cq * (Ct * A) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
      have := hpw0 X z; positivity
    have h1 : 0 ≤ (min 1 ‖z‖) ^ (-((sigma - 2) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1) := by
      have : 0 ≤ min 1 ‖z‖ := le_min zero_le_one (norm_nonneg _)
      positivity
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + (min 1 ‖z‖) ^ (-((sigma - 2) + (q : ℝ))) *
      (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1) by linarith) h0
    calc _ = Cq * (Ct * A) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * 1 := by ring
      _ ≤ _ := this
  have hintP : ∀ x y : Euc d, Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
      midPair P ((1 / 2 : ℝ) • (x + y)) z) := by
    intro x y
    have hg : Continuous (fun z : Euc d => chi z * midPair P ((1 / 2 : ℝ) • (x + y)) z) := by
      refine hchi.1.continuous.mul ?_
      unfold midPair
      have hcz : Continuous (fun z : Euc d => ((1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • z,
          (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • z)) := by fun_prop
      exact hPcd'.continuous.comp hcz
    have hcs : HasCompactSupport (fun z : Euc d => chi z * midPair P ((1 / 2 : ℝ) • (x + y)) z) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) (fun z hz => ?_)
      have : 2 < ‖z‖ := by simpa using hz
      simp [hchi.2.2.2.2 z this.le]
    have := r26t8a_N5_integrable hd nu hg hcs (x - y)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [mul_assoc]
  have hsum := r26t8a_N0_conormal_add hchi hCon1 hLP
  have hAeq : Cg * (Ct * A) + Cq * (Ct * A) = (Cg + Cq) * Ct * A := by ring
  rw [hAeq] at hsum
  have hlin : ∀ x y : Euc d, x ≠ y → rawNewton nu chi F x y =
      rawNewton nu chi (fun x y => F x y - P x y) x y + rawNewton nu chi P x y := by
    intro x y hxy
    unfold rawNewton
    rw [← mul_add, ← integral_add (hint1 x y hxy) (hintP x y)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [midPair]
    ring
  refine ⟨fun x y hxy => ?_, ?_⟩
  · have := (hint1 x y hxy).add (hintP x y)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, midPair]
    ring
  · exact r26t8a_N0_conormal_congr (fun x y hxy => (hlin x y hxy).symm) hsum

/-- Regularity needed for the raw Newton gain at order `sigma`. -/
def r26t8a_rawGainReg (k : ℕ) (σ : ℝ) : ℕ := if 0 ≤ σ then k else k + 1 + (⌈-σ⌉₊ - 1) + 1

theorem r26t8a_raw_newton_bound_full (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (nu M sigma : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M)
    (hsd : sigma < d) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal (r26t8a_rawGainReg k sigma) b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
        midPair F ((1 / 2 : ℝ) • (x + y)) z)) ∧
      Conormal k (b + 1) M (sigma - 2) (C * A) (rawNewton nu chi F) := by
  by_cases hσ : 0 ≤ sigma
  · obtain ⟨C, hC0, hC⟩ := r26t8a_raw_newton_bound_nonneg d hd k b nu M sigma hnu hM hσ hsd chi hchi
    refine ⟨C, hC0, fun F A hA hF => hC F A hA ?_⟩
    simpa only [r26t8a_rawGainReg, if_pos hσ] using hF
  · push Not at hσ
    set s : ℝ := -sigma with hs
    have hs0 : 0 < s := by rw [hs]; linarith
    have hceil : 1 ≤ ⌈s⌉₊ := Nat.one_le_iff_ne_zero.2 (by simpa using hs0)
    have hm : ((⌈s⌉₊ - 1 : ℕ) : ℝ) < -sigma := by
      rw [Nat.cast_sub hceil]
      have := Nat.ceil_lt_add_one hs0.le
      push_cast
      linarith
    have hm1 : -sigma ≤ ((⌈s⌉₊ - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hceil]
      have := Nat.le_ceil s
      push_cast
      linarith
    obtain ⟨C, hC0, hC⟩ := r26t8a_raw_newton_bound_neg d hd k b nu M sigma hnu hM hσ chi hchi (⌈s⌉₊ - 1) hm hm1
    refine ⟨C, hC0, fun F A hA hF => hC F A hA ?_⟩
    have : r26t8a_rawGainReg k sigma = k + 1 + (⌈s⌉₊ - 1) + 1 := by
      simp only [r26t8a_rawGainReg, if_neg (not_le.2 hσ), hs]
    rw [this] at hF
    exact hF

end HRS.MS.R26T8A
