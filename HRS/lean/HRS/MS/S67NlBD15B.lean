import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD15A
import HRS.MS.S67NlBD15E

/-!
# S6.7 nonlinear, packet S6.7nl.15B: weighted Sobolev Cauchy limit before physical identification

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4238-4245, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
`movc2_force_wt` gives the uniform bound `|Q^K F^loc_i|_{H^b} <= C |w|_{Sigma^m}` on Schwartz maps
(`b = m - movA`); the profile is linear on Schwartz differences, so the profiles of a
`Sigma^m`-Cauchy sequence are Cauchy in `H^b` and hence in `L^2`; the `L^2` limit `w` is completed
in `Lp`, and `s67bd_sobolev_fatou` (15E) is applied to the sequence (membership and sharp bound)
and to the tails (`H^b` convergence).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

lemma s67bd15b_L2_le {b : ℝ} (hb : 0 ≤ b) {u : Euc d → ℝ}
    (hu : HRS.PDE.ToolboxRd.MemSobolev b u) :
    (eLpNorm u 2 (volume : Measure (Euc d))).toReal ≤ s67bd_Hnorm b u := by
  have hn : 0 ≤ oscNorm 0 u := Real.sqrt_nonneg _
  rw [mn_eLpNorm_eq hu.1, ENNReal.toReal_ofReal hn, oscNorm_zero u hu.1]
  unfold s67bd_Hnorm HRS.PDE.ToolboxRd.sobolevNormSq
  refine Real.sqrt_le_sqrt ?_
  rw [← HRS.PDE.ToolboxRd.FourierAux.integral_norm_sq_fourierL2 hu.1]
  refine integral_mono (HRS.PDE.ToolboxRd.FourierAux.integrable_norm_sq_fourierL2 hu.1) hu.2
    (fun ξ => ?_)
  have h1 : 1 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b :=
    Real.one_le_rpow (by nlinarith [sq_nonneg ‖ξ‖, Real.pi_pos, sq_nonneg Real.pi]) hb
  nlinarith [sq_nonneg ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖]

lemma s67bd15b_uniform (H : Mov2dTh d s β q ρ₀) (m K : ℕ) (hm : (d : ℝ) / 2 + 7 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : SchwartzMap (Euc d) ℝ) (i : Fin d),
      HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s) (s67bd_profile d s ρ₀ w K i) ∧
      s67bd_Hnorm ((m : ℝ) - movA d s) (s67bd_profile d s ρ₀ w K i) ≤ C * oscNorm (m : ℝ) w := by
  obtain ⟨B, D⟩ := movc2_data H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (2 : ℝ) ≤ m := by linarith
  have hσ : (m : ℝ) - movA d s ≤ (m : ℝ) - 2 + ((d : ℝ) - s) := by
    have : s + 2 - d ≤ movA d s := le_max_right _ _
    linarith
  obtain ⟨C, hC, hforce⟩ := movc2_force_wt D H.hs0 H.hsd hm2 hσ K
  refine ⟨C, hC, fun w i => ?_⟩
  have h1 := ((hforce w).1 i).1
  have e : s67bd_profile d s ρ₀ w K i = fun x => (1 + ‖x‖ ^ 2) ^ K * movc2_Fl s ρ₀ w i x := rfl
  rw [e]
  exact ⟨h1.1, h1.2⟩

lemma s67bd15b_profile_sub (H : Mov2dTh d s β q ρ₀) (K : ℕ) (i : Fin d)
    (w1 w2 : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    s67bd_profile d s ρ₀ (⇑(w1 - w2)) K i x =
      s67bd_profile d s ρ₀ w1 K i x - s67bd_profile d s ρ₀ w2 K i x := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hsq1 : ContDiff ℝ 1 (fun y => Real.sqrt (ρ₀ y)) :=
    ((mnb_rhoData H).sqrt_smooth).of_le (by exact_mod_cast le_top)
  have hw : ∀ w : SchwartzMap (Euc d) ℝ, ContDiff ℝ 1 (fun y => Real.sqrt (ρ₀ y) * w y) :=
    fun w => hsq1.mul (by exact_mod_cast w.smooth 1)
  have hfun : (fun y => Real.sqrt (ρ₀ y) * (w1 - w2) y) = fun y =>
      Real.sqrt (ρ₀ y) * w1 y - Real.sqrt (ρ₀ y) * w2 y := by
    funext y; simp only [sub_apply]; ring
  have hfd : ∀ y, fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * w1 y - Real.sqrt (ρ₀ y) * w2 y) y =
      fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * w1 y) y -
        fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * w2 y) y := by
    intro y
    exact fderiv_sub (((hw w1).differentiable (by norm_num)) y) (((hw w2).differentiable (by norm_num)) y)
  unfold s67bd_profile
  rw [s67bd15a_loc_eq, s67bd15a_loc_eq, s67bd15a_loc_eq]
  simp only [sub_apply, mul_sub, hfd, ContinuousLinearMap.sub_apply]
  have hc : ∀ w : SchwartzMap (Euc d) ℝ, Continuous (fun y =>
      fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * w y) y (EuclideanSpace.single i 1)) := fun w =>
    ((hw w).continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [integral_sub (s67bd15a_conv_int hd1 H.hs0 H.hsd (hc w1) x)
    (s67bd15a_conv_int hd1 H.hs0 H.hsd (hc w2) x)]
  ring

theorem s67bd_weighted_profile_limit (H : Mov2dTh d s β q ρ₀)
    (m K : ℕ) (hm : (d : ℝ) / 2 + 7 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc d → ℝ, MemOsc (m : ℝ) v →
      ∀ vn : ℕ → SchwartzMap (Euc d) ℝ,
      Tendsto (fun n => oscNorm (m : ℝ) (fun x => vn n x - v x)) atTop (𝓝 0) →
      ∀ i : Fin d, ∃ w : Euc d → ℝ,
        HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s) w ∧
        (∀ n, HRS.PDE.ToolboxRd.MemSobolev ((m : ℝ) - movA d s)
          (s67bd_profile d s ρ₀ (vn n) K i)) ∧
        Tendsto (fun n => s67bd_Hnorm ((m : ℝ) - movA d s)
          (fun x => s67bd_profile d s ρ₀ (vn n) K i x - w x)) atTop (𝓝 0) ∧
        s67bd_Hnorm ((m : ℝ) - movA d s) w ≤ C * oscNorm (m : ℝ) v := by
  obtain ⟨C, hC0, hunif⟩ := s67bd15b_uniform H m K hm
  refine ⟨C, hC0, fun v hv vn hvn i => ?_⟩
  set b : ℝ := (m : ℝ) - movA d s with hb
  have hb0 : 0 ≤ b := by
    have := (mov2d_a_bounds d H.hd H.hsd).2
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hb]; linarith
  -- the differences `e n = vn n - v`
  set e : ℕ → Euc d → ℝ := fun n x => vn n x - v x with he
  have hlin : ∀ (a c : ℝ) (f g : Euc d → ℝ), MemOsc (m : ℝ) f → MemOsc (m : ℝ) g →
      MemOsc (m : ℝ) (fun x => a * f x + c * g x) ∧
      oscNorm (m : ℝ) (fun x => a * f x + c * g x) ≤ |a| * oscNorm (m : ℝ) f + |c| * oscNorm (m : ℝ) g :=
    fun a c f g hf hg => HRS.MS.MovC1.movc1_osc_lin (m : ℝ) a c hf hg
  have hvnm : ∀ n, MemOsc (m : ℝ) (vn n) := fun n => memOsc_schwartz (m : ℝ) (vn n)
  have hem : ∀ n, MemOsc (m : ℝ) (e n) := fun n => by
    have := (hlin 1 (-1) _ _ (hvnm n) hv).1
    simpa [he, sub_eq_add_neg] using this
  have heosc : Tendsto (fun n => oscNorm (m : ℝ) (e n)) atTop (𝓝 0) := hvn
  -- osc of Schwartz differences
  have hdiff_osc : ∀ n k, oscNorm (m : ℝ) (⇑(vn n - vn k)) ≤
      oscNorm (m : ℝ) (e n) + oscNorm (m : ℝ) (e k) := by
    intro n k
    have := (hlin 1 (-1) _ _ (hem n) (hem k)).2
    have hfe : (fun x => (1 : ℝ) * e n x + (-1) * e k x) = ⇑(vn n - vn k) := by
      funext x; simp only [he, sub_apply]; ring
    rw [hfe] at this
    simpa using this
  have hdiff_osc' : ∀ n k, oscNorm (m : ℝ) (⇑(vn n - vn k)) ≤
      oscNorm (m : ℝ) (e n) + oscNorm (m : ℝ) (e k) := hdiff_osc
  -- sequence of profiles
  set P : ℕ → Euc d → ℝ := fun n => s67bd_profile d s ρ₀ (vn n) K i with hP
  have hPs : ∀ n, HRS.PDE.ToolboxRd.MemSobolev b (P n) ∧ s67bd_Hnorm b (P n) ≤ C * oscNorm (m : ℝ) (vn n) :=
    fun n => hunif (vn n) i
  have hPdiff : ∀ n k, (fun x => P n x - P k x) = s67bd_profile d s ρ₀ (⇑(vn n - vn k)) K i := by
    intro n k; funext x; exact (s67bd15b_profile_sub H K i (vn n) (vn k) x).symm
  have hmem : ∀ n, MemLp (P n) 2 (volume : Measure (Euc d)) := fun n => (hPs n).1.1
  -- L² Cauchy
  have hL2le : ∀ n k, (eLpNorm (fun x => P n x - P k x) 2 (volume : Measure (Euc d))).toReal ≤
      C * (oscNorm (m : ℝ) (e n) + oscNorm (m : ℝ) (e k)) := by
    intro n k
    rw [hPdiff n k]
    have h1 := hunif (vn n - vn k) i
    exact (s67bd15b_L2_le hb0 h1.1).trans (h1.2.trans (mul_le_mul_of_nonneg_left (hdiff_osc n k) hC0))
  set f : ℕ → Lp ℝ 2 (volume : Measure (Euc d)) := fun n => (hmem n).toLp (P n) with hf
  have hfnorm : ∀ n k, ‖f n - f k‖ = (eLpNorm (fun x => P n x - P k x) 2 (volume : Measure (Euc d))).toReal := by
    intro n k
    rw [← MemLp.toLp_sub (hmem n) (hmem k), Lp.norm_toLp]
    rfl
  have hcauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hev : ∀ᶠ n in atTop, oscNorm (m : ℝ) (e n) < ε / (2 * (C + 1)) :=
      (heosc.eventually (gt_mem_nhds (by positivity)))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn k hk => ?_⟩
    rw [dist_eq_norm, hfnorm]
    refine lt_of_le_of_lt (hL2le n k) ?_
    have h1 := hN n hn
    have h2 := hN k hk
    have hC1 : 0 < C + 1 := by linarith
    calc C * (oscNorm (m : ℝ) (e n) + oscNorm (m : ℝ) (e k))
        ≤ (C + 1) * (oscNorm (m : ℝ) (e n) + oscNorm (m : ℝ) (e k)) :=
          mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ < (C + 1) * (ε / (2 * (C + 1)) + ε / (2 * (C + 1))) :=
          mul_lt_mul_of_pos_left (add_lt_add h1 h2) hC1
      _ = ε := by field_simp; ring
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  set w : Euc d → ℝ := fun x => (L : Euc d → ℝ) x with hw
  have hwL2 : MemLp w 2 (volume : Measure (Euc d)) := Lp.memLp L
  have hfL : ∀ n, ‖f n - L‖ = (eLpNorm (fun x => P n x - w x) 2 (volume : Measure (Euc d))).toReal := by
    intro n
    rw [Lp.norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (f n) L, (hmem n).coeFn_toLp] with x h1 h2
    have h2' : (⇑(f n) : Euc d → ℝ) x = P n x := h2
    show ((f n - L : Lp ℝ 2 (volume : Measure (Euc d))) : Euc d → ℝ) x = P n x - (L : Euc d → ℝ) x
    rw [h1, Pi.sub_apply, h2']
  have hL2conv : Tendsto (fun n => (eLpNorm (fun x => P n x - w x) 2 (volume : Measure (Euc d))).toReal)
      atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hL)
    simpa [hfL] using this
  -- oscillator norms of the sequence converge
  have hosc_vn : Tendsto (fun n => oscNorm (m : ℝ) (vn n)) atTop (𝓝 (oscNorm (m : ℝ) v)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) heosc
    rw [Real.norm_eq_abs, abs_le]
    have h1 := (hlin 1 1 _ _ (hem n) hv).2
    have h2 := (hlin 1 (-1) _ _ (hvnm n) (hem n)).2
    have e1 : (fun x => (1 : ℝ) * e n x + 1 * v x) = vn n := by funext x; simp only [he]; ring
    have e2 : (fun x => (1 : ℝ) * vn n x + (-1) * e n x) = v := by funext x; simp only [he]; ring
    rw [e1] at h1
    rw [e2] at h2
    simp only [abs_one, abs_neg, one_mul] at h1 h2
    constructor <;> linarith
  have hsob := s67bd_sobolev_fatou d b hb0 P w (fun n => (hPs n).1) hwL2 hL2conv
    (fun n => C * oscNorm (m : ℝ) (vn n)) (C * oscNorm (m : ℝ) v) (fun n => (hPs n).2)
    (hosc_vn.const_mul C)
  -- tails
  have htail : ∀ n, s67bd_Hnorm b (fun x => P n x - w x) ≤ C * oscNorm (m : ℝ) (e n) := by
    intro n
    have hosc_k : Tendsto (fun k => oscNorm (m : ℝ) (⇑(vn n - vn k))) atTop
        (𝓝 (oscNorm (m : ℝ) (e n))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) heosc
      rw [Real.norm_eq_abs, abs_le]
      have hmd : MemOsc (m : ℝ) (⇑(vn n - vn k)) := memOsc_schwartz (m : ℝ) _
      have h1 := hdiff_osc n k
      have h2 := (hlin 1 1 _ _ hmd (hem k)).2
      have e3 : (fun x => (1 : ℝ) * (⇑(vn n - vn k)) x + 1 * e k x) = e n := by
        funext x; simp only [he, sub_apply]; ring
      rw [e3] at h2
      simp only [abs_one, one_mul] at h2
      constructor <;> linarith
    have hF := (hmem n).sub hwL2
    have hfn : ∀ k, HRS.PDE.ToolboxRd.MemSobolev b (s67bd_profile d s ρ₀ (⇑(vn n - vn k)) K i) :=
      fun k => (hunif (vn n - vn k) i).1
    have hL2' : Tendsto (fun k => (eLpNorm (fun x => s67bd_profile d s ρ₀ (⇑(vn n - vn k)) K i x -
        (P n x - w x)) 2 (volume : Measure (Euc d))).toReal) atTop (𝓝 0) := by
      have e4 : ∀ k, (fun x => s67bd_profile d s ρ₀ (⇑(vn n - vn k)) K i x - (P n x - w x)) =
          -(fun x => P k x - w x) := by
        intro k; funext x
        rw [← congrFun (hPdiff n k) x]; simp only [Pi.neg_apply]; ring
      simp_rw [e4, eLpNorm_neg]
      exact hL2conv
    have := s67bd_sobolev_fatou d b hb0 (fun k => s67bd_profile d s ρ₀ (⇑(vn n - vn k)) K i)
      (fun x => P n x - w x) hfn hF hL2' (fun k => C * oscNorm (m : ℝ) (⇑(vn n - vn k)))
      (C * oscNorm (m : ℝ) (e n)) (fun k => (hunif (vn n - vn k) i).2) (hosc_k.const_mul C)
    exact this.2
  refine ⟨w, hsob.1, fun n => (hPs n).1, ?_, hsob.2⟩
  refine squeeze_zero (fun n => Real.sqrt_nonneg _) htail ?_
  simpa using heosc.const_mul C

end HRS.MS.BreakdownS67
