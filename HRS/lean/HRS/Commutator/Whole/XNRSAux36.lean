import HRS.Commutator.Whole.XNRSAux35

/-!
# Packet X-NRS, part 36: the mollifying sequence and `𝒞(v_n, a) → 𝒞(v, a)`
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

open HRS.Commutator.Whole HRS.Commutator.Whole.SAMP1

/-- The bump of radius `1/(n+1)`. -/
def xmbump (d n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]; nlinarith⟩

/-- The normalised mollifying kernel. -/
def xmk (d n : ℕ) : Euc d → ℝ := (xmbump d n).normed volume

lemma xmk_ker (n : ℕ) : XMolKer (xmk d n) :=
  ⟨(xmbump d n).continuous_normed, (xmbump d n).hasCompactSupport_normed,
    fun x => (xmbump d n).nonneg_normed x, (xmbump d n).integral_normed⟩

lemma xmk_smooth (n : ℕ) : ContDiff ℝ ∞ (xmk d n) := (xmbump d n).contDiff_normed

lemma xmk_supp (n : ℕ) (y : Euc d) (hy : xmk d n y ≠ 0) : ‖y‖ ≤ 1 / ((n : ℝ) + 1) := by
  have : y ∈ Function.support (xmk d n) := hy
  rw [xmk, (xmbump d n).support_normed_eq] at this
  have h : ‖y‖ < 1 / ((n : ℝ) + 1) := by simpa [xmbump] using this
  exact h.le

theorem xmol_tendsto (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v) {a : Euc d → ℝ} {φ : 𝓢(Euc d, ℂ)}
    (ha : ∀ x, φ x = (a x : ℂ)) :
    Tendsto (fun n : ℕ => CcommFun (kernGrad s) (xmol (xmk d n) v) a) atTop
      (nhds (CcommFun (kernGrad s) v a)) := by
  have hd1 : 1 ≤ d := by omega
  have hsd' : s < d := by linarith
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hLv : XLip v L := fun x y => lip_norm_le hL x y
  have hLm : ∀ n : ℕ, XLip (xmol (xmk d n) v) L := fun n x y => xmol_lip (xmk_ker n) hL x y
  have hmeq : ∀ n : ℕ, CcommFun (kernGrad s) (xmol (xmk d n) v) a =
      xBil s (xmol (xmk d n) v) a a := fun n =>
    xCcomm_eq hd1 hs0 hsd' hL0 (hLm n) ha
  have hveq : CcommFun (kernGrad s) v a = xBil s v a a := xCcomm_eq hd1 hs0 hsd' hL0 hLv ha
  simp_rw [hmeq, hveq]
  unfold xBil
  have hI := xIa_int hd1 hs0 hsd' ha ha
  refine tendsto_integral_of_dominated_convergence
    (bound := fun p : Euc d × Euc d => L * (‖p.1 - p.2‖ ^ (-s) * (|a p.1| * |a p.2|)))
    ?_ (hI.const_mul _) ?_ ?_
  · intro n
    have hac : Continuous a := by
      have : a = fun x => (φ x).re := by funext x; rw [ha]; simp
      rw [this]; exact Complex.continuous_re.comp φ.continuous
    have hmc : Continuous (xmol (xmk d n) v) := by
      refine LipschitzWith.continuous (K := L) (LipschitzWith.of_dist_le_mul fun x y => ?_)
      rw [dist_eq_norm, dist_eq_norm]; exact xmol_lip (xmk_ker n) hL x y
    have := (HRS.Commutator.Whole.cmxSA_commKer_measurable s hmc.measurable)
    exact (this.mul ((hac.measurable.comp measurable_fst).mul
      (hac.measurable.comp measurable_snd))).aestronglyMeasurable
  · intro n
    refine Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |commKer (kernGrad s) (xmol (xmk d n) v) p.1 p.2| * (|a p.1| * |a p.2|)
        ≤ (L * ‖p.1 - p.2‖ ^ (-s)) * (|a p.1| * |a p.2|) :=
          mul_le_mul_of_nonneg_right (xkv_bound hs0 hL0 (hLm n) _ _) (by positivity)
      _ = L * (‖p.1 - p.2‖ ^ (-s) * (|a p.1| * |a p.2|)) := by ring
  · refine Eventually.of_forall fun p => ?_
    have hc : Tendsto (fun n : ℕ => commKer (kernGrad s) (xmol (xmk d n) v) p.1 p.2) atTop
        (nhds (commKer (kernGrad s) v p.1 p.2)) := by
      unfold commKer
      by_cases hp : p.1 = p.2
      · simp only [hp, if_true]; exact tendsto_const_nhds
      · simp only [hp, if_false]
        have hconv : ∀ y : Euc d, Tendsto (fun n : ℕ => xmol (xmk d n) v y) atTop (nhds (v y)) := by
          intro y
          rw [tendsto_iff_norm_sub_tendsto_zero]
          have h0 : Tendsto (fun n : ℕ => (L : ℝ) * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
            have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
              tendsto_one_div_add_atTop_nhds_zero_nat
            simpa using this.const_mul (L : ℝ)
          refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
          exact xmol_close (xmk_ker n) hL (xmk_supp n) y
        exact ((((hconv p.1).sub (hconv p.2)).inner tendsto_const_nhds))
    exact (hc.mul_const _)

end HRS.Commutator.Whole.XNRS
