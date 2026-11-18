import HRS.Commutator.Whole.XNRSAux10

/-!
# Packet X-NRS, part 11: the two terms of `Θ G_y` and their integrability on the product
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xint_sq_lin (h : 𝓢(Euc d, ℂ)) (a₀ L : ℝ) :
    Integrable (fun x : Euc d => ‖h x‖ ^ 2 * (a₀ + L * ‖x‖)) := by
  obtain ⟨M, hM0, hM⟩ := xhbdd h
  have h1 : Integrable (fun x : Euc d => ‖h x‖ ^ 2 * a₀ + (‖h x‖ ^ 2 * ‖x‖) * L) := by
    refine ((xint_sq_bdd h).mul_const a₀).add ?_
    refine Integrable.mul_const ?_ L
    refine ((h.integrable_pow_mul volume 1).const_mul M).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((h.continuous.norm.pow 2).mul continuous_norm).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      calc ‖h x‖ ^ 2 * ‖x‖ = (‖h x‖ * ‖h x‖) * ‖x‖ := by ring
        _ ≤ (M * ‖h x‖) * ‖x‖ := by gcongr; exact hM x
        _ = M * (‖x‖ ^ 1 * ‖h x‖) := by ring
  refine h1.congr (Eventually.of_forall fun x => ?_)
  simp only; ring

lemma xint_G1 {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    Integrable (fun z : Euc d => ‖z‖ * xQ d σ δ z) := by
  have h1 := (integrable_norm_xP (d := d) hσ hδ).const_mul ((d : ℝ) + 2 * σ)
  have h2 := (integrable_xN (d := d) hσ hδ).const_mul (Real.sqrt δ)
  refine (h1.add h2).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (continuous_norm.mul (continuous_xQ hδ)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (xQ_nonneg hσ hδ z))]
    exact xQ_norm_le hσ hδ z

lemma xint_G2 {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    Integrable (fun z : Euc d => ‖z‖ ^ 2 * xQ d σ δ z) := by
  have h1 := (integrable_xN (d := d) hσ hδ).const_mul ((d : ℝ) + 2 * σ + 2)
  refine h1.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact ((continuous_norm.pow 2).mul (continuous_xQ hδ)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (xQ_nonneg hσ hδ z))]
    exact (xQ_mul_sq_le hσ hδ z).trans
      (mul_le_mul_of_nonneg_left (xK_le_xN hδ z)
        (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith))


/-- `D₁(x,y) = (div v)(x) K(x-y)`. -/
def xD1 (v : Euc d → Euc d) (σ δ : ℝ) (x y : Euc d) : ℝ :=
  (∑ c, xw v c c x) * xK d σ δ (x - y)

/-- `D₂(x,y) = Q(x-y) ⟨x-y, v(x)⟩`. -/
def xD2 (v : Euc d → Euc d) (σ δ : ℝ) (x y : Euc d) : ℝ :=
  xQ d σ δ (x - y) * inner ℝ (x - y) (v x)

lemma xGy_eq (v : Euc d → Euc d) (σ δ : ℝ) (y x : Euc d) :
    xGy v σ δ y x = xD1 v σ δ x y - xD2 v σ δ x y := by
  unfold xGy xD1 xD2 xg'
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  congr 1
  rw [real_inner_comm, PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [real_inner_eq_re_inner]
  ring

lemma xD1_bound {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hδ : 0 < δ) (x y : Euc d) : |xD1 v σ δ x y| ≤ (d : ℝ) * L * xK d σ δ (x - y) := by
  unfold xD1
  rw [abs_mul, abs_of_pos (xK_pos hδ _)]
  have : |∑ c, xw v c c x| ≤ (d : ℝ) * L := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ c, |xw v c c x| ≤ ∑ c : Fin d, L := Finset.sum_le_sum fun c _ => xw_le hv hL0 hL c c x
      _ = (d : ℝ) * L := by simp
  exact mul_le_mul_of_nonneg_right this (xK_pos hδ _).le

lemma xD2_bound {v : Euc d → Euc d} (σ δ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (x y : Euc d) :
    |xD2 v σ δ x y| ≤ ‖x - y‖ * xQ d σ δ (x - y) * ‖v x‖ := by
  unfold xD2
  rw [abs_mul, abs_of_nonneg (xQ_nonneg hσ hδ _)]
  have := abs_real_inner_le_norm (x - y) (v x)
  calc xQ d σ δ (x - y) * |inner ℝ (x - y) (v x)| ≤ xQ d σ δ (x - y) * (‖x - y‖ * ‖v x‖) :=
        mul_le_mul_of_nonneg_left this (xQ_nonneg hσ hδ _)
    _ = _ := by ring


/-- `Φ₁ = Θ D₁`. -/
def xPhi1 (h : 𝓢(Euc d, ℂ)) (v : Euc d → Euc d) (σ δ : ℝ) (p : Euc d × Euc d) : ℂ :=
  (h p.1 - h p.2) ^ 2 * ((xD1 v σ δ p.1 p.2 : ℝ) : ℂ)

/-- `Φ₂ = Θ D₂`. -/
def xPhi2 (h : 𝓢(Euc d, ℂ)) (v : Euc d → Euc d) (σ δ : ℝ) (p : Euc d × Euc d) : ℂ :=
  (h p.1 - h p.2) ^ 2 * ((xD2 v σ δ p.1 p.2 : ℝ) : ℂ)

lemma continuous_xD1 {v : Euc d → Euc d} (hv : XTVF v) {σ δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : Euc d × Euc d => xD1 v σ δ p.1 p.2) := by
  unfold xD1
  refine (continuous_finsetSum _ fun c _ => ?_).mul ?_
  · exact (xtg_xw hv c c).1.continuous.comp continuous_fst
  · exact (continuous_xK hδ).comp (continuous_fst.sub continuous_snd)

lemma continuous_xD2 {v : Euc d → Euc d} (hv : XTVF v) {σ δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : Euc d × Euc d => xD2 v σ δ p.1 p.2) := by
  unfold xD2
  refine ((continuous_xQ hδ).comp (continuous_fst.sub continuous_snd)).mul ?_
  have hvc : Continuous v := by
    have h1 : Continuous (fun x => (v x).ofLp) := continuous_pi fun c => xtvf_continuous hv c
    have h2 := (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp h1
    have h3 : ((WithLp.toLp 2 : (Fin d → ℝ) → Euc d) ∘ fun x => (v x).ofLp) = v := by
      funext x; simp
    rw [h3] at h2
    exact h2
  exact (continuous_fst.sub continuous_snd).inner (hvc.comp continuous_fst)

lemma xPhi1_int {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) :
    Integrable (xPhi1 h v σ δ) (volume.prod volume) := by
  have hb := (xe_int (xKer_xK (d := d) hσ hδ) h).const_mul ((d : ℝ) * L)
  refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
  · have : Continuous (xPhi1 h v σ δ) := by
      unfold xPhi1
      exact (((h.continuous.comp continuous_fst).sub (h.continuous.comp continuous_snd)).pow 2).mul
        (Complex.continuous_ofReal.comp (continuous_xD1 hv hδ))
    exact this.aestronglyMeasurable
  · show ‖xPhi1 h v σ δ p‖ ≤ (d : ℝ) * L * (‖h p.1 - h p.2‖ ^ 2 * xK d σ δ (p.1 - p.2))
    unfold xPhi1
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have := xD1_bound hv hL0 hL (σ := σ) hδ p.1 p.2
    nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg ‖h p.1 - h p.2‖)]


lemma xPhi2_int {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) {σ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (h : 𝓢(Euc d, ℂ)) :
    Integrable (xPhi2 h v σ δ) (volume.prod volume) := by
  have hG1 := xint_G1 (d := d) hσ hδ
  have hG2 := xint_G2 (d := d) hσ hδ
  have ha := xint_sq_lin h ‖v 0‖ L
  have hb1 := xint_xy1 (a := fun x => 2 * (‖h x‖ ^ 2 * (‖v 0‖ + L * ‖x‖))) (G := fun z => ‖z‖ * xQ d σ δ z)
    (ha.const_mul 2) hG1
  have hb2 := xint_xy2 (a := fun x => 2 * (‖h x‖ ^ 2 * (‖v 0‖ + L * ‖x‖))) (G := fun z => ‖z‖ * xQ d σ δ z)
    (ha.const_mul 2) hG1
  have hb3 := xint_xy2 (a := fun x => 2 * L * ‖h x‖ ^ 2) (G := fun z => ‖z‖ ^ 2 * xQ d σ δ z)
    ((xint_sq_bdd h).const_mul (2 * L)) hG2
  refine ((hb1.add hb2).add hb3).mono' ?_ (Eventually.of_forall fun p => ?_)
  · have : Continuous (xPhi2 h v σ δ) := by
      unfold xPhi2
      exact (((h.continuous.comp continuous_fst).sub (h.continuous.comp continuous_snd)).pow 2).mul
        (Complex.continuous_ofReal.comp (continuous_xD2 hv hδ))
    exact this.aestronglyMeasurable
  · show ‖xPhi2 h v σ δ p‖ ≤
      2 * (‖h p.1‖ ^ 2 * (‖v 0‖ + L * ‖p.1‖)) * (‖p.1 - p.2‖ * xQ d σ δ (p.1 - p.2)) +
      2 * (‖h p.2‖ ^ 2 * (‖v 0‖ + L * ‖p.2‖)) * (‖p.1 - p.2‖ * xQ d σ δ (p.1 - p.2)) +
      2 * L * ‖h p.2‖ ^ 2 * (‖p.1 - p.2‖ ^ 2 * xQ d σ δ (p.1 - p.2))
    unfold xPhi2
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    set z := p.1 - p.2 with hz
    have hD := xD2_bound (v := v) σ δ hσ hδ p.1 p.2
    have hQ := xQ_nonneg hσ hδ z
    have hv1 : ‖v p.1‖ ≤ ‖v 0‖ + L * ‖p.1‖ := xv_growth hL p.1
    have hx : ‖p.1‖ ≤ ‖p.2‖ + ‖z‖ := by
      calc ‖p.1‖ = ‖p.2 + z‖ := by rw [hz]; simp
        _ ≤ _ := norm_add_le _ _
    have hs := xsq_le (h p.1) (h p.2)
    have h0 : 0 ≤ ‖z‖ * xQ d σ δ z := mul_nonneg (norm_nonneg _) hQ
    have hD' : |xD2 v σ δ p.1 p.2| ≤ ‖z‖ * xQ d σ δ z * (‖v 0‖ + L * ‖p.1‖) := by
      refine hD.trans ?_
      rw [show ‖p.1 - p.2‖ * xQ d σ δ (p.1 - p.2) * ‖v p.1‖ = (‖z‖ * xQ d σ δ z) * ‖v p.1‖ by rw [hz]]
      exact mul_le_mul_of_nonneg_left hv1 h0
    have hmain : ‖h p.1 - h p.2‖ ^ 2 * |xD2 v σ δ p.1 p.2| ≤
        (2 * ‖h p.1‖ ^ 2 + 2 * ‖h p.2‖ ^ 2) * (‖z‖ * xQ d σ δ z * (‖v 0‖ + L * ‖p.1‖)) := by
      refine mul_le_mul hs hD' (abs_nonneg _) (by positivity)
    refine hmain.trans ?_
    have hxv : ‖v 0‖ + L * ‖p.1‖ ≤ (‖v 0‖ + L * ‖p.2‖) + L * ‖z‖ := by nlinarith
    have ha1 : 0 ≤ ‖v 0‖ + L * ‖p.1‖ := by positivity
    have e1 : (2 * ‖h p.1‖ ^ 2 + 2 * ‖h p.2‖ ^ 2) * (‖z‖ * xQ d σ δ z * (‖v 0‖ + L * ‖p.1‖)) =
        2 * ‖h p.1‖ ^ 2 * (‖z‖ * xQ d σ δ z * (‖v 0‖ + L * ‖p.1‖)) +
        2 * ‖h p.2‖ ^ 2 * (‖z‖ * xQ d σ δ z * (‖v 0‖ + L * ‖p.1‖)) := by ring
    rw [e1]
    have t1 : 2 * ‖h p.1‖ ^ 2 * (‖z‖ * xQ d σ δ z * (‖v 0‖ + L * ‖p.1‖)) =
        2 * (‖h p.1‖ ^ 2 * (‖v 0‖ + L * ‖p.1‖)) * (‖z‖ * xQ d σ δ z) := by ring
    have t2 : 2 * ‖h p.2‖ ^ 2 * (‖z‖ * xQ d σ δ z * (‖v 0‖ + L * ‖p.1‖)) ≤
        2 * ‖h p.2‖ ^ 2 * (‖z‖ * xQ d σ δ z * ((‖v 0‖ + L * ‖p.2‖) + L * ‖z‖)) := by
      gcongr
    have t3 : 2 * ‖h p.2‖ ^ 2 * (‖z‖ * xQ d σ δ z * ((‖v 0‖ + L * ‖p.2‖) + L * ‖z‖)) =
        2 * (‖h p.2‖ ^ 2 * (‖v 0‖ + L * ‖p.2‖)) * (‖z‖ * xQ d σ δ z) +
        2 * L * ‖h p.2‖ ^ 2 * (‖z‖ ^ 2 * xQ d σ δ z) := by ring
    rw [t1]
    linarith

end HRS.Commutator.Whole.XNRS
