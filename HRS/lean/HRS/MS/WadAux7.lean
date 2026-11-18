import HRS.MS.WadAux6

/-!
# S8.3, packet D2 (part 5): Duhamel (mild) form of classical solutions, continuity and differentiation
in the time parameter

Let `y_s(z) = e^{-a(s-r)} x + σ_{s-r} z` (the Mehler argument).  For `Φ` jointly continuous on
`[0,t] × ℝ^d` with polynomial growth in `y`, `s ↦ ∫ Φ(s, y_s(z)) dγ(z)` is continuous on `[r,t]`
(`s83_cont_param`).  `s83_hasDerivAt_theta` computes the derivative of `s ↦ ∫ (w_s - w_{s_0})(y_s(z)) dγ(z)`
at `s_0` as `∫ ∂_s w(s_0, y_{s_0}(z)) dγ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s83_continuous_mc (a : ℝ) : Continuous (s83_mc a) := by
  unfold s83_mc; fun_prop

theorem s83_continuous_ms (a ν : ℝ) : Continuous (s83_ms a ν) := by
  unfold s83_ms; fun_prop

theorem s83_continuous_y (a ν r : ℝ) (x z : Euc d) :
    Continuous fun s : ℝ => s83_mc a (s - r) • x + s83_ms a ν (s - r) • z :=
  (((s83_continuous_mc a).comp (continuous_id.sub continuous_const)).smul continuous_const).add
    (((s83_continuous_ms a ν).comp (continuous_id.sub continuous_const)).smul continuous_const)

/-- Norm bound of the Mehler argument for `s ≥ r`. -/
theorem s83_norm_y_le {a ν r s : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (hrs : r ≤ s) (x z : Euc d) :
    ‖s83_mc a (s - r) • x + s83_ms a ν (s - r) • z‖ ≤ ‖x‖ + Real.sqrt (ν / a) * ‖z‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 : |s83_mc a (s - r)| ≤ 1 := s83_abs_mc_le_one ha.le (by linarith)
  have h2 : |s83_ms a ν (s - r)| ≤ Real.sqrt (ν / a) := s83_abs_ms_le ha hν (by linarith)
  exact add_le_add (by nlinarith [norm_nonneg x]) (mul_le_mul_of_nonneg_right h2 (norm_nonneg z))

/-- `(1 + ‖y_s(z)‖)^p ≤ K (1 + ‖z‖)^p`. -/
theorem s83_poly_y_le {a ν r s : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (hrs : r ≤ s) (x z : Euc d) (p : ℕ) :
    (1 + ‖s83_mc a (s - r) • x + s83_ms a ν (s - r) • z‖) ^ p ≤
      (1 + ‖x‖ + Real.sqrt (ν / a)) ^ p * (1 + ‖z‖) ^ p := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ p
  have := s83_norm_y_le ha hν hrs x z
  have hs : 0 ≤ Real.sqrt (ν / a) := Real.sqrt_nonneg _
  nlinarith [norm_nonneg x, norm_nonneg z, mul_nonneg hs (norm_nonneg z), mul_nonneg (norm_nonneg x) (norm_nonneg z)]

/-- **Continuity of the parameter integral.** -/
theorem s83_cont_param {Φ : ℝ → Euc d → ℝ} {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    (hΦ : ContinuousOn (fun q : ℝ × Euc d => Φ q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ)) {K : ℝ} {p : ℕ}
    (hb : ∀ s ∈ Set.Icc 0 t, ∀ y, |Φ s y| ≤ K * (1 + ‖y‖) ^ p) {a ν : ℝ} (ha : 0 < a) (hν : 0 ≤ ν)
    (x : Euc d) :
    ContinuousOn (fun s => ∫ z, Φ s (s83_mc a (s - r) • x + s83_ms a ν (s - r) • z)
      ∂(stdGaussian (Euc d))) (Set.Icc r t) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg (Φ r 0)).trans (hb r ⟨hr, hrt⟩ 0)
    simpa using this
  have hsub : ∀ s ∈ Set.Icc r t, s ∈ Set.Icc 0 t := fun s hs => ⟨hr.trans hs.1, hs.2⟩
  refine continuousOn_of_dominated
    (bound := fun z : Euc d => K * ((1 + ‖x‖ + Real.sqrt (ν / a)) ^ p * (1 + ‖z‖) ^ p)) ?_ ?_ ?_ ?_
  · intro s hs
    have hc : Continuous fun z : Euc d => Φ s (s83_mc a (s - r) • x + s83_ms a ν (s - r) • z) := by
      have h1 : Continuous fun z : Euc d => (s, s83_mc a (s - r) • x + s83_ms a ν (s - r) • z) :=
        continuous_const.prodMk (continuous_const.add (continuous_const_smul _))
      exact hΦ.comp_continuous h1 (fun z => ⟨hsub s hs, Set.mem_univ _⟩)
    exact hc.aestronglyMeasurable
  · intro s hs
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs]
    refine (hb s (hsub s hs) _).trans ?_
    exact mul_le_mul_of_nonneg_left (s83_poly_y_le ha hν hs.1 x z p) hK
  · exact ((s83_int_pow p).const_mul _).const_mul _
  · refine Eventually.of_forall fun z => ?_
    have h1 : Continuous fun s : ℝ => (s, s83_mc a (s - r) • x + s83_ms a ν (s - r) • z) :=
      continuous_id.prodMk (s83_continuous_y a ν r x z)
    exact hΦ.comp h1.continuousOn (fun s hs => ⟨hsub s hs, Set.mem_univ _⟩)

/-- The Mehler argument `y_s(z) = e^{-a(s-r)} x + σ_{s-r} z`. -/
def s83_Y (a ν r : ℝ) (x z : Euc d) (s : ℝ) : Euc d :=
  s83_mc a (s - r) • x + s83_ms a ν (s - r) • z

/-- Mean value theorem in the time variable, with a point strictly between. -/
theorem s83_mvt {w v : ℝ → Euc d → ℝ} {t s0 : ℝ} (hs0 : s0 ∈ Set.Ioo 0 t)
    (hw : ContinuousOn (fun q : ℝ × Euc d => w q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hder : ∀ y, ∀ s ∈ Set.Ioo 0 t, HasDerivAt (fun s' => w s' y) (v s y) s) (y : Euc d) {s : ℝ}
    (hs : s ∈ Set.Ioo 0 t) (hne : s ≠ s0) :
    ∃ ξ, |ξ - s0| ≤ |s - s0| ∧ ξ ∈ Set.Ioo 0 t ∧ (w s y - w s0 y) / (s - s0) = v ξ y := by
  have hcont : ∀ u₁ u₂ : ℝ, Set.Icc u₁ u₂ ⊆ Set.Ioo 0 t →
      ContinuousOn (fun s' => w s' y) (Set.Icc u₁ u₂) := by
    intro u₁ u₂ hsub
    have h1 : Continuous fun s' : ℝ => (s', y) := continuous_id.prodMk continuous_const
    exact hw.comp h1.continuousOn (fun s' hs' => ⟨⟨(hsub hs').1.le, (hsub hs').2.le⟩, Set.mem_univ _⟩)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsub : Set.Icc s s0 ⊆ Set.Ioo 0 t := fun u hu => ⟨by linarith [hs.1, hu.1], by linarith [hs0.2, hu.2]⟩
    obtain ⟨ξ, hξ, hv⟩ := exists_hasDerivAt_eq_slope (fun s' => w s' y) (fun s' => v s' y) hlt
      (hcont s s0 hsub) (fun u hu => hder y u ⟨by linarith [hs.1, hu.1], by linarith [hs0.2, hu.2]⟩)
    refine ⟨ξ, ?_, ⟨by linarith [hs.1, hξ.1], by linarith [hs0.2, hξ.2]⟩, ?_⟩
    · rw [abs_of_neg (by linarith [hξ.2]), abs_of_neg (by linarith)]
      linarith [hξ.1]
    · rw [← neg_div_neg_eq, neg_sub, neg_sub, hv]
  · have hsub : Set.Icc s0 s ⊆ Set.Ioo 0 t := fun u hu => ⟨by linarith [hs0.1, hu.1], by linarith [hs.2, hu.2]⟩
    obtain ⟨ξ, hξ, hv⟩ := exists_hasDerivAt_eq_slope (fun s' => w s' y) (fun s' => v s' y) hgt
      (hcont s0 s hsub) (fun u hu => hder y u ⟨by linarith [hs0.1, hu.1], by linarith [hs.2, hu.2]⟩)
    refine ⟨ξ, ?_, ⟨by linarith [hs0.1, hξ.1], by linarith [hs.2, hξ.2]⟩, ?_⟩
    · rw [abs_of_pos (by linarith [hξ.1]), abs_of_pos (by linarith)]
      linarith [hξ.2]
    · rw [hv]

/-- Derivative of `s ↦ ∫ (w_s - w_{s_0})(y_s(z)) dγ(z)` at `s_0` (the time-dependence of the datum). -/
theorem s83_hasDerivAt_theta {w v : ℝ → Euc d → ℝ} {r t s0 : ℝ} (hr : 0 ≤ r) (hrs : r < s0)
    (hst : s0 < t)
    (hw : ContinuousOn (fun q : ℝ × Euc d => w q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hv : ContinuousOn (fun q : ℝ × Euc d => v q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hder : ∀ y, ∀ s ∈ Set.Ioo 0 t, HasDerivAt (fun s' => w s' y) (v s y) s) {Bv : ℝ}
    (hvb : ∀ s ∈ Set.Icc 0 t, ∀ y, |v s y| ≤ Bv * (1 + ‖y‖)) {a ν : ℝ} (ha : 0 < a) (hν : 0 ≤ ν)
    (x : Euc d) :
    HasDerivAt (fun s => ∫ z, (w s (s83_Y a ν r x z s) - w s0 (s83_Y a ν r x z s))
        ∂(stdGaussian (Euc d)))
      (∫ z, v s0 (s83_Y a ν r x z s0) ∂(stdGaussian (Euc d))) s0 := by
  have hs0 : s0 ∈ Set.Ioo 0 t := ⟨by linarith, hst⟩
  have hBv : 0 ≤ Bv := by
    have := (abs_nonneg (v s0 0)).trans (hvb s0 ⟨hs0.1.le, hs0.2.le⟩ 0)
    simpa using this
  rw [hasDerivAt_iff_tendsto_slope]
  have hmvt : ∀ (y : Euc d) (s : ℝ), s ∈ Set.Ioo 0 t → s ≠ s0 →
      ∃ ξ, |ξ - s0| ≤ |s - s0| ∧ ξ ∈ Set.Ioo 0 t ∧ (w s y - w s0 y) / (s - s0) = v ξ y :=
    fun y s hs hne => s83_mvt hs0 hw hder y hs hne
  choose! ξ hξ using hmvt
  set l : Filter ℝ := 𝓝[≠] s0 with hl
  have hev : ∀ᶠ s in l, s ∈ Set.Ioo r t ∧ s ≠ s0 := by
    have h1 : Set.Ioo r t ∈ 𝓝 s0 := Ioo_mem_nhds hrs hst
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs1 hs2 using ⟨hs1, hs2⟩
  have hcz : ∀ u ∈ Set.Icc 0 t, ∀ s : ℝ, Continuous fun z : Euc d => w u (s83_Y a ν r x z s) := by
    intro u hu s
    have h1 : Continuous fun z : Euc d => (u, s83_mc a (s - r) • x + s83_ms a ν (s - r) • z) :=
      continuous_const.prodMk (continuous_const.add (continuous_const_smul _))
    exact hw.comp_continuous h1 (fun z => ⟨hu, Set.mem_univ _⟩)
  set F : ℝ → Euc d → ℝ := fun s z =>
    (s - s0)⁻¹ * (w s (s83_Y a ν r x z s) - w s0 (s83_Y a ν r x z s)) with hF
  have hslope : ∀ s, s ≠ s0 → slope (fun s => ∫ z, (w s (s83_Y a ν r x z s) -
      w s0 (s83_Y a ν r x z s)) ∂(stdGaussian (Euc d))) s0 s = ∫ z, F s z ∂(stdGaussian (Euc d)) := by
    intro s hs
    rw [slope_def_field]
    simp only [sub_self, integral_zero, sub_zero, hF]
    rw [integral_const_mul, div_eq_inv_mul]
  have hbound : ∀ s ∈ Set.Ioo r t, s ≠ s0 → ∀ z : Euc d, ‖F s z‖ ≤
      Bv * (1 + ‖x‖ + Real.sqrt (ν / a)) ^ 1 * (1 + ‖z‖) ^ 1 := by
    intro s hs hne z
    have hs' : s ∈ Set.Ioo 0 t := ⟨by linarith [hs.1], hs.2⟩
    have hh := hξ (s83_Y a ν r x z s) s hs' hne
    have : F s z = v (ξ (s83_Y a ν r x z s) s) (s83_Y a ν r x z s) := by
      rw [← hh.2.2, hF, div_eq_inv_mul]
    rw [this, Real.norm_eq_abs]
    refine (hvb _ ⟨hh.2.1.1.le, hh.2.1.2.le⟩ _).trans ?_
    have := s83_poly_y_le ha hν hs.1.le x z 1
    simp only [pow_one] at this ⊢
    calc Bv * (1 + ‖s83_Y a ν r x z s‖) ≤ Bv * ((1 + ‖x‖ + Real.sqrt (ν / a)) * (1 + ‖z‖)) :=
          mul_le_mul_of_nonneg_left this hBv
      _ = _ := by ring
  refine Tendsto.congr' ?_ (tendsto_integral_filter_of_dominated_convergence
    (F := F) (bound := fun z : Euc d => Bv * (1 + ‖x‖ + Real.sqrt (ν / a)) ^ 1 * (1 + ‖z‖) ^ 1) ?_ ?_ ?_ ?_)
  · filter_upwards [hev] with s hs
    exact (hslope s hs.2).symm
  · filter_upwards [hev] with s hs
    have hs' : s ∈ Set.Icc 0 t := ⟨by linarith [hs.1.1], hs.1.2.le⟩
    exact (continuous_const.mul ((hcz s hs' s).sub (hcz s0 ⟨hs0.1.le, hs0.2.le⟩ s))).aestronglyMeasurable
  · filter_upwards [hev] with s hs
    exact Eventually.of_forall (hbound s hs.1 hs.2)
  · exact (s83_int_pow 1).const_mul _
  · refine Eventually.of_forall fun z => ?_
    have hξt : Tendsto (fun s => ξ (s83_Y a ν r x z s) s) l (𝓝 s0) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero' (g := fun s : ℝ => dist s s0) (Eventually.of_forall fun s => dist_nonneg) ?_ ?_
      · show ∀ᶠ s in l, dist (ξ (s83_Y a ν r x z s) s) s0 ≤ dist s s0
        filter_upwards [hev] with s hs
        have hs' : s ∈ Set.Ioo 0 t := ⟨by linarith [hs.1.1], hs.1.2⟩
        have := (hξ (s83_Y a ν r x z s) s hs' hs.2).1
        simpa [Real.dist_eq] using this
      · exact tendsto_iff_dist_tendsto_zero.1
          ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 s0) (𝓝 s0)).mono_left nhdsWithin_le_nhds)
    have hY : Tendsto (fun s => s83_Y a ν r x z s) l (𝓝 (s83_Y a ν r x z s0)) :=
      ((s83_continuous_y a ν r x z).tendsto s0).mono_left nhdsWithin_le_nhds
    have hpair : Tendsto (fun s => (ξ (s83_Y a ν r x z s) s, s83_Y a ν r x z s)) l
        (𝓝 (s0, s83_Y a ν r x z s0)) := hξt.prodMk_nhds hY
    have hvc : ContinuousAt (fun q : ℝ × Euc d => v q.1 q.2) (s0, s83_Y a ν r x z s0) := by
      refine hv.continuousAt ?_
      exact prod_mem_nhds (Icc_mem_nhds hs0.1 hs0.2) Filter.univ_mem
    refine (hvc.tendsto.comp hpair).congr' ?_
    filter_upwards [hev] with s hs
    have hs' : s ∈ Set.Ioo 0 t := ⟨by linarith [hs.1.1], hs.1.2⟩
    have h3 := (hξ (s83_Y a ν r x z s) s hs' hs.2).2.2
    simp only [Function.comp, hF]
    rw [← h3, div_eq_inv_mul]

end HRS.MS.Wad
