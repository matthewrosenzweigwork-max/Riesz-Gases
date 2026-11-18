import HRS.MS.UniqE3c

/-!
# G2fb: a time-independent finite neighbour set (geometry only)

For `B(σ,c) = closedBall (Ψ σ c) (8 L)`, the local integral of any measurable `G ≥ 0` is bounded by the
sum over a finite family `S c` of lattice centres (independent of `σ` and `G`) of the weighted integrals
`∫ ς_{c'} G`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqG2fb

open HRS HRS.Whole HRS.MS.UniqC3

variable {d : ℕ}

theorem g2fb_cellPt_injective (hd : 1 ≤ d) : Function.Injective (cellPt d) := by
  intro z z' h
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hκ : (0 : ℝ) < (⌈Real.sqrt d⌉ : ℝ) := by
    have h1 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
    exact_mod_cast lt_of_lt_of_le h1 (Int.le_ceil _)
  funext i
  have := congrArg (fun v : Euc d => v i) h
  simp only [cellPt, HRS.MS.FlowD.latticePt_apply, PiLp.smul_apply, smul_eq_mul] at this
  have h2 := mul_left_cancel₀ (inv_ne_zero hκ.ne') this
  exact_mod_cast h2

/-- Every lattice point of `cellPt` within `R` of `c` lies in a finset of explicit cardinality. -/
theorem g2fb_finset (hd : 1 ≤ d) (c : Euc d) {R : ℝ} (hR : 0 ≤ R) :
    ∃ F : Finset (Fin d → ℤ), (∀ z, ‖cellPt d z - c‖ ≤ R → z ∈ F) ∧
      (F.card : ℝ) ≤ (2 * (R * (cellScale d : ℝ)) + 1) ^ d := by
  have hκ : (0 : ℝ) < (cellScale d : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast cellScale_pos hd)
  obtain ⟨F, hF1, hF2⟩ := count_scaled hκ c hR
  refine ⟨F, fun z hz => hF1 z ?_, ?_⟩
  · rw [← cellPt_eq_scaledPt, norm_sub_rev]; exact hz
  · simpa [div_inv_eq_mul] using hF2

theorem g2fb_neighbours {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hd : 1 ≤ d)
    (hF : FlowBundle d m Cb t χ χh b Ψ K) (ht : 0 ≤ t) :
    ∃ N : ℕ, ∃ S : Euc d → Finset (Euc d), (∀ c, (S c).card ≤ N) ∧
      (∀ c, ∀ c' ∈ S c, ∃ z : Fin d → ℤ, c' = cellPt d z) ∧
      ∀ σ ∈ Set.Icc (0:ℝ) t, ∀ c : Euc d, ∀ G : Euc d → ℝ≥0∞, Measurable G →
        ∫⁻ x in closedBall (Ψ σ c) (8 * Real.exp (Cb * t)), G x ≤
          ∑ c' ∈ S c, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c' x) * G x := by
  set E : ℝ := Real.exp (|Cb| * t) with hE
  set R : ℝ := 10 * E ^ 2 with hRdef
  have hE0 : 0 < E := Real.exp_pos _
  have hR0 : 0 ≤ R := by positivity
  have hfin := fun c : Euc d => g2fb_finset hd c hR0
  choose F hF1 hF2 using hfin
  refine ⟨⌈(2 * (R * (cellScale d : ℝ)) + 1) ^ d⌉₊, fun c => (F c).image (cellPt d), fun c => ?_,
    fun c c' hc' => ?_, fun σ hσ c G hG => ?_⟩
  · refine (Finset.card_image_le).trans ?_
    exact_mod_cast (hF2 c).trans (Nat.le_ceil _)
  · obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hc'
    exact ⟨z, rfl⟩
  · set L : ℝ := Real.exp (Cb * t) with hL
    have hL0 : 0 < L := Real.exp_pos _
    have hLE : L ≤ E := Real.exp_le_exp.2 (by nlinarith [neg_abs_le Cb, le_abs_self Cb])
    have hσE : Real.exp (Cb * σ) ≤ E :=
      Real.exp_le_exp.2 (by nlinarith [le_abs_self Cb, hσ.1, hσ.2, abs_nonneg Cb])
    set G' : Euc d → ℝ≥0∞ := (closedBall (Ψ σ c) (8 * L)).indicator G with hG'
    have hG'm : Measurable G' := hG.indicator measurableSet_closedBall
    have hlow := hF.cover_lower σ hσ G' hG'm
    rw [hG', lintegral_indicator measurableSet_closedBall] at hlow
    refine hlow.trans ?_
    set T : (Fin d → ℤ) → ℝ≥0∞ := fun z =>
      ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ (cellPt d z) x) * G' x with hT
    have hT0 : ∀ z ∉ F c, T z = 0 := by
      intro z hz
      have hfar : R < ‖cellPt d z - c‖ := by
        by_contra hle
        exact hz (hF1 c z (not_lt.1 hle))
      have h0 : ∀ x, ENNReal.ofReal (varsigma χ Ψ σ (cellPt d z) x) * G' x = 0 := by
        intro x
        by_cases hx : x ∈ closedBall (Ψ σ c) (8 * L)
        · have : varsigma χ Ψ σ (cellPt d z) x = 0 := by
            by_contra hne
            have hxs := hF.supp σ hσ (cellPt d z) (subset_tsupport _ (Function.mem_support.2 hne))
            rw [mem_closedBall, dist_eq_norm] at hxs hx
            have h10 : ‖Ψ σ (cellPt d z) - Ψ σ c‖ ≤ 10 * L := by
              have := norm_sub_le_norm_sub_add_norm_sub (Ψ σ (cellPt d z)) x (Ψ σ c)
              rw [norm_sub_rev x] at hxs
              linarith
            have h1 := hF.flow.lip_inv σ hσ (Ψ σ (cellPt d z)) (Ψ σ c)
            rw [hF.flow.inv_left σ hσ, hF.flow.inv_left σ hσ] at h1
            have h2 : ‖cellPt d z - c‖ ≤ E * (10 * L) :=
              h1.trans (mul_le_mul hσE h10 (norm_nonneg _) hE0.le)
            have h3 : E * (10 * L) ≤ R := by
              rw [hRdef]; nlinarith [mul_le_mul_of_nonneg_left hLE hE0.le]
            linarith
          simp [this]
        · simp [hG', Set.indicator_of_notMem hx]
      simp [hT, h0]
    rw [tsum_eq_sum hT0]
    have hle : ∀ z, T z ≤ ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ (cellPt d z) x) * G x := by
      intro z
      refine lintegral_mono fun x => ?_
      refine mul_le_mul_right ?_ _
      exact Set.indicator_le_self _ _ x
    calc ∑ z ∈ F c, T z ≤ ∑ z ∈ F c, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ (cellPt d z) x) * G x :=
          Finset.sum_le_sum fun z _ => hle z
      _ = ∑ c' ∈ (F c).image (cellPt d), ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c' x) * G x := by
          rw [Finset.sum_image (fun a _ b _ h => g2fb_cellPt_injective hd h)]

end HRS.MS.UniqG2fb
