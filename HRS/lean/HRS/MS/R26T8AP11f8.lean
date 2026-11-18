import HRS.MS.R26T8AP11f7

/-!
# S8.2 T8A P11f (part 8): `Conormal (k+1) b M σ A F → Conormal k b M (σ+1) (2A) (dx_i F)`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem r26t8a_f8_dx_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A : ℝ} (hA : 0 ≤ A)
    {F : Euc d → Euc d → ℝ} (hF : Conormal (k + 1) b M σ A F) (i : Fin d) :
    Conormal k b M (σ + 1) (2 * A) (r26t8a_dx i F) := by
  refine ⟨r26t8a_f7_dx_contDiffOn hF.1 i, fun p q hpq X z hz => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * ‖z‖ := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hl : R / 4 < ‖z‖ := by rw [hRdef]; linarith
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2 with hΨdef
  have hΨ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Ψ := r26t8a_gtilde_contDiff hchi hR hF.1
  have hΨ' : ContDiff ℝ ((p + q + 1 : ℕ) : WithTop ℕ∞) Ψ := hΨ.of_le (by exact_mod_cast (by omega : p + q + 1 ≤ k + 1))
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  set e : Euc d := EuclideanSpace.single i 1 with hedef
  set a1 : Euc d := (1 / 2 : ℝ) • e with ha1
  have hen : ‖e‖ = 1 := by simp [hedef]
  have ha1n : ‖a1‖ ≤ 1 := by rw [ha1, norm_smul, hen]; norm_num
  -- the identity of `midPair (dx_i F)` with a directional derivative of `Ψ` near `z`
  have hid : ∀ Y w : Euc d, ‖w - z‖ < ‖z‖ / 2 →
      midPair (r26t8a_dx i F) Y w = fderiv ℝ Ψ (Y, w) (a1, e) := by
    intro Y w hw
    have hwn : ‖z‖ / 2 < ‖w‖ := by
      have := norm_sub_norm_le z w
      rw [norm_sub_rev] at this; linarith
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hwn; linarith
    set x : Euc d := Y + (1 / 2 : ℝ) • w with hx
    set y : Euc d := Y - (1 / 2 : ℝ) • w with hy
    have hxy : x - y = w := by rw [hx, hy]; module
    have hxy' : (x + y) = (2 : ℝ) • Y := by rw [hx, hy]; module
    -- near `x`, `F x' y = Ψ ((x'+y)/2, x'-y)`
    set m : Euc d → Euc d × Euc d := fun x' => ((1 / 2 : ℝ) • (x' + y), x' - y) with hm
    have hmx : m x = (Y, w) := by
      simp only [hm]; rw [hxy]; ext <;> simp [hxy'] 
    have hev : (fun x' => F x' y) =ᶠ[𝓝 x] fun x' => Ψ (m x') := by
      have hopen : IsOpen {x' : Euc d | R / 4 < ‖x' - y‖} :=
        isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
      have hxm : x ∈ {x' : Euc d | R / 4 < ‖x' - y‖} := by
        show R / 4 < ‖x - y‖
        rw [hxy]; rw [hRdef]; linarith
      filter_upwards [hopen.mem_nhds hxm] with x' hx'
      have hx'' : R / 4 ≤ ‖x' - y‖ := le_of_lt hx'
      simp only [hm, hΨdef, r26t8a_psiCut_one hchi hR hx'', one_mul, midPair]
      congr 1
      · module
      · module
    set L : Euc d →L[ℝ] Euc d × Euc d :=
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)).prod (ContinuousLinearMap.id ℝ (Euc d)) with hL
    have hmd : HasFDerivAt m L x := by
      have h1 := ((hasFDerivAt_id (𝕜 := ℝ) x).add_const y).const_smul (1 / 2 : ℝ)
      have h2 := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const y
      exact h1.prodMk h2
    have hcomp := (hΨd (m x)).hasFDerivAt.comp x hmd
    have hfd := hcomp.fderiv
    rw [hmx] at hfd
    show fderiv ℝ (fun x' => F x' y) x e = fderiv ℝ Ψ (Y, w) (a1, e)
    rw [hev.fderiv_eq]
    show fderiv ℝ (Ψ ∘ m) x e = _
    rw [hfd]
    simp [hL, ha1]
  have hcong : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_dx i F) Yw.1 Yw.2) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => fderiv ℝ Ψ Yw (a1, e)) X z :=
    r26t8a_nest_congr_ball p q _ _ (ρ := ‖z‖ / 2) (by positivity) X z (fun Y w hw => hid Y w hw)
  have hmj : mixedJet p q (r26t8a_dx i F) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_dx i F) Yw.1 Yw.2) X z := rfl
  have hsplit : (fun Yw : Euc d × Euc d => fderiv ℝ Ψ Yw (a1, e)) =
      fun Yw => (r26t8a_dY Ψ Yw) a1 + (r26t8a_dw Ψ Yw) e := by
    funext Yw
    rw [r26t8a_dw_eq hΨd]
    simp only [r26t8a_dY, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    rw [← map_add]
    congr 1
    ext <;> simp
  have hC1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_dY Ψ) := r26t8a_p06b_dY_contDiff hΨ'
  have hC2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_dw Ψ) := r26t8a_dw_contDiff hΨ'
  have hLn : ∀ T : Euc d →L[ℝ] ℝ, ‖(ContinuousLinearMap.apply ℝ ℝ a1) T‖ ≤ ‖T‖ := fun T => by
    show ‖T a1‖ ≤ ‖T‖
    calc ‖T a1‖ ≤ ‖T‖ * ‖a1‖ := T.le_opNorm a1
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left ha1n (norm_nonneg _)
      _ = ‖T‖ := mul_one _
  have hLe : ∀ T : Euc d →L[ℝ] ℝ, ‖(ContinuousLinearMap.apply ℝ ℝ e) T‖ ≤ ‖T‖ := fun T => by
    show ‖T e‖ ≤ ‖T‖
    calc ‖T e‖ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
      _ = ‖T‖ := by rw [hen, mul_one]
  have hP1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => (ContinuousLinearMap.apply ℝ ℝ a1) (r26t8a_dY Ψ Yw)) :=
    (ContinuousLinearMap.apply ℝ ℝ a1).contDiff.comp hC1
  have hP2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => (ContinuousLinearMap.apply ℝ ℝ e) (r26t8a_dw Ψ Yw)) :=
    (ContinuousLinearMap.apply ℝ ℝ e).contDiff.comp hC2
  have hadd := r26t8a_nest_add p q z X hP1 hP2
  have t1 := r26t8a_nest_clm' (ContinuousLinearMap.apply ℝ ℝ a1) hLn p q (r26t8a_dY Ψ) X z hC1
  have t2 := r26t8a_nest_clm' (ContinuousLinearMap.apply ℝ ℝ e) hLe p q (r26t8a_dw Ψ) X z hC2
  have t1' := r26t8a_nest_dY_le q p Ψ X z hΨ'
  have t2' := r26t8a_nest_succ p q Ψ X z
  have g1 : r26t8a_nest (p + 1) q Ψ X z = mixedJet (p + 1) q F X z :=
    r26t8a_nest_gtilde hchi hR (F := F) (p + 1) q X z hl
  have g2 : r26t8a_nest p (q + 1) Ψ X z = mixedJet p (q + 1) F X z :=
    r26t8a_nest_gtilde hchi hR (F := F) p (q + 1) X z hl
  have b1 := hF.2 (p + 1) q (by omega) X z hz
  have b2 := hF.2 p (q + 1) (by omega) X z hz
  rw [hmj, hcong, hsplit]
  have hpw0 : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    unfold pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hs0 : 0 < min 1 ‖z‖ := lt_min one_pos hn
  have hs1 : min 1 ‖z‖ ≤ 1 := min_le_left _ _
  have hL0 : 0 ≤ (1 + |Real.log (min 1 ‖z‖)|) ^ b := by positivity
  have hexp1 : (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) ≤ (min 1 ‖z‖) ^ (-((σ + 1) + (q : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 hs1 (by linarith)
  have hexp2 : (min 1 ‖z‖) ^ (-(σ + ((q + 1 : ℕ) : ℝ))) = (min 1 ‖z‖) ^ (-((σ + 1) + (q : ℝ))) := by
    congr 1; push_cast; ring
  rw [hexp2] at b2
  have hApw : 0 ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := mul_nonneg hA hpw0
  calc ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => (ContinuousLinearMap.apply ℝ ℝ a1) (r26t8a_dY Ψ Yw) +
          (ContinuousLinearMap.apply ℝ ℝ e) (r26t8a_dw Ψ Yw)) X z‖
      ≤ ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => (ContinuousLinearMap.apply ℝ ℝ a1) (r26t8a_dY Ψ Yw)) X z‖ +
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => (ContinuousLinearMap.apply ℝ ℝ e) (r26t8a_dw Ψ Yw)) X z‖ :=
        (le_of_eq (congrArg norm hadd)).trans (norm_add_le _ _)
    _ ≤ ‖r26t8a_nest p q (r26t8a_dY Ψ) X z‖ + ‖r26t8a_nest p q (r26t8a_dw Ψ) X z‖ := add_le_add t1 t2
    _ ≤ ‖r26t8a_nest (p + 1) q Ψ X z‖ + ‖r26t8a_nest p (q + 1) Ψ X z‖ := add_le_add t1' (le_of_eq t2'.symm)
    _ = ‖mixedJet (p + 1) q F X z‖ + ‖mixedJet p (q + 1) F X z‖ := by rw [g1, g2]
    _ ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
          (1 + (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b) +
        A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
          (1 + (min 1 ‖z‖) ^ (-((σ + 1) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b) := add_le_add b1 b2
    _ ≤ 2 * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
          (1 + (min 1 ‖z‖) ^ (-((σ + 1) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b) := by
        have := mul_le_mul_of_nonneg_right hexp1 hL0
        nlinarith [mul_le_mul_of_nonneg_left this hApw]

end HRS.MS.R26T8A
