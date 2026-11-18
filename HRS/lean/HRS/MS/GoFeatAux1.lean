import HRS.MS.GoCommAux2

/-!
# S5.5, oscillator bounds: the uniformly local norm of the Hermite functions (infrastructure)

`s55c_*` are the lemmas `mri_cutoff_bound`, `mri_cutoff_deriv_bound`, `mri_leibniz_sq`, `mri_cell_bound` of
`HRS.MP.RdInit`, with the uloc cutoff `χ` (support in `B(0,2)`) replaced by a cutoff supported in `B(0,R)` (the
cutoff `θ` of `ulNormE` is only `C_c^∞`).  `s55_ul_of_sup`: the `H^r_ul` norm is bounded by the sup bounds of the
partial derivatives of order at most `r`.  Combined with the combination bounds of `GoCommAux2` this gives
`‖θ(·-z) h_α‖_{H^r}` and `ulNormE r θ (oscTestFun m α) ≤ C λ_α^{(r-m)/2}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Go
open HRS HRS.Whole HRS.MP.RdInit

variable {d : ℕ} {R : ℝ}

/-- derivative bounds of the cutoff -/
theorem s55c_cutoff_bound {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Metric.ball (0 : Euc d) R) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M := by
  obtain ⟨hsm, hcs, -⟩ := hχ
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ C := fun i =>
    (hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hcs.iteratedFDeriv i)
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (m + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i hi x => ?_⟩
  refine (hC i x).trans ?_
  refine (le_abs_self _).trans ?_
  exact Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))


theorem s55c_cutoff_deriv_bound {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Metric.ball (0 : Euc d) R) {M : ℝ}
    (m : ℕ) (hM : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M) (z : Euc d) {i : ℕ} (hi : i ≤ m)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ ≤ (Metric.ball z R).indicator (fun _ => M) x := by
  rw [iteratedFDeriv_comp_sub]
  by_cases hx : x ∈ Metric.ball z R
  · rw [Set.indicator_of_mem hx]
    exact hM i hi _
  · rw [Set.indicator_of_notMem hx]
    have : x - z ∉ tsupport χ := by
      intro h
      apply hx
      have := hχ.2.2 h
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [Metric.mem_ball] using this
    have hz : iteratedFDeriv ℝ i χ (x - z) = 0 := by
      by_contra hne
      exact this (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))
    rw [hz]; simp



/-- `∑_{i ≤ m} ‖D^i g(x)‖²` -/
def mriG (m : ℕ) (g : Euc d → ℝ) (x : Euc d) : ℝ := ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i g x‖ ^ 2


theorem s55c_leibniz_sq {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Metric.ball (0 : Euc d) R) {M : ℝ} (hM0 : 0 ≤ M)
    (m : ℕ) (hM : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M) {g : Euc d → ℝ} (hg : ContDiff ℝ m g)
    (z : Euc d) {j : ℕ} (hj : j ≤ m) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => χ (y - z) * g y) x‖ ^ 2 ≤
      (Metric.ball z R).indicator (fun y => ((m + 1 : ℕ) : ℝ) * 4 ^ m * M ^ 2 * mriG m g y) x := by
  have hχz : ContDiff ℝ m (fun y => χ (y - z)) :=
    (hχ.1.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have hle := norm_iteratedFDeriv_mul_le hχz hg x (n := j) (by exact_mod_cast hj)
  by_cases hx : x ∈ Metric.ball z R
  · rw [Set.indicator_of_mem hx]
    have hb : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖ ≤ (2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) g x‖ := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 := s55c_cutoff_deriv_bound hχ (M := M) m hM z (hi'.trans hj) x
      rw [Set.indicator_of_mem hx] at h1
      have h2 : (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
      have : (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ ≤ 2 ^ j * M :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have h3 := hle.trans (Finset.sum_le_sum hb)
    have h4 : ‖iteratedFDeriv ℝ j (fun y => χ (y - z) * g y) x‖ ^ 2 ≤
        (∑ i ∈ Finset.range (j + 1), (2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) g x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    refine h4.trans ?_
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    rw [Finset.card_range]
    have h5 : ∑ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) g x‖) ^ 2 ≤
        4 ^ m * M ^ 2 * mriG m g x := by
      have : ∀ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) g x‖) ^ 2 =
          (4 : ℝ) ^ j * M ^ 2 * ‖iteratedFDeriv ℝ (j - i) g x‖ ^ 2 := by
        intro i _
        rw [show (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        ring
      have hrefl : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) g x‖ ^ 2 =
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i g x‖ ^ 2 := by
        have := Finset.sum_range_reflect (fun i => ‖iteratedFDeriv ℝ i g x‖ ^ 2) (j + 1)
        simpa using this
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hrefl]
      have h6 : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i g x‖ ^ 2 ≤ mriG m g x := by
        unfold mriG
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) fun i _ _ => sq_nonneg _
      have h7 : (4 : ℝ) ^ j ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hj
      exact mul_le_mul (mul_le_mul_of_nonneg_right h7 (sq_nonneg _)) h6
        (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
    have h8 : ((j + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
    exact le_trans (mul_le_mul h8 h5 (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity))
      (le_of_eq (by ring))
  · rw [Set.indicator_of_notMem hx]
    have hb : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖ ≤ 0 := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 := s55c_cutoff_deriv_bound hχ (M := M) m hM z (hi'.trans hj) x
      rw [Set.indicator_of_notMem hx] at h1
      have h0 : ‖iteratedFDeriv ℝ i (fun y => χ (y - z)) x‖ = 0 := le_antisymm h1 (norm_nonneg _)
      rw [h0]; simp
    have h3 := hle.trans (Finset.sum_nonpos hb)
    have : ‖iteratedFDeriv ℝ j (fun y => χ (y - z) * g y) x‖ = 0 := le_antisymm h3 (norm_nonneg _)
    rw [this]; simp


open HRS.PDE.ToolboxRd in
theorem s55c_cell_bound {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Metric.ball (0 : Euc d) R) {M : ℝ} (hM0 : 0 ≤ M)
    (m : ℕ) (hM : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ M) {g : Euc d → ℝ} (hg : ContDiff ℝ m g)
    (z : Euc d) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => χ (x - z) * g x) ∧
      0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => χ (x - z) * g x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => χ (x - z) * g x) ≤
        mriKc d m M * ∫ x in Metric.ball z R, mriG m g x := by
  have hχz : ContDiff ℝ m (fun y => χ (y - z)) :=
    (hχ.1.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const)
  have hu : ContDiff ℝ m (fun y => χ (y - z) * g y) := hχz.mul hg
  have hcs : HasCompactSupport (fun y => χ (y - z)) :=
    hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
  have hc : HasCompactSupport (fun y => χ (y - z) * g y) := hcs.mul_right
  obtain ⟨hmem, hsq⟩ := mri_sobolev_deriv hu hc
  refine ⟨hmem, ?_, ?_⟩
  · rw [hsq]
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (Finset.sum_nonneg fun idx _ => ?_)
    exact integral_nonneg fun x => sq_nonneg _
  rw [hsq]
  have hGint : IntegrableOn (mriG m g) (Metric.ball z R) volume :=
    ((mriG_continuous hg).continuousOn.integrableOn_compact (isCompact_closedBall z R)).mono_set
      Metric.ball_subset_closedBall
  set c0 : ℝ := ((m + 1 : ℕ) : ℝ) * 4 ^ m * M ^ 2 with hc0
  have hterm : ∀ j ≤ m, ∀ idx : Fin j → Fin d,
      ∫ x, (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2 ≤
        c0 * ∫ x in Metric.ball z R, mriG m g x := by
    intro j hj idx
    obtain ⟨hcont, hcomp⟩ := mri_partial_memLp hu hc (j := j) (by exact_mod_cast hj) idx
    have hLint : Integrable (fun x => (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2) volume := by
      refine (hcont.pow 2).integrable_of_hasCompactSupport ?_
      refine hcomp.mono fun x hx => ?_
      rw [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [h0])
    have hRint : Integrable ((Metric.ball z R).indicator (fun y => c0 * mriG m g y)) volume :=
      (integrable_indicator_iff measurableSet_ball).2 (hGint.const_mul c0)
    calc ∫ x, (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2
        ≤ ∫ x, (Metric.ball z R).indicator (fun y => c0 * mriG m g y) x := by
          refine integral_mono hLint hRint fun x => ?_
          have h1 := mri_abs_partialDeriv_le idx (fun y => χ (y - z) * g y) x
          have h2 := s55c_leibniz_sq hχ hM0 m hM hg z hj x
          calc (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2
              = |partialDeriv idx (fun y => χ (y - z) * g y) x| ^ 2 := (sq_abs _).symm
            _ ≤ ‖iteratedFDeriv ℝ j (fun y => χ (y - z) * g y) x‖ ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) h1 2
            _ ≤ _ := h2
      _ = c0 * ∫ x in Metric.ball z R, mriG m g x := by
          rw [integral_indicator measurableSet_ball, integral_const_mul]
  calc ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2
      ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ((d : ℝ) ^ j * (c0 * ∫ x in Metric.ball z R, mriG m g x)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx (fun y => χ (y - z) * g y) x) ^ 2
            ≤ ∑ _idx : Fin j → Fin d, c0 * ∫ x in Metric.ball z R, mriG m g x :=
              Finset.sum_le_sum fun idx _ => hterm j hjm idx
          _ = (d : ℝ) ^ j * (c0 * ∫ x in Metric.ball z R, mriG m g x) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                Fintype.card_fin, nsmul_eq_mul]
              push_cast; ring
    _ = mriKc d m M * ∫ x in Metric.ball z R, mriG m g x := by
        have e : ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
            ((d : ℝ) ^ j * (c0 * ∫ x in Metric.ball z R, mriG m g x)) =
            (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (d : ℝ) ^ j) *
              (c0 * ∫ x in Metric.ball z R, mriG m g x) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e]
        unfold mriKc
        rw [← hc0]
        ring






lemma s55_ul_of_sup {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (r : ℕ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ (g : Euc d → ℝ) (K' : ℝ), 0 ≤ K' → ContDiff ℝ r g →
      (∀ l ≤ r, ∀ (idx : Fin l → Fin d) (x : Euc d), |partialDeriv idx g x| ≤ K') →
      ulNormE r θ g ≤ ENNReal.ofReal (Cu * K') := by
  obtain ⟨R, hR⟩ := (hθ.2.1.isBounded).subset_ball (0 : Euc d)
  have hχ : ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ Metric.ball (0 : Euc d) R :=
    ⟨hθ.1, hθ.2.1, hR⟩
  obtain ⟨M, hM0, hM⟩ := s55c_cutoff_bound hχ r
  set V0 : ℝ := (volume (Metric.ball (0 : Euc d) R)).toReal with hV0
  have hV00 : 0 ≤ V0 := ENNReal.toReal_nonneg
  set S : ℝ := ∑ i ∈ Finset.range (r + 1), ((d : ℝ) ^ i) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨Real.sqrt (mriKc d r M * (S * V0)), Real.sqrt_nonneg _, fun g K' hK0 hg hK => ?_⟩
  have hnorm : ∀ i ≤ r, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ (d : ℝ) ^ i * K' := by
    intro i hi x
    exact (mri_norm_iter_le i g x).trans (s55_card_sum_le i _ fun idx => hK i hi idx x)
  set Gc : ℝ := ∑ i ∈ Finset.range (r + 1), ((d : ℝ) ^ i * K') ^ 2 with hGc
  have hG : ∀ x, mriG r g x ≤ Gc := by
    intro x
    unfold mriG
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm i hi' x) 2
  have hbound : ∀ z : Euc d, ∫ x in Metric.ball z R, mriG r g x ≤ Gc * V0 := by
    intro z
    have hGint : IntegrableOn (mriG r g) (Metric.ball z R) volume :=
      ((mriG_continuous hg).continuousOn.integrableOn_compact (isCompact_closedBall z R)).mono_set
        Metric.ball_subset_closedBall
    have hcint : IntegrableOn (fun _ : Euc d => Gc) (Metric.ball z R) volume :=
      integrableOn_const measure_ball_lt_top.ne
    calc ∫ x in Metric.ball z R, mriG r g x ≤ ∫ x in Metric.ball z R, Gc :=
          setIntegral_mono_on hGint hcint measurableSet_ball fun x _ => hG x
      _ = Gc * V0 := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Measure.addHaar_ball_center, mul_comm]
  have hEq : mriKc d r M * (Gc * V0) = (Real.sqrt (mriKc d r M * (S * V0)) * K') ^ 2 := by
    have h1 : Gc = K' ^ 2 * S := by
      rw [hGc, hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [mul_pow, Real.sq_sqrt (by have := mriKc_nonneg d r M; positivity), h1]; ring
  have hlt : ∀ z : Fin d → ℤ, sobolevNormE (r : ℝ) (fun x => θ (x - latticePt z) * g x) ≤
      ENNReal.ofReal (Real.sqrt (mriKc d r M * (S * V0)) * K') := by
    intro z
    obtain ⟨hmem, -, hle⟩ := s55c_cell_bound hχ hM0 r hM hg (latticePt z)
    unfold sobolevNormE
    simp only [hmem, ite_true]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r : ℝ) (fun x => θ (x - latticePt z) * g x)) ≤
        Real.sqrt ((Real.sqrt (mriKc d r M * (S * V0)) * K') ^ 2) :=
      Real.sqrt_le_sqrt (by
        rw [← hEq]
        exact hle.trans (mul_le_mul_of_nonneg_left (hbound _) (mriKc_nonneg d r M)))
    rwa [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hK0)] at h2
  unfold ulNormE
  exact iSup_le hlt


/-! ### Packaging for `oscTestFun m α = λ_α^{-m/2} h_α` -/

lemma s55_osc_eq (m : ℝ) (α : MultiIndex d) :
    oscTestFun m α = fun x => oscEigenvalue d α ^ (-(m / 2)) * hermiteFunD α x := rfl

lemma s55_rpow_sqrt_pow (m : ℝ) (α : MultiIndex d) (N0 : ℕ) :
    oscEigenvalue d α ^ (-(m / 2)) * Real.sqrt (oscEigenvalue d α) ^ N0 =
      oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2) := by
  have hl : 0 < oscEigenvalue d α := oscEigenvalue_pos α
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hl.le, ← Real.rpow_add hl]
  congr 1; ring

lemma s55_decay_smul {k : ℕ} {b Λ : ℝ} (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ k f) (hΛ : 0 ≤ Λ)
    (h : decayNormE k b f ≤ ENNReal.ofReal Λ) :
    decayNormE k b (fun x => c * f x) ≤ ENNReal.ofReal (|c| * Λ) := by
  unfold decayNormE at h ⊢
  refine s55_dse_le fun j hj idx x => ?_
  have e : partialDeriv idx (fun x => c * f x) x = c * partialDeriv idx f x :=
    HRS.MP.RdInit.mri_partialDeriv_smul (hf.of_le (by exact_mod_cast hj)) c idx x
  have h1 := s55_dse_bound h hj idx x
  rw [max_eq_left hΛ] at h1
  rw [e, abs_mul]
  calc jbracket x ^ (b + j) * (|c| * |partialDeriv idx f x|)
      = |c| * (jbracket x ^ (b + j) * |partialDeriv idx f x|) := by ring
    _ ≤ |c| * Λ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem s55_osc_bounds {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (m : ℝ) (r k : ℕ) (b : ℝ) (hb : 0 ≤ b) (N0 : ℕ)
    (hr : r ≤ N0) (hk : k + 2 * ⌈(b + k) / 2⌉₊ ≤ N0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧
      ulNormE r θ (oscTestFun m α) ≤ ENNReal.ofReal (C * oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2)) ∧
      decayNormE k b (oscTestFun m α) ≤ ENNReal.ofReal (C * oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2)) := by
  obtain ⟨Cinf, hC⟩ := hermiteFunD_uniform_bound (d := d)
  have hC0 : 0 ≤ Cinf := (abs_nonneg _).trans (hC (fun _ => 0) 0)
  obtain ⟨Cu, hCu0, hCu⟩ := s55_ul_of_sup hθ r
  obtain ⟨Cd, hCd0, hCd⟩ := s55_decay_hermite (d := d) k b hb N0 hk
  set C1 : ℝ := Cinf * (2 * Real.sqrt ((N0 : ℝ) + 1)) ^ N0 with hC1
  have hC10 : 0 ≤ C1 := by positivity
  refine ⟨max (Cu * C1) Cd, le_max_of_le_left (mul_nonneg hCu0 hC10), fun α => ⟨?_, ?_, ?_⟩⟩
  · exact contDiff_const.mul (contDiff_hermiteFunD α)
  · -- uniformly local norm
    set K' : ℝ := C1 * Real.sqrt (oscEigenvalue d α) ^ N0 with hK'
    have hK'0 : 0 ≤ K' := by positivity
    have hsup : ∀ l ≤ r, ∀ (idx : Fin l → Fin d) (x : Euc d), |partialDeriv idx (hermiteFunD α) x| ≤ K' := by
      intro l hl idx x
      have h1 := (s55_partial_comb α N0 l idx (by omega)).sup_le hC x
      have hKK1 := s55_KK_ge_one α N0
      have h2 : KK α N0 ^ l * Cinf ≤ KK α N0 ^ N0 * Cinf :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hKK1 (by omega)) hC0
      have h4 : KK α N0 ^ N0 ≤ (2 * Real.sqrt ((N0 : ℝ) + 1)) ^ N0 * Real.sqrt (oscEigenvalue d α) ^ N0 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (KK_nonneg α N0) (by simpa [mul_assoc] using s55_KK_le α N0) N0
      calc |partialDeriv idx (hermiteFunD α) x| ≤ KK α N0 ^ l * Cinf := h1
        _ ≤ KK α N0 ^ N0 * Cinf := h2
        _ ≤ ((2 * Real.sqrt ((N0 : ℝ) + 1)) ^ N0 * Real.sqrt (oscEigenvalue d α) ^ N0) * Cinf :=
            mul_le_mul_of_nonneg_right h4 hC0
        _ = K' := by rw [hK', hC1]; ring
    have hl := oscEigenvalue_pos α
    set c : ℝ := oscEigenvalue d α ^ (-(m / 2)) with hc
    have hc0 : 0 ≤ c := (Real.rpow_pos_of_pos hl _).le
    have hgd : ContDiff ℝ ∞ (fun x => c * hermiteFunD α x) :=
      contDiff_const.mul (contDiff_hermiteFunD α)
    have hg : ContDiff ℝ r (fun x => c * hermiteFunD α x) := hgd.of_le (by exact_mod_cast le_top)
    have hsup' : ∀ l ≤ r, ∀ (idx : Fin l → Fin d) (x : Euc d),
        |partialDeriv idx (fun x => c * hermiteFunD α x) x| ≤ c * K' := by
      intro l hl' idx x
      have e : partialDeriv idx (fun x => c * hermiteFunD α x) x = c * partialDeriv idx (hermiteFunD α) x :=
        HRS.MP.RdInit.mri_partialDeriv_smul ((contDiff_hermiteFunD α).of_le (by exact_mod_cast le_top)) c idx x
      rw [e, abs_mul, abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left (hsup l hl' idx x) hc0
    have h1 := hCu _ (c * K') (mul_nonneg hc0 hK'0) hg hsup'
    rw [s55_osc_eq]
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpos : 0 ≤ oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2) := (Real.rpow_pos_of_pos hl _).le
    calc Cu * (c * K') = (Cu * C1) * (c * Real.sqrt (oscEigenvalue d α) ^ N0) := by rw [hK']; ring
      _ = (Cu * C1) * oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2) := by rw [hc, s55_rpow_sqrt_pow]
      _ ≤ max (Cu * C1) Cd * oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  · have hl := oscEigenvalue_pos α
    set c : ℝ := oscEigenvalue d α ^ (-(m / 2)) with hc
    have hc0 : 0 ≤ c := (Real.rpow_pos_of_pos hl _).le
    have hpos : 0 ≤ oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2) := (Real.rpow_pos_of_pos hl _).le
    have hΛ : 0 ≤ Cd * Real.sqrt (oscEigenvalue d α) ^ N0 := by positivity
    have h1 := s55_decay_smul (k := k) (b := b) c ((contDiff_hermiteFunD α).of_le (by exact_mod_cast le_top)) hΛ
      (hCd α)
    rw [s55_osc_eq]
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [abs_of_nonneg hc0]
    calc c * (Cd * Real.sqrt (oscEigenvalue d α) ^ N0) = Cd * (c * Real.sqrt (oscEigenvalue d α) ^ N0) := by ring
      _ = Cd * oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2) := by rw [hc, s55_rpow_sqrt_pow]
      _ ≤ max (Cu * C1) Cd * oscEigenvalue d α ^ (((N0 : ℝ) - m) / 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos

end HRS.MS.Go
