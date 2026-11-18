import HRS.Whole.Round2Moving
import HRS.MS.R2SeAux1
import HRS.MS.SuppU1
import HRS.MS.MovThermAux1

/-!
# S11.4 item (4), part 1: the velocity ball, the commutator difference estimate, and a finite `C^1(K_R)`-net

Worker S11P, namespace `HRS.MS.R2S11`, helper prefix `s11_`.  No existing file is edited.

Setting: `V Λ = {v // IsR2VelocityBall d Λ v}` (`C²` fields with `‖v‖_{C_b²} ≤ Λ`).  Results:

* `s11_thermal_round2`: a thermal equilibrium `ρ₀` satisfies `IsRound2Density d s M L ρ₀` (and a Gaussian upper bound);
* `s11_V_fderiv_le`, `s11_V_fderiv2_le`, `s11_V_lip`, `s11_V_fderiv_lip`: the pointwise bounds on `v ∈ V Λ`;
* `s11_inner_bound`: `|⟨a, ∇g(z)⟩| ≤ (s+1) ℓ (1 + W_s(z))` if `‖a‖ ≤ ℓ‖z‖`;
* `s11_kernel_diff_bound`: if `‖Dv - Dw‖ ≤ η` on `closedBall 0 R` then `|h_v - h_w| ≤ (s+1) η (1 + W_s(x-y))` on `closedBall 0 R × closedBall 0 R`;
* `s11_net_fderiv`: Arzelà-Ascoli: for `R, η > 0` there is a finite `F ⊂ V Λ` with every `v ∈ V Λ` within `η` of some `w ∈ F` in
  `sup_{closedBall 0 R} ‖Dv - Dw‖`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-! ### Thermal data -/

theorem s11_thermal_round2 (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hq : 0 < q)
    (hβ : 0 < β) {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ M L c : ℝ, IsRound2Density d s M L ρ₀ ∧ HasR2GaussianUpper M c ρ₀ := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd hq hβ
  obtain ⟨L, hL, hG⟩ := S99.s99_round2_density hT
  have hrho : ρ₀ = thermalDensity d s q β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd hq hβ hρ
  subst hrho
  exact ⟨C, L, c, hL, hG⟩

/-! ### The velocity ball -/

/-- The ball of velocities `‖v‖_{C_b²} ≤ Λ`. -/
abbrev s11V (d : ℕ) (Λ : ℝ) : Type := {v : Euc d → Euc d // IsR2VelocityBall d Λ v}

theorem s11_cbVec_bound {K : ℕ} {v : Euc d → Euc d} {Λ : ℝ} (h : cbNormVecE K v ≤ ENNReal.ofReal Λ)
    {i : ℕ} (hi : i ≤ K) (x : Euc d) : ‖iteratedFDeriv ℝ i v x‖ ≤ max Λ 0 := by
  unfold cbNormVecE at h
  have h1 : (⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i v y‖) ≤ ENNReal.ofReal Λ :=
    (Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v y‖)
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))).trans h
  have h2 : ENNReal.ofReal ‖iteratedFDeriv ℝ i v x‖ ≤ ENNReal.ofReal Λ := (le_iSup _ x).trans h1
  by_cases hΛ : 0 ≤ Λ
  · exact ((ENNReal.ofReal_le_ofReal_iff hΛ).1 h2).trans (le_max_left _ _)
  · push Not at hΛ
    rw [ENNReal.ofReal_of_nonpos hΛ.le] at h2
    have := ENNReal.ofReal_eq_zero.1 (le_antisymm h2 zero_le)
    exact this.trans (le_max_right _ _)

theorem s11_V_fderiv_le {Λ : ℝ} (v : s11V d Λ) (x : Euc d) : ‖fderiv ℝ v.1 x‖ ≤ max Λ 0 := by
  have := s11_cbVec_bound v.2.2 (i := 1) (by norm_num) x
  rwa [norm_iteratedFDeriv_one] at this

theorem s11_V_fderiv2_le {Λ : ℝ} (v : s11V d Λ) (x : Euc d) :
    ‖fderiv ℝ (fderiv ℝ v.1) x‖ ≤ max Λ 0 := by
  have h := s11_cbVec_bound v.2.2 (i := 2) (by norm_num) x
  have e : ‖iteratedFDeriv ℝ 1 (fderiv ℝ v.1) x‖ = ‖iteratedFDeriv ℝ (1 + 1) v.1 x‖ :=
    norm_iteratedFDeriv_fderiv
  rw [norm_iteratedFDeriv_one] at e
  rw [e]
  exact h

theorem s11_V_diff {Λ : ℝ} (v : s11V d Λ) : Differentiable ℝ v.1 :=
  v.2.1.differentiable (by norm_num)

theorem s11_V_fderiv_diff {Λ : ℝ} (v : s11V d Λ) : Differentiable ℝ (fderiv ℝ v.1) :=
  (v.2.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

theorem s11_V_lip {Λ : ℝ} (v : s11V d Λ) : LipschitzWith (Real.toNNReal (max Λ 0)) v.1 := by
  refine lipschitzWith_of_nnnorm_fderiv_le (s11_V_diff v) (fun x => ?_)
  have h := s11_V_fderiv_le v x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
  exact h

theorem s11_V_fderiv_lip {Λ : ℝ} (v : s11V d Λ) :
    LipschitzWith (Real.toNNReal (max Λ 0)) (fderiv ℝ v.1) := by
  refine lipschitzWith_of_nnnorm_fderiv_le (s11_V_fderiv_diff v) (fun x => ?_)
  have h := s11_V_fderiv2_le v x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
  exact h

/-! ### The commutator difference -/

theorem s11_rieszWeight_nonneg (s : ℝ) (z : Euc d) : 0 ≤ rieszWeight s z := by
  unfold rieszWeight
  split_ifs
  · exact le_max_right _ _
  · exact Real.rpow_nonneg (norm_nonneg _) _

theorem s11_inner_bound {s : ℝ} (hs0 : 0 ≤ s) {a z : Euc d} {ℓ : ℝ} (hz : z ≠ 0) (hℓ : 0 ≤ ℓ)
    (ha : ‖a‖ ≤ ℓ * ‖z‖) :
    |inner ℝ a (rieszKernelGrad d s z)| ≤ (s + 1) * ℓ * (1 + rieszWeight s z) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hW := s11_rieszWeight_nonneg (d := d) s z
  have hG := movtr_rieszKernelGrad_norm (d := d) s hs0 hz
  have hpow : ‖z‖ ^ (-s) = ‖z‖ ^ (-s - 1) * ‖z‖ := by
    rw [← Real.rpow_add_one hzpos.ne']
    congr 1
    ring
  have h1 : |inner ℝ a (rieszKernelGrad d s z)| ≤ ‖a‖ * ‖rieszKernelGrad d s z‖ :=
    abs_real_inner_le_norm _ _
  have h2 : ‖a‖ * ‖rieszKernelGrad d s z‖ ≤ (ℓ * ‖z‖) * (movtr_sigma s * ‖z‖ ^ (-s - 1)) := by
    rw [hG]
    exact mul_le_mul ha le_rfl (by rw [← hG]; exact norm_nonneg _) (by positivity)
  refine h1.trans (h2.trans ?_)
  by_cases h0 : s = 0
  · subst h0
    have e : (ℓ * ‖z‖) * (movtr_sigma 0 * ‖z‖ ^ (-(0 : ℝ) - 1)) = ℓ := by
      simp [movtr_sigma, Real.rpow_neg_one, mul_inv_cancel₀ hzpos.ne']
      field_simp
    rw [e]
    nlinarith [mul_nonneg hℓ hW]
  · have hσ : movtr_sigma s = s := by simp [movtr_sigma, h0]
    have hw : rieszWeight s z = ‖z‖ ^ (-s) := by simp [rieszWeight, h0]
    have e : (ℓ * ‖z‖) * (movtr_sigma s * ‖z‖ ^ (-s - 1)) = s * ℓ * ‖z‖ ^ (-s) := by
      rw [hσ, hpow]; ring
    rw [e, ← hw]
    nlinarith [mul_nonneg hℓ hW, hℓ]

/-- If `‖D(v-w)‖ ≤ η` on `closedBall 0 R`, then `|h_v - h_w| ≤ (s+1) η (1 + W_s)` on `closedBall 0 R × closedBall 0 R`. -/
theorem s11_kernel_diff_bound {s : ℝ} (hs0 : 0 ≤ s) {Λ : ℝ} (v w : s11V d Λ) {R η : ℝ} (hη : 0 ≤ η)
    (hD : ∀ z ∈ closedBall (0 : Euc d) R, ‖fderiv ℝ v.1 z - fderiv ℝ w.1 z‖ ≤ η)
    {x y : Euc d} (hx : x ∈ closedBall (0 : Euc d) R) (hy : y ∈ closedBall (0 : Euc d) R) (hxy : x ≠ y) :
    |commutatorKernel d s v.1 x y - commutatorKernel d s w.1 x y| ≤
      (s + 1) * η * (1 + rieszWeight s (x - y)) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  set u : Euc d → Euc d := fun z => v.1 z - w.1 z with hu
  have hud : ∀ z ∈ closedBall (0 : Euc d) R, DifferentiableAt ℝ u z := fun z _ =>
    ((s11_V_diff v) z).sub ((s11_V_diff w) z)
  have hfd : ∀ z ∈ closedBall (0 : Euc d) R, ‖fderiv ℝ u z‖ ≤ η := fun z hz' => by
    have : fderiv ℝ u z = fderiv ℝ v.1 z - fderiv ℝ w.1 z :=
      fderiv_sub ((s11_V_diff v) z) ((s11_V_diff w) z)
    rw [this]; exact hD z hz'
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le hud hfd (convex_closedBall (0 : Euc d) R) hy hx
  have ha : ‖(v.1 x - v.1 y) - (w.1 x - w.1 y)‖ ≤ η * ‖x - y‖ := by
    have e : (v.1 x - v.1 y) - (w.1 x - w.1 y) = u x - u y := by simp only [hu]; abel
    rw [e]
    exact hmv
  have e2 : commutatorKernel d s v.1 x y - commutatorKernel d s w.1 x y =
      inner ℝ ((v.1 x - v.1 y) - (w.1 x - w.1 y)) (rieszKernelGrad d s (x - y)) := by
    unfold commutatorKernel
    exact (inner_sub_left _ _ _).symm
  rw [e2]
  exact s11_inner_bound hs0 hz hη ha

/-! ### Arzelà-Ascoli: a finite net for `Dv` on `closedBall 0 R` -/

theorem s11_net_fderiv (Λ : ℝ) (R : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset (s11V d Λ), ∀ v : s11V d Λ, ∃ w ∈ F,
      ∀ z ∈ closedBall (0 : Euc d) R, ‖fderiv ℝ v.1 z - fderiv ℝ w.1 z‖ ≤ η := by
  classical
  set K : Set (Euc d) := closedBall 0 R with hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  set Λ' : ℝ := max Λ 0 with hΛ'
  let Dv : s11V d Λ → (BoundedContinuousFunction K (Euc d →L[ℝ] Euc d)) := fun v =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun z : K => fderiv ℝ v.1 (z : Euc d))
      ((s11_V_fderiv_lip v).continuous.comp continuous_subtype_val) Λ'
      (fun z => s11_V_fderiv_le v z)
  set A : Set (BoundedContinuousFunction K (Euc d →L[ℝ] Euc d)) := range Dv with hA
  have hlipA : ∀ u : A, LipschitzWith (Real.toNNReal Λ') (fun z : K => (u.1 : BoundedContinuousFunction K (Euc d →L[ℝ] Euc d)) z) := by
    rintro ⟨u, v, rfl⟩
    have h := (s11_V_fderiv_lip v).comp (LipschitzWith.subtype_val K)
    rw [mul_one] at h
    exact h
  have heq : Equicontinuous ((↑) : A → K → (Euc d →L[ℝ] Euc d)) :=
    (LipschitzWith.uniformEquicontinuous (fun u : A => (u.1 : K → (Euc d →L[ℝ] Euc d)))
      (Real.toNNReal Λ') hlipA).equicontinuous
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : Euc d →L[ℝ] Euc d) Λ')
      (isCompact_closedBall _ _) A
      (fun u z hu => by
        obtain ⟨v, rfl⟩ := hu
        rw [mem_closedBall, dist_zero_right]
        exact s11_V_fderiv_le v z) heq
  have htb : TotallyBounded A := hcomp.totallyBounded.subset subset_closure
  obtain ⟨t, htA, htfin, hcover⟩ := (EMetric.totallyBounded_iff'.1 htb) (ENNReal.ofReal η)
    (ENNReal.ofReal_pos.2 hη)
  obtain ⟨T, -, hTfin, hTimg⟩ : ∃ T ⊆ (univ : Set (s11V d Λ)), T.Finite ∧ Dv '' T = t := by
    have := (Set.exists_subset_image_finite_and (f := Dv) (s := (univ : Set (s11V d Λ)))
      (p := fun t' => t' = t)).1 ⟨t, by simpa [hA, Set.image_univ] using htA, htfin, rfl⟩
    exact this
  refine ⟨hTfin.toFinset, fun v => ?_⟩
  have hv : Dv v ∈ A := ⟨v, rfl⟩
  have := hcover hv
  simp only [mem_iUnion, exists_prop] at this
  obtain ⟨y, hyt, hdist0⟩ := this
  have hdist : dist (Dv v) y < η := by
    have := (edist_lt_ofReal (x := Dv v) (y := y) (r := η)).1 hdist0
    exact this
  rw [← hTimg] at hyt
  obtain ⟨w, hwT, rfl⟩ := hyt
  refine ⟨w, by simpa using hwT, fun z hz => ?_⟩
  have h1 : dist (Dv v ⟨z, hz⟩) (Dv w ⟨z, hz⟩) ≤ dist (Dv v) (Dv w) :=
    BoundedContinuousFunction.dist_coe_le_dist _
  have h2 : dist (Dv v ⟨z, hz⟩) (Dv w ⟨z, hz⟩) = ‖fderiv ℝ v.1 z - fderiv ℝ w.1 z‖ := by
    rw [dist_eq_norm]; rfl
  rw [← h2]
  exact h1.trans hdist.le

end HRS.MS.R2S11
