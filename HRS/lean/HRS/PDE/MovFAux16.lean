import HRS.PDE.MovFAux15

/-!
# MOVF Aux16: integration by parts against a continuous weight vanishing on a finite set (`movf_libp`)

For `φ ≥ 0` continuous on `𝕋^d`, positive and `C¹` off a finite set `S` where it vanishes, with `∂_jφ ∈ L¹`, and a `C¹`
vector field `Y`: `∫ ∑_j (∂_jY_j φ + Y_j ∂_jφ) = 0`.  Proof: truncate vertically by `Φ_ε ∘ φ`
(`Φ_ε(y) = ε Φ(y/ε - 1)`, zero for `y ≤ ε`), classical torus integration by parts, `ε → 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

def movf_Phi (ε y : ℝ) : ℝ := ε * b15c_phi (y / ε - 1)

theorem movf_Phi_hasDerivAt {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (movf_Phi ε) (Real.smoothTransition (y / ε - 1)) y := by
  have h1 : HasDerivAt (fun y : ℝ => y / ε - 1) (1 / ε) y := by
    have := ((hasDerivAt_id y).div_const ε).sub_const 1
    simpa using this
  have h2 := (b15c_phi_hasDerivAt (y / ε - 1)).comp y h1
  have h3 := h2.const_mul ε
  have e : movf_Phi ε = fun y => ε * (b15c_phi ∘ fun y : ℝ => y / ε - 1) y := rfl
  rw [e]
  exact h3.congr_deriv (by field_simp)

theorem movf_Phi_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (movf_Phi ε) := by
  refine contDiff_one_iff_deriv.2 ⟨fun y => (movf_Phi_hasDerivAt hε y).differentiableAt, ?_⟩
  have : deriv (movf_Phi ε) = fun y => Real.smoothTransition (y / ε - 1) :=
    funext fun y => (movf_Phi_hasDerivAt hε y).deriv
  rw [this]
  exact Real.smoothTransition.continuous.comp ((continuous_id.div_const ε).sub continuous_const)

theorem movf_Phi_of_le {ε y : ℝ} (hε : 0 < ε) (hy : y ≤ ε) : movf_Phi ε y = 0 := by
  unfold movf_Phi
  rw [b15c_phi_of_nonpos (by rw [sub_nonpos, div_le_one hε]; exact hy), mul_zero]

theorem movf_Phi_nonneg {ε : ℝ} (hε : 0 < ε) (y : ℝ) : 0 ≤ movf_Phi ε y :=
  mul_nonneg hε.le (b15c_phi_nonneg _)

theorem movf_Phi_le {ε y : ℝ} (hε : 0 < ε) (hy : 0 ≤ y) : movf_Phi ε y ≤ y := by
  unfold movf_Phi
  rcases le_total (y / ε - 1) 0 with h | h
  · rw [b15c_phi_of_nonpos h, mul_zero]; exact hy
  · have := b15c_phi_le_of_nonneg h
    calc ε * b15c_phi (y / ε - 1) ≤ ε * (y / ε - 1) := mul_le_mul_of_nonneg_left this hε.le
      _ ≤ y := by
        have : ε * (y / ε) = y := by field_simp
        nlinarith

theorem movf_Phi_sub_le {ε y : ℝ} (hε : 0 < ε) (hy : 0 ≤ y) :
    |movf_Phi ε y - y| ≤ (2 + b15c_phi 1) * ε := by
  have hp1 : 0 ≤ b15c_phi 1 := b15c_phi_nonneg 1
  rcases le_total y (2 * ε) with h | h
  · have h1 : movf_Phi ε y ≤ b15c_phi 1 * ε := by
      unfold movf_Phi
      have : b15c_phi (y / ε - 1) ≤ b15c_phi 1 := b15c_phi_mono (by
        have : y / ε ≤ 2 := by rw [div_le_iff₀ hε]; linarith
        linarith)
      nlinarith
    have h0 := movf_Phi_nonneg hε y
    rw [abs_le]
    constructor <;> nlinarith
  · have : movf_Phi ε y = ε * b15c_phi 1 + (y - 2 * ε) := by
      unfold movf_Phi
      have hge : 1 ≤ y / ε - 1 := by
        have : 2 ≤ y / ε := by rw [le_div_iff₀ hε]; linarith
        linarith
      rw [b15c_phi_of_one_le hge]
      have : ε * (y / ε - 1 - 1) = y - 2 * ε := by field_simp; ring
      rw [mul_add, this]
    rw [this, abs_le]
    constructor <;> nlinarith

theorem movf_Phi_deriv_one {ε y : ℝ} (hε : 0 < ε) (hy : 2 * ε ≤ y) :
    Real.smoothTransition (y / ε - 1) = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : 2 ≤ y / ε := by rw [le_div_iff₀ hε]; linarith
  linarith

theorem movf_Phi_deriv_zero {ε : ℝ} (hε : 0 < ε) : Real.smoothTransition (0 / ε - 1) = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  simp

theorem movf_libp {φ : Torus d → ℝ} {S : Finset (Torus d)} {Y : Fin d → Torus d → ℝ}
    (hd : 1 ≤ d) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (hS : ∀ x ∈ S, φ x = 0)
    (hpos : ∀ x, x ∉ S → 0 < φ x)
    (hφd : ∀ y : Euc d, Torus.mk y ∉ S → ContDiffAt ℝ 1 (Torus.lift φ) y)
    (hY : ∀ j, Torus.IsCk 1 (Y j))
    (hint : ∀ j, Integrable (Torus.partialDeriv j φ)) :
    ∫ x, ∑ j, (Torus.partialDeriv j (Y j) x * φ x + Y j x * Torus.partialDeriv j φ x) = 0 := by
  have hYc : ∀ j, Continuous (Y j) := fun j => mova_continuous_of_isCk (hY j)
  have hdYc : ∀ j, Continuous (Torus.partialDeriv j (Y j)) := fun j => mova_continuous_partialDeriv (hY j) j
  -- the truncated identity
  have key : ∀ ε : ℝ, 0 < ε → ∫ x, ∑ j, (Torus.partialDeriv j (Y j) x * movf_Phi ε (φ x) +
      Y j x * (Real.smoothTransition (φ x / ε - 1) * Torus.partialDeriv j φ x)) = 0 := by
    intro ε hε
    set ψ : Torus d → ℝ := fun x => movf_Phi ε (φ x) with hψdef
    have hψ : Torus.IsCk 1 ψ := by
      unfold Torus.IsCk
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy : Torus.mk y ∈ S
      · have h0 : φ (Torus.mk y) = 0 := hS _ hy
        have hev : ∀ᶠ y' in 𝓝 y, φ (Torus.mk y') < ε :=
          ((hφc.comp Torus.continuous_mk).continuousAt (x := y)).eventually (gt_mem_nhds (by
            show φ (Torus.mk y) < ε; rw [h0]; exact hε))
        have : Torus.lift ψ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hev] with y' hy'
          exact movf_Phi_of_le hε hy'.le
        exact (contDiffAt_const).congr_of_eventuallyEq this
      · exact ((movf_Phi_contDiff hε).contDiffAt (x := Torus.lift φ y)).comp y (hφd y hy)
    have hψd : ∀ j x, Torus.partialDeriv j ψ x =
        Real.smoothTransition (φ x / ε - 1) * Torus.partialDeriv j φ x := by
      intro j x
      unfold Torus.partialDeriv
      set y := Torus.rep x with hyx
      have hmk : Torus.mk y = x := Torus.mk_rep x
      by_cases hx : x ∈ S
      · have h0 : φ x = 0 := hS _ hx
        have hev : ∀ᶠ y' in 𝓝 y, φ (Torus.mk y') < ε :=
          ((hφc.comp Torus.continuous_mk).continuousAt (x := y)).eventually (gt_mem_nhds (by
            show φ (Torus.mk y) < ε; rw [hmk, h0]; exact hε))
        have : Torus.lift ψ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hev] with y' hy'
          exact movf_Phi_of_le hε hy'.le
        rw [this.fderiv_eq, h0, movf_Phi_deriv_zero hε]
        simp
      · have hdiff := (hφd y (by rw [hmk]; exact hx)).differentiableAt (by norm_num)
        have h1 := (movf_Phi_hasDerivAt hε (Torus.lift φ y)).comp_hasFDerivAt y hdiff.hasFDerivAt
        have e : Torus.lift ψ = movf_Phi ε ∘ Torus.lift φ := rfl
        rw [e, h1.fderiv]
        simp [Torus.lift, hmk]
    have hψc : Continuous ψ := mova_continuous_of_isCk hψ
    have hsum : ∀ j, ∫ x, (Torus.partialDeriv j (Y j) x * ψ x + Y j x * Torus.partialDeriv j ψ x) = 0 := by
      intro j
      have hi1 : Integrable fun x => Torus.partialDeriv j (Y j) x * ψ x := mova_int_cont ((hdYc j).mul hψc)
      have hi2 : Integrable fun x => Y j x * Torus.partialDeriv j ψ x :=
        mova_int_cont ((hYc j).mul (mova_continuous_partialDeriv hψ j))
      rw [integral_add hi1 hi2, mova_integral_ibp j (hY j) hψ]
      ring
    have hi : ∀ j, Integrable fun x => Torus.partialDeriv j (Y j) x * ψ x + Y j x * Torus.partialDeriv j ψ x :=
      fun j => (mova_int_cont ((hdYc j).mul hψc)).add
        (mova_int_cont ((hYc j).mul (mova_continuous_partialDeriv hψ j)))
    have e : ∀ x, ∑ j, (Torus.partialDeriv j (Y j) x * movf_Phi ε (φ x) +
        Y j x * (Real.smoothTransition (φ x / ε - 1) * Torus.partialDeriv j φ x)) =
        ∑ j, (Torus.partialDeriv j (Y j) x * ψ x + Y j x * Torus.partialDeriv j ψ x) := by
      intro x
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hψd j x]
    simp_rw [e]
    rw [integral_finset_sum _ (fun j _ => hi j)]
    exact Finset.sum_eq_zero fun j _ => hsum j
  -- the limit
  obtain ⟨BY, hBY⟩ : ∃ B : ℝ, ∀ j x, |Torus.partialDeriv j (Y j) x| ≤ B := by
    have : ∀ j, ∃ B, ∀ x, |Torus.partialDeriv j (Y j) x| ≤ B := fun j => by
      obtain ⟨B, -, hB⟩ := mova_bound_of_continuous (hdYc j); exact ⟨B, hB⟩
    choose B hB using this
    refine ⟨∑ j, |B j|, fun j x => (hB j x).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun j => |B j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  obtain ⟨CY, hCY⟩ : ∃ B : ℝ, ∀ j x, |Y j x| ≤ B := by
    have : ∀ j, ∃ B, ∀ x, |Y j x| ≤ B := fun j => by
      obtain ⟨B, -, hB⟩ := mova_bound_of_continuous (hYc j); exact ⟨B, hB⟩
    choose B hB using this
    refine ⟨∑ j, |B j|, fun j x => (hB j x).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun j => |B j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hBY0 : 0 ≤ BY := (abs_nonneg _).trans (hBY ⟨0, by omega⟩ 0)
  have hCY0 : 0 ≤ CY := (abs_nonneg _).trans (hCY ⟨0, by omega⟩ 0)
  haveI : NullSingletonClass (volume : Measure (Torus d)) := ⟨fun x => volume_singleton_torus hd x⟩
  have hSnull : ∀ᵐ x : Torus d, x ∉ S := by
    have : (volume : Measure (Torus d)) (S : Set (Torus d)) = 0 := (S.finite_toSet).measure_zero _
    rw [ae_iff]
    simpa using this
  set f : ℕ → Torus d → ℝ := fun n x => ∑ j, (Torus.partialDeriv j (Y j) x * movf_Phi (1 / ((n : ℝ) + 1)) (φ x) +
      Y j x * (Real.smoothTransition (φ x / (1 / ((n : ℝ) + 1)) - 1) * Torus.partialDeriv j φ x)) with hf
  set f0 : Torus d → ℝ := fun x => ∑ j, (Torus.partialDeriv j (Y j) x * φ x + Y j x * Torus.partialDeriv j φ x)
    with hf0
  have hεn : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hmeas : ∀ n, AEStronglyMeasurable (f n) volume := by
    intro n
    refine (Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ => ?_)
    refine ((hdYc j).mul ((continuous_const.mul (b15c_phi_contDiff.continuous.comp
      ((hφc.div_const _).sub continuous_const)))) |>.aestronglyMeasurable).add ?_
    exact ((hYc j).aestronglyMeasurable).mul ((Real.smoothTransition.continuous.comp
      ((hφc.div_const _).sub continuous_const)).aestronglyMeasurable.mul (hint j).aestronglyMeasurable)
  have hbound : ∀ n, ∀ᵐ x ∂(volume : Measure (Torus d)), ‖f n x‖ ≤
      ∑ j, (BY * φ x + CY * |Torus.partialDeriv j φ x|) := by
    intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (movf_Phi_nonneg (hεn n) _)]
      exact mul_le_mul (hBY j x) (movf_Phi_le (hεn n) (hφ0 x)) (movf_Phi_nonneg (hεn n) _ |>.trans' le_rfl) hBY0
    · rw [abs_mul, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      have h1 : Real.smoothTransition (φ x / (1 / ((n : ℝ) + 1)) - 1) ≤ 1 := Real.smoothTransition.le_one _
      calc |Y j x| * (Real.smoothTransition (φ x / (1 / ((n : ℝ) + 1)) - 1) * |Torus.partialDeriv j φ x|)
          ≤ CY * (1 * |Torus.partialDeriv j φ x|) :=
            mul_le_mul (hCY j x) (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
              (mul_nonneg (Real.smoothTransition.nonneg _) (abs_nonneg _)) hCY0
        _ = CY * |Torus.partialDeriv j φ x| := by ring
  have hbint : Integrable (fun x => ∑ j : Fin d, (BY * φ x + CY * |Torus.partialDeriv j φ x|)) := by
    refine integrable_finsetSum _ fun j _ => ?_
    exact (mova_int_cont (continuous_const.mul hφc)).add ((hint j).abs.const_mul CY)
  have hlim : ∀ᵐ x ∂(volume : Measure (Torus d)), Tendsto (fun n => f n x) atTop (𝓝 (f0 x)) := by
    filter_upwards [hSnull] with x hx
    have hp := hpos x hx
    have hε0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hPhi : Tendsto (fun n : ℕ => movf_Phi (1 / ((n : ℝ) + 1)) (φ x)) atTop (𝓝 (φ x)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
        (by simpa using hε0.const_mul (2 + b15c_phi 1) : Tendsto (fun n : ℕ => (2 + b15c_phi 1) *
          (1 / ((n : ℝ) + 1))) atTop (𝓝 0))
      rw [Real.dist_eq]
      exact movf_Phi_sub_le (hεn n) (hφ0 x)
    have hST : ∀ᶠ n : ℕ in atTop, Real.smoothTransition (φ x / (1 / ((n : ℝ) + 1)) - 1) = 1 := by
      have : ∀ᶠ n : ℕ in atTop, 2 * (1 / ((n : ℝ) + 1)) ≤ φ x :=
        (hε0.eventually (gt_mem_nhds (show (0 : ℝ) < φ x / 2 by linarith))).mono fun n hn => by
          linarith
      filter_upwards [this] with n hn
      exact movf_Phi_deriv_one (hεn n) hn
    refine tendsto_finsetSum _ fun j _ => ?_
    refine Tendsto.add ((tendsto_const_nhds).mul hPhi) ?_
    refine tendsto_const_nhds.mul ?_
    exact (tendsto_const_nhds (x := Torus.partialDeriv j φ x)).congr'
      (hST.mono fun n hn => by beta_reduce; rw [hn, one_mul])
  have hT := tendsto_integral_of_dominated_convergence _ hmeas hbint hbound hlim
  have hzero : ∀ n, ∫ x, f n x = 0 := fun n => key _ (hεn n)
  simp only [hzero] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end HRS

end
