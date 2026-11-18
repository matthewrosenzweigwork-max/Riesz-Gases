import HRS.MS.SA12DE7C
import HRS.MS.SA12V3M
import HRS.MS.AdjRdNorms

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part D: the `H^m` norm of the cut-off mollified datum

`sa12de7_cut_mollify_norm`: for `φ ∈ H^m`, `ζ` a cutoff and `η` a mollifier, for every `δ > 0` there are `L₀ ≥ 1`, `ε₀ > 0` with
`‖ζ(·/L) (η_ε * φ)‖_{H^m} ≤ ‖φ‖_{H^m} + δ` for all `L ≥ L₀`, `0 < ε ≤ ε₀`.  (Density of `C_c^∞` in `H^m`, the uniform
multiplier bound `sa12v3_zeta_mul`, the mollifier contraction, and part C; no interchange of cutoff and mollifier.)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd.FourierAux HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Limit HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12V3

variable {d : ℕ}

theorem sa12de7_mollify_sub {η : Euc d → ℝ} (hη : IsMollifier η) {ε : ℝ} (hε : 0 < ε) {φ ψ : Euc d → ℝ}
    (hφ : MemLp φ 2 volume) (hψ : MemLp ψ 2 volume) :
    mollify η ε (fun y => φ y - ψ y) = fun x => mollify η ε φ x - mollify η ε ψ x := by
  funext x
  have hG2 : MemLp (sa12v3_G η ε) 2 volume :=
    (sa12v3_G_cont hη ε).memLp_of_hasCompactSupport (by
      unfold sa12v3_G
      exact (hη.2.1.comp_smul (inv_ne_zero hε.ne')).mul_left)
  have hint : ∀ f : Euc d → ℝ, MemLp f 2 volume → Integrable (fun y => sa12v3_G η ε y * f (x - y)) volume := by
    intro f hf
    have h1 : MemLp (fun y => f (x - y)) 2 volume :=
      hf.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
    exact hG2.integrable_mul h1
  have e : ∀ f : Euc d → ℝ, mollify η ε f x = ∫ y, sa12v3_G η ε y * f (x - y) := fun f => rfl
  rw [e, e, e, ← integral_sub (hint φ hφ) (hint ψ hψ)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mul_sub]

theorem sa12de7_normE_cc (m : ℕ) {w : Euc d → ℝ} (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) :
    sobolevNormE (m : ℝ) w = ENNReal.ofReal (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) w)) := by
  unfold sobolevNormE
  rw [if_pos (sa12de7_memSobolev m hw hc)]

theorem sa12de7_mollify_cc {η : Euc d → ℝ} (hη : IsMollifier η) {ψ : Euc d → ℝ} (hψ1 : ContDiff ℝ ∞ ψ)
    (hψ2 : HasCompactSupport ψ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ContDiff ℝ ∞ (fun x => mollify η ε ψ x - ψ x) ∧ HasCompactSupport (fun x => mollify η ε ψ x - ψ x) := by
  obtain ⟨R, hR⟩ := hψ2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hRψ : ∀ x : Euc d, R < ‖x‖ → ψ x = 0 := fun x hx => by
    by_contra h
    have := hR (subset_tsupport _ (Function.mem_support.2 h))
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  refine ⟨(sa12v3_mollify_smooth hη hε0 hψ1.continuous.locallyIntegrable).sub hψ1, ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (R + 1)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  show mollify η ε ψ x - ψ x = 0
  rw [sa12de7_mollify_supp hη hε0 hε1 hRψ hx, hRψ x (by linarith)]
  simp

theorem sa12de7_cut_mollify_norm (m : ℕ) {ζ η : Euc d → ℝ}
    (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) (hη : IsMollifier η) {φ : Euc d → ℝ}
    (hφ : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
      sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * mollify η (min ε 1) φ x) ≤
        sobolevNormE (m : ℝ) φ + ENNReal.ofReal δ := by
  obtain ⟨C, hC0, hCz⟩ := sa12v3_zeta_mul m hζ.1 hζ.2.1
  set α : ℝ := δ / (4 * (C + 1)) with hα
  have hα0 : 0 < α := by positivity
  obtain ⟨ψ, hψcc, hψmem, hψsq⟩ := sa12y_ccdense m hφ hα0
  have hψ1 : ContDiff ℝ ∞ ψ := hψcc.1
  have hψ2 : HasCompactSupport ψ := hψcc.2
  have hN1 : sobolevNormE (m : ℝ) (fun x => ψ x - φ x) ≤ ENNReal.ofReal α := by
    unfold sobolevNormE
    rw [if_pos hψmem]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) fun x => ψ x - φ x) ≤ Real.sqrt (α ^ 2) :=
          Real.sqrt_le_sqrt hψsq
      _ = α := Real.sqrt_sq hα0.le
  obtain ⟨R, hR⟩ := hψ2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hRψ : ∀ x : Euc d, R < ‖x‖ → ψ x = 0 := fun x hx => by
    by_contra h
    have := hR (subset_tsupport _ (Function.mem_support.2 h))
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hMH := sa12de7_mollify_H hη m hψ1 hψ2 (δ := α ^ 2) (by positivity)
  obtain ⟨ε1, hε1, hsub⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 hMH
  have hε1pos : 0 < ε1 := hε1
  refine ⟨max 1 (4 * R), le_max_left _ _, min ε1 1, lt_min hε1pos one_pos, ?_⟩
  intro L hL ε hε hεle
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL4 : 4 * R ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hε1' : ε ≤ 1 := hεle.trans (min_le_right _ _)
  rw [min_eq_left hε1']
  have hεε1 : ε ∈ Ioc (0 : ℝ) ε1 := ⟨hε, hεle.trans (min_le_left _ _)⟩
  have hMψ : HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => mollify η ε ψ x - ψ x) ≤ α ^ 2 := hsub hεε1
  have hφ2 : MemLp φ 2 volume := hφ.1
  have hψL2 : MemLp ψ 2 volume := hψ1.continuous.memLp_of_hasCompactSupport hψ2
  obtain ⟨hwsm, hwc⟩ := sa12de7_mollify_cc hη hψ1 hψ2 hε hε1'
  have hN2 : sobolevNormE (m : ℝ) (fun x => mollify η ε ψ x - ψ x) ≤ ENNReal.ofReal α := by
    rw [sa12de7_normE_cc m hwsm hwc]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) fun x => mollify η ε ψ x - ψ x) ≤ Real.sqrt (α ^ 2) :=
          Real.sqrt_le_sqrt hMψ
      _ = α := Real.sqrt_sq hα0.le
  -- the three pieces
  have hdecomp : (fun x => ζ (L⁻¹ • x) * mollify η ε φ x) = fun x =>
      (ζ (L⁻¹ • x) * mollify η ε (fun y => φ y - ψ y) x +
        ζ (L⁻¹ • x) * (mollify η ε ψ x - ψ x)) + ζ (L⁻¹ • x) * ψ x := by
    funext x
    rw [sa12de7_mollify_sub hη hε hφ2 hψL2]
    ring
  have hA : sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * mollify η ε (fun y => φ y - ψ y) x) ≤
      ENNReal.ofReal C * ENNReal.ofReal α := by
    refine (hCz L hL1 _).trans (mul_le_mul' le_rfl ?_)
    refine (sa12v3_mollify_sobolevNormE_le hη hε _ _).trans ?_
    have e : (fun y => φ y - ψ y) = fun y => -(ψ y - φ y) := by funext y; ring
    rw [e]
    exact (sa12v3_sobolevNormE_neg_le _ _).trans hN1
  have hB : sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * (mollify η ε ψ x - ψ x)) ≤
      ENNReal.ofReal C * ENNReal.ofReal α :=
    (hCz L hL1 _).trans (mul_le_mul' le_rfl hN2)
  have hCc : sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * ψ x) ≤ sobolevNormE (m : ℝ) φ + ENNReal.ofReal α := by
    have e1 : (fun x => ζ (L⁻¹ • x) * ψ x) = ψ := by
      funext x
      by_cases hx : R < ‖x‖
      · rw [hRψ x hx]; simp
      · have : ζ (L⁻¹ • x) = 1 := by
          apply hζ.2.2.2.2
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL0,
            inv_mul_le_iff₀ hL0]
          nlinarith [not_lt.1 hx]
        rw [this, one_mul]
    have e2 : ψ = fun x => φ x + (ψ x - φ x) := by funext x; ring
    rw [e1]
    calc sobolevNormE (m : ℝ) ψ = sobolevNormE (m : ℝ) (fun x => φ x + (ψ x - φ x)) := by rw [← e2]
      _ ≤ sobolevNormE (m : ℝ) φ + sobolevNormE (m : ℝ) (fun x => ψ x - φ x) :=
          sa12v3_sobolevNormE_add_le _ _ _
      _ ≤ _ := add_le_add le_rfl hN1
  rw [hdecomp]
  calc sobolevNormE (m : ℝ) (fun x => (ζ (L⁻¹ • x) * mollify η ε (fun y => φ y - ψ y) x +
        ζ (L⁻¹ • x) * (mollify η ε ψ x - ψ x)) + ζ (L⁻¹ • x) * ψ x)
      ≤ sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * mollify η ε (fun y => φ y - ψ y) x +
          ζ (L⁻¹ • x) * (mollify η ε ψ x - ψ x)) + sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * ψ x) :=
        sa12v3_sobolevNormE_add_le _ _ _
    _ ≤ (sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * mollify η ε (fun y => φ y - ψ y) x) +
          sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * (mollify η ε ψ x - ψ x))) +
          sobolevNormE (m : ℝ) (fun x => ζ (L⁻¹ • x) * ψ x) :=
        add_le_add (sa12v3_sobolevNormE_add_le _ _ _) le_rfl
    _ ≤ (ENNReal.ofReal C * ENNReal.ofReal α + ENNReal.ofReal C * ENNReal.ofReal α) +
          (sobolevNormE (m : ℝ) φ + ENNReal.ofReal α) := add_le_add (add_le_add hA hB) hCc
    _ = sobolevNormE (m : ℝ) φ + ENNReal.ofReal (C * α + C * α + α) := by
        rw [← ENNReal.ofReal_mul hC0, ENNReal.ofReal_add (by positivity) hα0.le,
          ENNReal.ofReal_add (by positivity) (by positivity)]
        ring
    _ ≤ sobolevNormE (m : ℝ) φ + ENNReal.ofReal δ := by
        refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
        have : (2 * C + 1) * α ≤ δ := by
          rw [hα]
          have h1 : (2 * C + 1) * (δ / (4 * (C + 1))) = δ * ((2 * C + 1) / (4 * (C + 1))) := by ring
          rw [h1]
          have h2 : (2 * C + 1) / (4 * (C + 1)) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith
        nlinarith

end HRS.MS.SA12DE7
