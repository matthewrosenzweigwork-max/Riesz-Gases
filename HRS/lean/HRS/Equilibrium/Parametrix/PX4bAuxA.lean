import HRS.Equilibrium.Parametrix.PX3aAuxAA
import HRS.Equilibrium.Parametrix.PX2AuxE
import HRS.Equilibrium.Parametrix.PX1AuxExtApply
import HRS.PDE.MeanFieldSchauder

/-!
# Packet PX4b auxiliaries A: smooth bumps on the torus
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Distance from `mk w` to `0` in the torus: `‖centeredRep (mk w)‖`. -/
def px4b_D (w : Euc d) : ℝ := ‖Torus.centeredRep (Torus.mk w)‖

lemma px4b_D_le (w w' : Euc d) : px4b_D w ≤ px4b_D w' + ‖w - w'‖ := by
  obtain ⟨n', hn', hc⟩ := cR_exists_lat w'
  have h1 := norm_cR_le w n' hn'
  have h2 : ‖w - n'‖ ≤ ‖w - w'‖ + ‖w' - n'‖ := by
    calc ‖w - n'‖ = ‖(w - w') + (w' - n')‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  unfold px4b_D
  rw [hc]
  linarith

lemma px4b_D_lip (w w' : Euc d) : |px4b_D w - px4b_D w'| ≤ ‖w - w'‖ := by
  rw [abs_le]
  have h1 := px4b_D_le w w'
  have h2 := px4b_D_le w' w
  rw [norm_sub_rev] at h2
  constructor <;> linarith

lemma px4b_D_eq_of_small {w : Euc d} (hw : ‖w‖ < 1 / 2) : px4b_D w = ‖w‖ := by
  unfold px4b_D
  rw [cR_mk_of_small w (norm_coord_lt_half hw)]

lemma px4b_D_sub_lat (w n : Euc d) (hn : IsLat n) : px4b_D (w - n) = px4b_D w := by
  unfold px4b_D
  rw [mk_sub_eq, mk_isLat hn, sub_zero]

lemma px4b_D_nonneg (w : Euc d) : 0 ≤ px4b_D w := norm_nonneg _

/-- The lift of a bump: `v ↦ b (centeredRep (mk v))` is smooth when `b` is smooth and supported in
`‖x‖ < 1/8`. -/
lemma px4b_contDiff_bump_cR {b : Euc d → ℝ} (hb : ContDiff ℝ ∞' b) (hs : ∀ x, b x ≠ 0 → ‖x‖ < 1 / 8) :
    ContDiff ℝ ∞' (fun v : Euc d => b (Torus.centeredRep (Torus.mk v))) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  obtain ⟨n, hn, hc⟩ := cR_exists_lat v
  by_cases h : ‖v - n‖ < 1 / 4
  · -- near `v`, the centred representative is `v' - n`
    have hev : (fun v' : Euc d => b (Torus.centeredRep (Torus.mk v'))) =ᶠ[𝓝 v] fun v' => b (v' - n) := by
      have hopen : IsOpen {v' : Euc d | ‖v' - n‖ < 1 / 2} :=
        isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
      filter_upwards [hopen.mem_nhds (show v ∈ {v' : Euc d | ‖v' - n‖ < 1 / 2} by
        show ‖v - n‖ < 1 / 2; linarith)] with v' hv'
      have : Torus.centeredRep (Torus.mk v') = v' - n := by
        have hmk : Torus.mk (v' - n) = Torus.mk v' := by rw [mk_sub_eq, mk_isLat hn, sub_zero]
        rw [← hmk]
        exact cR_mk_of_small _ (norm_coord_lt_half hv')
      rw [this]
    exact ((hb.comp (contDiff_id.sub contDiff_const)).contDiffAt).congr_of_eventuallyEq hev
  · push Not at h
    have hev : (fun v' : Euc d => b (Torus.centeredRep (Torus.mk v'))) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds v (show (0 : ℝ) < 1 / 8 by norm_num)] with v' hv'
      by_contra hne
      have h1 := hs _ hne
      have h2 : px4b_D v' < 1 / 8 := h1
      have h3 := px4b_D_le v v'
      have h4 : px4b_D v = ‖v - n‖ := by
        unfold px4b_D; rw [hc]
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hv'
      rw [norm_sub_rev] at h3
      have : ‖v - v'‖ = ‖v' - v‖ := norm_sub_rev _ _
      linarith
    exact (contDiffAt_const).congr_of_eventuallyEq hev


lemma px4b_D_neg (w : Euc d) : px4b_D (-w) = px4b_D w := by
  obtain ⟨n, hn, hc⟩ := cR_exists_lat w
  have h1 : px4b_D w = ‖w - n‖ := by unfold px4b_D; rw [hc]
  have hmin := norm_cR_le (-w) (-n) (fun i => by
    obtain ⟨k, hk⟩ := hn i; exact ⟨-k, by simp [hk]⟩)
  have h2 : ‖-w - -n‖ = ‖w - n‖ := by rw [← norm_neg]; congr 1; abel
  have h3 : px4b_D (-w) ≤ px4b_D w := by unfold px4b_D at h1 ⊢; rw [h1, ← h2]; exact hmin
  have hmin' := norm_cR_le w n hn
  -- reverse inequality by applying the same to `-w`
  have h4 : px4b_D w ≤ px4b_D (-w) := by
    obtain ⟨n', hn', hc'⟩ := cR_exists_lat (-w)
    have h5 : px4b_D (-w) = ‖-w - n'‖ := by unfold px4b_D; rw [hc']
    have hm := norm_cR_le w (-n') (fun i => by
      obtain ⟨k, hk⟩ := hn' i; exact ⟨-k, by simp [hk]⟩)
    have h6 : ‖w - -n'‖ = ‖-w - n'‖ := by rw [← norm_neg]; congr 1; abel
    unfold px4b_D at h5 ⊢; rw [h5, ← h6]; exact hm
  exact le_antisymm h3 h4

lemma px4b_D_add (a b : Euc d) : px4b_D (a + b) ≤ px4b_D a + px4b_D b := by
  obtain ⟨n, hn, hc⟩ := cR_exists_lat b
  have h1 : px4b_D b = ‖b - n‖ := by unfold px4b_D; rw [hc]
  have h2 : px4b_D (a + b) = px4b_D (a + b - n) := (px4b_D_sub_lat _ n hn).symm
  have h3 := px4b_D_le (a + b - n) a
  have h4 : a + b - n - a = b - n := by abel
  rw [h4] at h3
  rw [h2]
  linarith

lemma px4b_D_sub (a b : Euc d) : px4b_D (a - b) ≤ px4b_D a + px4b_D b := by
  have := px4b_D_add a (-b)
  rw [px4b_D_neg] at this
  simpa [sub_eq_add_neg] using this

/-- A smooth bump on the torus around `mk c`: `= 1` where `D (v - c) ≤ δ`, `= 0` where
`D (v - c) ≥ 2 δ`. -/
lemma px4b_exists_bump (c : Euc d) {δ : ℝ} (hδ : 0 < δ) (hδ8 : 2 * δ ≤ 1 / 8) :
    ∃ φ : Torus d → ℝ, Torus.IsSmooth φ ∧ (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧
      (∀ v : Euc d, px4b_D (v - c) ≤ δ → φ (Torus.mk v) = 1) ∧
      (∀ v : Euc d, 2 * δ ≤ px4b_D (v - c) → φ (Torus.mk v) = 0) := by
  let b : ContDiffBump (0 : Euc d) := ⟨δ, 2 * δ, hδ, by linarith⟩
  let φ : Torus d → ℝ := fun u => b (Torus.centeredRep (u - Torus.mk c))
  have hφv : ∀ v : Euc d, φ (Torus.mk v) = b (Torus.centeredRep (Torus.mk (v - c))) := by
    intro v
    simp only [φ]
    rw [mk_sub_eq]
  refine ⟨φ, ?_, fun u => ⟨b.nonneg, b.le_one⟩, ?_, ?_⟩
  · have hs : ∀ x, b x ≠ 0 → ‖x‖ < 1 / 8 := by
      intro x hx
      have : x ∈ Function.support b := hx
      rw [ContDiffBump.support_eq] at this
      have h2 : ‖x‖ < 2 * δ := by simpa [b] using this
      linarith
    have h1 := px4b_contDiff_bump_cR (d := d) (b := b) b.contDiff hs
    have h2 : Torus.lift φ = fun v => b (Torus.centeredRep (Torus.mk (v - c))) := by
      funext v; exact hφv v
    show ContDiff ℝ ∞' (Torus.lift φ)
    rw [h2]
    exact h1.comp (contDiff_id.sub contDiff_const)
  · intro v hv
    rw [hφv]
    apply ContDiffBump.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff]
    exact hv
  · intro v hv
    rw [hφv]
    apply ContDiffBump.zero_of_le_dist
    rw [dist_zero_right]
    exact hv


lemma px4b_D_mk_zero {v : Euc d} (hv : Torus.mk v = 0) : px4b_D v = 0 := by
  unfold px4b_D
  rw [hv]
  have : Torus.mk (0 : Euc d) = 0 := mk_isLat isLat_zero
  rw [← this, cR_mk_of_small 0 (fun i => by simp)]
  simp

lemma px4b_isOpen_D_lt (v0 : Euc d) (r : ℝ) : IsOpen {v : Euc d | px4b_D (v - v0) < r} := by
  have hc : Continuous (fun v : Euc d => px4b_D (v - v0)) := by
    refine continuous_iff_continuousAt.2 fun v => ?_
    refine Metric.continuousAt_iff.2 fun ε hε => ⟨ε, hε, fun v' hv' => ?_⟩
    rw [Real.dist_eq]
    have := px4b_D_lip (v' - v0) (v - v0)
    rw [show v' - v0 - (v - v0) = v' - v by abel] at this
    rw [dist_eq_norm] at hv'
    linarith
  exact isOpen_lt hc continuous_const

/-- Splitting of an integrable kernel smooth off zero into a part supported near `0` and a
globally `C^1` part. -/
lemma px4b_gsplit {g : Torus d → ℝ} (hg : Integrable g) (hgs : Torus.IsSmoothOffZero g) {δ : ℝ}
    (hδ : 0 < δ) (hδ8 : 2 * δ ≤ 1 / 8) :
    ∃ gn gf : Torus d → ℝ, (∀ u, g u = gn u + gf u) ∧ Integrable gn ∧
      (∀ w : Euc d, 2 * δ ≤ px4b_D w → gn (Torus.mk w) = 0) ∧ Torus.IsCk 1 gf := by
  obtain ⟨ψ, hψs, hψ01, hψ1, hψ0⟩ := px4b_exists_bump (d := d) 0 hδ hδ8
  have hψc : Continuous ψ := continuous_of_isSmooth hψs
  refine ⟨fun u => g u * ψ u, fun u => g u * (1 - ψ u), fun u => by ring, ?_, ?_, ?_⟩
  · refine hg.mul_bdd (c := 1) hψc.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ01 u).1]
    exact (hψ01 u).2
  · intro w hw
    have := hψ0 w (by simpa using hw)
    simp [this]
  · show ContDiff ℝ 1 (Torus.lift fun u => g u * (1 - ψ u))
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : Torus.mk v = 0
    · have hD : px4b_D v = 0 := px4b_D_mk_zero hv
      have hev : Torus.lift (fun u => g u * (1 - ψ u)) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
        filter_upwards [(px4b_isOpen_D_lt 0 δ).mem_nhds (show px4b_D (v - 0) < δ by
          rw [sub_zero, hD]; exact hδ)] with v' hv'
        have h1 : ψ (Torus.mk v') = 1 := hψ1 v' (by rw [sub_zero]; rw [sub_zero] at hv'; exact hv'.le)
        simp [Torus.lift, h1]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hg1 : ContDiffAt ℝ 1 (Torus.lift g) v :=
        ((hgs.contDiffAt (isOpen_mk_ne_zero'.mem_nhds hv)).of_le (by exact_mod_cast le_top))
      have hψ1' : ContDiffAt ℝ 1 (Torus.lift ψ) v :=
        ((show ContDiff ℝ ∞' (Torus.lift ψ) from hψs).contDiffAt.of_le (by exact_mod_cast le_top))
      exact hg1.mul (contDiffAt_const.sub hψ1')


lemma px4b_convFun_comm (a b : Torus d → ℝ) (x : Torus d) : convFun a b x = convFun b a x := by
  unfold convFun
  rw [← integral_sub_left_eq_self (fun y => a (x - y) * b y) volume x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

/-- Decomposition of `g ⋆ h` near a lifted point `v0`: `g = gn + gf` (near part and smooth part) and
`h φ` a globally `C¹` function agreeing with `h` near `v0`. -/
theorem px4b_convFun_split {g h : Torus d → ℝ} (hg : Integrable g) (hgs : Torus.IsSmoothOffZero g)
    (hh : Integrable h) (v0 : Euc d) {δ : ℝ} (hδ : 0 < δ) (hδ' : 6 * δ ≤ 1 / 8)
    (hloc : ∀ v : Euc d, px4b_D (v - v0) < 8 * δ → ContDiffAt ℝ 1 (Torus.lift h) v) :
    ∃ gn gf hφ : Torus d → ℝ, (∀ u, g u = gn u + gf u) ∧ Integrable gn ∧ Torus.IsCk 1 gf ∧
      Torus.IsCk 1 hφ ∧ (∀ w : Euc d, 2 * δ ≤ px4b_D w → gn (Torus.mk w) = 0) ∧
      (∀ v : Euc d, px4b_D (v - v0) < 3 * δ → hφ (Torus.mk v) = h (Torus.mk v)) ∧
      ∀ z : Euc d, px4b_D (z - v0) < δ →
        Integrable (fun w => g (Torus.mk z - w) * h w) ∧
        convFun g h (Torus.mk z) = convFun gn hφ (Torus.mk z) + convFun gf h (Torus.mk z) := by
  obtain ⟨gn, gf, hsum, hgn, hgn0, hgf⟩ := px4b_gsplit hg hgs (δ := δ) hδ (by linarith)
  obtain ⟨φ, hφs, hφ01, hφ1, hφ0⟩ := px4b_exists_bump v0 (δ := 3 * δ) (by linarith) (by linarith)
  have hφc : ContDiff ℝ 1 (Torus.lift φ) :=
    (show ContDiff ℝ ∞' (Torus.lift φ) from hφs).of_le (by exact_mod_cast le_top)
  have hhφ : Torus.IsCk 1 (fun u => h u * φ u) := by
    show ContDiff ℝ 1 (Torus.lift fun u => h u * φ u)
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : px4b_D (v - v0) < 8 * δ
    · exact (hloc v hv).mul hφc.contDiffAt
    · push Not at hv
      have hev : Torus.lift (fun u => h u * φ u) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds v (show (0 : ℝ) < 2 * δ by linarith)] with v' hv'
        have h1 := px4b_D_lip (v - v0) (v' - v0)
        rw [show v - v0 - (v' - v0) = v - v' by abel] at h1
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hv'
        have h2 : 2 * (3 * δ) ≤ px4b_D (v' - v0) := by
          have := (abs_le.1 h1).2
          linarith
        simp [Torus.lift, hφ0 v' h2]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hgfc : Continuous gf := KernelGrad.continuous_of_lift hgf.continuous
  have hhφc : Continuous (fun u => h u * φ u) := KernelGrad.continuous_of_lift hhφ.continuous
  have hpt : ∀ z : Euc d, px4b_D (z - v0) < δ → ∀ w : Torus d,
      g (Torus.mk z - w) * h w =
        gn (Torus.mk z - w) * (h w * φ w) + gf (Torus.mk z - w) * h w := by
    intro z hz w
    rw [hsum (Torus.mk z - w), add_mul]
    congr 1
    by_cases h0 : gn (Torus.mk z - w) = 0
    · simp [h0]
    · have hw := Torus.mk_rep w
      have hmk : Torus.mk z - w = Torus.mk (z - Torus.rep w) := by rw [mk_sub_eq, hw]
      rw [hmk] at h0
      have hD : px4b_D (z - Torus.rep w) < 2 * δ := by
        by_contra hcon
        exact h0 (hgn0 _ (not_lt.1 hcon))
      have hD3 : px4b_D (Torus.rep w - v0) ≤ 3 * δ := by
        have := px4b_D_add (Torus.rep w - z) (z - v0)
        rw [show Torus.rep w - z + (z - v0) = Torus.rep w - v0 by abel] at this
        have hneg : px4b_D (Torus.rep w - z) = px4b_D (z - Torus.rep w) := by
          rw [← px4b_D_neg]; congr 1; abel
        linarith
      have := hφ1 (Torus.rep w) hD3
      rw [hw] at this
      rw [this]; ring
  have hI1 : ∀ z : Euc d, Integrable (fun w => gn (Torus.mk z - w) * (h w * φ w)) := by
    intro z
    obtain ⟨B, hB⟩ := PDE.MFSchauder.exists_bound_of_cont hhφc
    refine (hgn.comp_sub_left (Torus.mk z)).mul_bdd (c := B) hhφc.aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    simpa using hB w
  have hI2 : ∀ z : Euc d, Integrable (fun w => gf (Torus.mk z - w) * h w) := by
    intro z
    obtain ⟨B, hB⟩ := PDE.MFSchauder.exists_bound_of_cont hgfc
    refine hh.bdd_mul (c := B) (f := fun w => gf (Torus.mk z - w))
      (hgfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    simpa using hB (Torus.mk z - w)
  refine ⟨gn, gf, fun u => h u * φ u, hsum, hgn, hgf, hhφ, hgn0, ?_, ?_⟩
  · intro v hv
    show h (Torus.mk v) * φ (Torus.mk v) = h (Torus.mk v)
    rw [hφ1 v hv.le, mul_one]
  · intro z hz
    refine ⟨?_, ?_⟩
    · have := (hI1 z).add (hI2 z)
      refine this.congr (Eventually.of_forall fun w => ?_)
      exact (hpt z hz w).symm
    · show convFun g h (Torus.mk z) = convFun gn (fun u => h u * φ u) (Torus.mk z) +
        convFun gf h (Torus.mk z)
      unfold convFun
      rw [← integral_add (hI1 z) (hI2 z)]
      exact integral_congr_ae (Eventually.of_forall fun w => hpt z hz w)

/-- Local differentiability of `g ⋆ h` for an integrable kernel `g` smooth off `0` and an integrable
`h` that is `C¹` near the lifted point `v0` (Euclidean/torus radius `8 δ`). -/
theorem px4b_convFun_local {g h : Torus d → ℝ} (hg : Integrable g) (hgs : Torus.IsSmoothOffZero g)
    (hh : Integrable h) (v0 : Euc d) {δ : ℝ} (hδ : 0 < δ) (hδ' : 6 * δ ≤ 1 / 8)
    (hloc : ∀ v : Euc d, px4b_D (v - v0) < 8 * δ → ContDiffAt ℝ 1 (Torus.lift h) v) :
    ∀ z : Euc d, px4b_D (z - v0) < δ →
      Integrable (fun w => g (Torus.mk z - w) * h w) ∧
      DifferentiableAt ℝ (Torus.lift (convFun g h)) z := by
  obtain ⟨gn, gf, hφ, hsum, hgn, hgf, hhφ, hgn0, hagree, hz⟩ :=
    px4b_convFun_split hg hgs hh v0 hδ hδ' hloc
  intro z hz'
  refine ⟨(hz z hz').1, ?_⟩
  have hd1 := PDE.MFSchauder.convFun_hasFDerivAt hgn hhφ z
  have hd2 := PDE.MFSchauder.convFun_hasFDerivAt hh hgf z
  have e2 : Torus.lift (convFun gf h) = Torus.lift (convFun h gf) := by
    funext v; exact px4b_convFun_comm gf h (Torus.mk v)
  rw [← e2] at hd2
  have hsum' := hd1.add hd2
  refine (hsum'.differentiableAt).congr_of_eventuallyEq ?_
  filter_upwards [(px4b_isOpen_D_lt v0 δ).mem_nhds hz'] with v hv
  simp only [Pi.add_apply, Torus.lift, Function.comp]
  exact (hz v hv).2

end HRS.Parx
end
