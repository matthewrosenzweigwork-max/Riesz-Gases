import HRS.MS.CritForceLead2

/-!
# S8.2 NormalForm packet P05, part 3: `-2ν Δ (leading inverse) = -(s/2) |z|^{-s} B(ω,ω)`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S82N

open HRS

variable {d : ℕ}

lemma s82n_lap_combo (f1 f2 : Euc d → ℝ) (A c2 K : ℝ) (z : Euc d)
    (h1 : ContDiffAt ℝ 2 f1 z) (h2 : ContDiffAt ℝ 2 f2 z) :
    Laplacian.laplacian (fun w => A * f1 w - c2 * f2 w + K) z =
      A * Laplacian.laplacian f1 z - c2 * Laplacian.laplacian f2 z := by
  have e : (fun w => A * f1 w - c2 * f2 w + K) = (A • f1 - c2 • f2) + (fun _ => K) := by
    funext w; simp [smul_eq_mul]
  have hA : ContDiffAt ℝ 2 (A • f1) z := h1.const_smul A
  have hC : ContDiffAt ℝ 2 (c2 • f2) z := h2.const_smul c2
  have hAC : ContDiffAt ℝ 2 (A • f1 - c2 • f2) z := hA.sub hC
  rw [e, ContDiffAt.laplacian_add hAC (contDiffAt_const (c := K)), ContDiffAt.laplacian_sub hA hC,
    InnerProductSpace.laplacian_smul A h1, InnerProductSpace.laplacian_smul c2 h2]
  simp

lemma s82n_cd_radial (z : Euc d) (g : ℝ → ℝ) (hg : ContDiffAt ℝ 2 g (‖z‖ ^ 2)) :
    ContDiffAt ℝ 2 (fun w : Euc d => g (‖w‖ ^ 2)) z :=
  hg.comp z (contDiff_norm_sq ℝ).contDiffAt

lemma s82n_cd_quad_rpow (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (z : Euc d) (hz : z ≠ 0) (a : ℝ) :
    ContDiffAt ℝ 2 (fun x : Euc d => B x x * (‖x‖ ^ 2) ^ a) z := by
  have ht : ‖z‖ ^ 2 ≠ 0 := by positivity
  have h1 : ContDiffAt ℝ 2 (fun x : Euc d => B x x) z :=
    ((contDiff_const (c := B)).clm_apply contDiff_id).clm_apply contDiff_id |>.contDiffAt
  exact h1.mul (s82n_cd_radial z (fun v => v ^ a) (Real.contDiffAt_rpow_const_of_ne ht))

lemma s82n_trace_eq (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) :
    (∑ i : Fin d, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
      ∑ i, B (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  simp [EuclideanSpace.basisFun_apply]

lemma s82n_rpow_split (w : Euc d) (hw : w ≠ 0) (s : ℝ) :
    ‖w‖ ^ (2 - s) = ‖w‖ ^ 2 * (‖w‖ ^ 2) ^ (-s / 2) ∧
      (‖w‖ ^ 2) ^ (-s / 2) = ‖w‖ ^ (-s) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 : (‖w‖ ^ 2) ^ (-s / 2) = ‖w‖ ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1; push_cast; ring
  refine ⟨?_, h1⟩
  rw [h1, sub_eq_add_neg, Real.rpow_add hr, ← Real.rpow_two]

lemma s82n_omega_quad (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (w : Euc d) (hw : w ≠ 0) :
    B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) = (‖w‖ ^ 2)⁻¹ * B w w := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hr : ‖w‖ ≠ 0 := (norm_pos_iff.2 hw).ne'
  field_simp

/-- The leading inverse solves `-2ν Δ L = -(s/2) |z|^{-s} B(ω,ω)` away from the origin. -/
theorem s82n_leading_laplacian (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (z : Euc d) (hz : z ≠ 0) :
    -2 * nu * Laplacian.laplacian (s82n_leadingInverse nu B) z =
      -(s82n_critS d / 2) * ‖z‖ ^ (-s82n_critS d) * B (‖z‖⁻¹ • z) (‖z‖⁻¹ • z) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have ht : 0 < ‖z‖ ^ 2 := by positivity
  obtain ⟨hsplit, hXs⟩ := s82n_rpow_split z hz (s82n_critS d)
  set tr : ℝ := ∑ i, B (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i)
    with htr
  set h0 : ℝ := tr / d with hh0
  have htr' : tr = d * h0 := by rw [hh0]; field_simp
  have hs2 : (0 : ℝ) < s82n_critS d + 2 := by unfold s82n_critS; positivity
  have hQ := s82n_omega_quad B z hz
  set X : ℝ := (‖z‖ ^ 2) ^ (-s82n_critS d / 2) with hX
  set Q : ℝ := B z z with hQdef
  set t : ℝ := ‖z‖ ^ 2 with htdef
  have hXpos : 0 < X := Real.rpow_pos_of_pos ht _
  rw [hQ, ← hXs]
  have hnear : ∀ᶠ w in 𝓝 z, w ≠ 0 := isOpen_ne.mem_nhds hz
  have hβ1 : -s82n_critS d / 2 - 1 = -s82n_critS d / 2 - 1 := rfl
  have hXd : t ^ (-s82n_critS d / 2 - 1) = X / t := Real.rpow_sub_one ht.ne' _
  by_cases hd4 : d = 4
  · -- logarithmic case
    subst hd4
    have hs : s82n_critS 4 = 2 := by unfold s82n_critS; norm_num
    have hc2 : (0 : ℝ) < 1 := one_pos
    have hrep : ∀ w : Euc 4, w ≠ 0 → s82n_leadingInverse nu B w =
        (h0 / (8 * nu)) * Real.log (‖w‖ ^ 2) -
          (1 / (4 * nu * (s82n_critS 4 + 2))) * (B w w * (‖w‖ ^ 2) ^ (-s82n_critS 4 / 2)) +
          (1 / (4 * nu * (s82n_critS 4 + 2))) * h0 := by
      intro w hw
      obtain ⟨hsp, hXs'⟩ := s82n_rpow_split w hw (s82n_critS 4)
      have hrw : 0 < ‖w‖ := norm_pos_iff.2 hw
      have hQw := s82n_omega_quad B w hw
      simp only [s82n_leadingInverse, ite_true, hQw, hs, hh0, htr, s82n_trace_eq B]
      rw [Real.log_pow]
      have h2s : (2 : ℝ) - 2 = 0 := by norm_num
      rw [h2s, Real.rpow_zero]
      have hX2 : (‖w‖ ^ 2) ^ (-(2 : ℝ) / 2) = (‖w‖ ^ 2)⁻¹ := by
        rw [show (-(2 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
      rw [hX2]
      push_cast
      field_simp
      ring
    let F : Euc 4 → ℝ := fun w => (h0 / (8 * nu)) * Real.log (‖w‖ ^ 2) -
          (1 / (4 * nu * (s82n_critS 4 + 2))) * (B w w * (‖w‖ ^ 2) ^ (-s82n_critS 4 / 2)) +
          (1 / (4 * nu * (s82n_critS 4 + 2))) * h0
    have hcongr : Laplacian.laplacian (s82n_leadingInverse nu B) z = Laplacian.laplacian F z :=
      (InnerProductSpace.laplacian_congr_nhds (hnear.mono fun w hw => hrep w hw)).self_of_nhds
    have hcd1 : ContDiffAt ℝ 2 (fun w : Euc 4 => Real.log (‖w‖ ^ 2)) z :=
      s82n_cd_radial z Real.log (Real.contDiffAt_log.2 ht.ne')
    rw [hcongr, s82n_lap_combo _ _ _ _ _ z hcd1 (s82n_cd_quad_rpow B z hz _),
      s82n_lap_log z hz, s82n_lap_quad_rpow B hB z hz, hXd, ← htr, hs]
    have hr2 : ‖z‖ ^ 2 = t := htdef.symm
    rw [hr2] at *
    have htr4 : tr = 4 * h0 := by rw [htr']; norm_num
    rw [htr4]
    norm_num
    rw [Real.rpow_neg_one, ← hQdef]
    field_simp
    ring
  · have hs2ne : 2 - s82n_critS d ≠ 0 := by
      intro h; apply hd4; unfold s82n_critS at h
      have : (d : ℝ) = 4 := by linarith
      exact_mod_cast this
    have hsp2ne : s82n_critS d + 2 ≠ 0 := hs2.ne'
    set α : ℝ := (2 - s82n_critS d) / 2 with hα
    have hαβ : α = -s82n_critS d / 2 + 1 := by rw [hα]; ring
    have hrep : ∀ w : Euc d, w ≠ 0 → s82n_leadingInverse nu B w =
        (h0 / (4 * nu * (2 - s82n_critS d)) + (1 / (4 * nu * (s82n_critS d + 2))) * h0) *
            (‖w‖ ^ 2) ^ α -
          (1 / (4 * nu * (s82n_critS d + 2))) * (B w w * (‖w‖ ^ 2) ^ (-s82n_critS d / 2)) + 0 := by
      intro w hw
      obtain ⟨hsp, _⟩ := s82n_rpow_split w hw (s82n_critS d)
      have hQw := s82n_omega_quad B w hw
      have hwt : ‖w‖ ^ 2 ≠ 0 := by have := norm_pos_iff.2 hw; positivity
      have hα' : (‖w‖ ^ 2) ^ α = ‖w‖ ^ 2 * (‖w‖ ^ 2) ^ (-s82n_critS d / 2) := by
        rw [hαβ, Real.rpow_add_one hwt]; ring
      simp only [s82n_leadingInverse, if_neg hd4, hQw, hsp, hα', hh0, htr, s82n_trace_eq B]
      field_simp
      ring
    let F : Euc d → ℝ := fun w =>
        (h0 / (4 * nu * (2 - s82n_critS d)) + (1 / (4 * nu * (s82n_critS d + 2))) * h0) *
            (‖w‖ ^ 2) ^ α -
          (1 / (4 * nu * (s82n_critS d + 2))) * (B w w * (‖w‖ ^ 2) ^ (-s82n_critS d / 2)) + 0
    have hcongr : Laplacian.laplacian (s82n_leadingInverse nu B) z = Laplacian.laplacian F z :=
      (InnerProductSpace.laplacian_congr_nhds (hnear.mono fun w hw => hrep w hw)).self_of_nhds
    have hcd1 : ContDiffAt ℝ 2 (fun w : Euc d => (‖w‖ ^ 2) ^ α) z :=
      s82n_cd_radial z (fun v => v ^ α) (Real.contDiffAt_rpow_const_of_ne ht.ne')
    rw [hcongr, s82n_lap_combo _ _ _ _ _ z hcd1 (s82n_cd_quad_rpow B z hz _),
      s82n_lap_rpow z hz, s82n_lap_quad_rpow B hB z hz, hXd, ← htr]
    have hα1 : α - 1 = -s82n_critS d / 2 := by rw [hαβ]; ring
    rw [hα1]
    have htr4 : tr = d * h0 := htr'
    rw [htr4, ← htdef, ← hX, ← hQdef, hαβ]
    clear_value X Q t
    have hdd : (d : ℝ) = 2 * s82n_critS d := by unfold s82n_critS; ring
    generalize s82n_critS d = s at hs2ne hsp2ne hdd ⊢
    rw [hdd]
    field_simp
    ring

end HRS.MS.S82N
