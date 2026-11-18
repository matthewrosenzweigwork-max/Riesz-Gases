import HRS.MS.R26T8AP07s

/-!
# S8.2 local Newton layer, packet T8A.P07: raw Newton conormal gain (pure conormal hypothesis, any `sigma < d`; and the case `0 <= sigma`)
`r26t8a_raw_newton_boundP`: `ConormalP` hypothesis, every real `sigma < d`. `r26t8a_raw_newton_bound_nonneg`: the T8A.P07 contract with the extra hypothesis `0 <= sigma`
(NOT the verbatim contract for `sigma < 0`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

theorem r26t8a_raw_newton_boundP (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (nu M sigma : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ConormalP k b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
        midPair F ((1 / 2 : ℝ) • (x + y)) z)) ∧
      Conormal k (b + 1) M (sigma - 2) (C * A) (rawNewton nu chi F) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_raw_jet hd k b nu M sigma hnu hM hsd hchi
  refine ⟨C, hC0, fun F A hA hF => ⟨fun x y hxy => ?_, ?_, ?_⟩⟩
  · exact (r26t8a_p07_series_repr hd k b nu M sigma hnu hM hsd hchi hA hF ((1 / 2 : ℝ) • (x + y)) (x - y)
      (sub_ne_zero.2 hxy)).1
  · -- smoothness off the diagonal
    set Φ : Euc d × Euc d → ℝ := fun Yw => chi Yw.2 *
      ∑' n : ℕ, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2 with hΦ
    have hN := r26t8a_p07_N_contDiffOn hd k b nu M sigma hnu hM hsd hchi hA hF
    have hchic : ContDiff ℝ (k : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
    have hΦc : ContDiffOn ℝ (k : WithTop ℕ∞) Φ {Yw : Euc d × Euc d | Yw.2 ≠ 0} := by
      refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
      by_cases h3 : ‖x.2‖ < 3
      · refine ⟨{Yw : Euc d × Euc d | ‖Yw.2‖ < 3}, isOpen_lt (continuous_norm.comp continuous_snd) continuous_const,
          h3, ?_⟩
        refine ((hchic.comp contDiff_snd).contDiffOn.mul (hN.mono ?_))
        intro Yw hYw
        exact ⟨norm_pos_iff.2 hYw.1, hYw.2⟩
      · push Not at h3
        refine ⟨{Yw : Euc d × Euc d | 2 < ‖Yw.2‖}, isOpen_lt continuous_const (continuous_norm.comp continuous_snd),
          by simp only [Set.mem_setOf_eq]; linarith, ?_⟩
        refine (contDiffOn_const (c := (0 : ℝ))).congr fun Yw hYw => ?_
        simp only [hΦ, hchi.2.2.2.2 Yw.2 (le_of_lt hYw.2), zero_mul]
    have hL : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ((1 / 2 : ℝ) • (p.1 + p.2), p.1 - p.2)) :=
      (((contDiff_fst.add contDiff_snd).const_smul _)).prodMk (contDiff_fst.sub contDiff_snd)
    refine (hΦc.comp hL.contDiffOn (fun p hp => ?_)).congr (fun p hp => ?_)
    · exact sub_ne_zero.2 hp
    · have hw : p.1 - p.2 ≠ 0 := sub_ne_zero.2 hp
      have h := r26t8a_p07_raw_mid hd k b nu M sigma hnu hM hsd hchi hA hF ((1 / 2 : ℝ) • (p.1 + p.2))
        (p.1 - p.2) hw
      have e1 : (1 / 2 : ℝ) • (p.1 + p.2) + (1 / 2 : ℝ) • (p.1 - p.2) = p.1 := by module
      have e2 : (1 / 2 : ℝ) • (p.1 + p.2) - (1 / 2 : ℝ) • (p.1 - p.2) = p.2 := by module
      simp only [midPair, e1, e2] at h
      simpa [Function.uncurry, hΦ] using h
  · intro p q hpq X z hz
    exact hC A hA F hF p q hpq X z hz

theorem r26t8a_p07_conormal_toP {d : ℕ} {k b : ℕ} {M sigma A : ℝ} {F : Euc d → Euc d → ℝ} (hA : 0 ≤ A)
    (hs : 0 ≤ sigma) (h : Conormal k b M sigma A F) : ConormalP k b M sigma (2 * A) F := by
  refine And.intro h.1 fun p q hpq X z hz => (h.2 p q hpq X z hz).trans ?_
  have hpw0 : 0 ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
    mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _))
  have hr : 0 < min 1 ‖z‖ := lt_min zero_lt_one (norm_pos_iff.2 hz)
  have h1 : (1 : ℝ) ≤ (min 1 ‖z‖) ^ (-(sigma + (q : ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr (min_le_left _ _) (by
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      linarith)
  have h2 : (1 : ℝ) ≤ (1 + |Real.log (min 1 ‖z‖)|) ^ b :=
    one_le_pow₀ (by linarith [abs_nonneg (Real.log (min 1 ‖z‖))])
  have h3 : 1 ≤ (min 1 ‖z‖) ^ (-(sigma + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b := by nlinarith
  calc A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (1 + (min 1 ‖z‖) ^ (-(sigma + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b)
      ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (2 * ((min 1 ‖z‖) ^ (-(sigma + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpw0
    _ = 2 * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        ((min 1 ‖z‖) ^ (-(sigma + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b) := by ring

theorem r26t8a_raw_newton_bound_nonneg (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (nu M sigma : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal k b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
        midPair F ((1 / 2 : ℝ) • (x + y)) z)) ∧
      Conormal k (b + 1) M (sigma - 2) (C * A) (rawNewton nu chi F) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_raw_newton_boundP d hd k b nu M sigma hnu hM hsd chi hchi
  refine ⟨2 * C, by positivity, fun F A hA hF => ?_⟩
  obtain ⟨h1, h2⟩ := hC F (2 * A) (by positivity) (r26t8a_p07_conormal_toP hA hsigma hF)
  refine ⟨h1, ?_⟩
  rwa [show C * (2 * A) = 2 * C * A by ring] at h2

end HRS.MS.R26T8A
