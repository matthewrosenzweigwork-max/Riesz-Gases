import HRS.MS.S111K4ATD
import HRS.MS.S111K4J01D
import HRS.MS.S111K2B04h

/-!
# S11.1 / all-tests boundary (S111K4AT), piece E: `boundary_drift_coordinates_all_tests`

Pro `r26t6_boundary_drift_coordinates_all_tests`, proved from the orbit approximation `K4OscOrbitApprox`: the dual-combination
formula for `D` extends to every oscillator test function (Hermite sections, the envelope `k4at_envelope`, and
`k4at_int_limit`).  The envelope `N` of `dualNormE (z ·)` is taken measurable (for the coefficient fields it is `‖q ·‖`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole HRS.MS.S111K2 HRS.MS.S111K4J01

variable {d : ℕ}

theorem k4_all_tests_drift {r : ℕ} {Pw T u : ℝ} (hu : 0 ≤ u) (hP : (d : ℝ) < 2 * Pw) {C : WholeCoeff d}
    (horb : K4OscOrbitApprox C (wholeSpaceIndex d : ℝ) (u + T) r) {z : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r Pw (u + T) z) {N : ℝ → ℝ≥0∞} (hNm : Measurable N)
    (hN : ∫⁻ s in Set.Icc (0 : ℝ) (u + T), N s < ⊤)
    (hzN : ∀ s ∈ Set.Icc (0 : ℝ) (u + T), dualNormE r Pw (z s) ≤ N s)
    (hdm : S111k2DriftIntegrandMeas C (wholeSpaceIndex d : ℝ) T u z)
    {v : ℝ} (D : OscPath d (wholeSpaceIndex d : ℝ) T)
    (hD : ∀ tau : Set.Icc (0 : ℝ) T, ∀ phi : Euc d → ℝ, IsR2DualCombo (wholeSpaceIndex d : ℝ) phi →
      OscDual.eval (OscPath.at' D tau) phi =
        ∫ s in Set.Ioc 0 v ∩ Set.Icc 0 (u + tau), z s (propagatorW C s (u + tau) phi)) :
    AllDriftCoordinates C (wholeSpaceIndex d : ℝ) T u z v D := by
  intro tau phi hphi
  have htau0 := tau.2.1
  have htauT := tau.2.2
  have hDt := hD tau
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = u + (tau : ℝ) := ⟨_, rfl⟩
  have htH : t ∈ Set.Icc (0 : ℝ) (u + T) := ⟨by rw [htdef]; linarith, by rw [htdef]; linarith⟩
  have ht : t ∈ Set.Icc u (u + T) := ⟨by rw [htdef]; linarith, by rw [htdef]; linarith⟩
  rw [← htdef] at hDt ⊢
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = min v t := ⟨_, rfl⟩
  rw [← hadef]
  have hsub : Set.Icc (0 : ℝ) a ⊆ Set.Icc (0 : ℝ) t := by
    rw [hadef]; exact Set.Icc_subset_Icc_right (min_le_right _ _)
  have hsub' : Set.Icc (0 : ℝ) a ⊆ Set.Icc (0 : ℝ) (u + T) := hsub.trans (Set.Icc_subset_Icc_right htH.2)
  obtain ⟨c, hc, e, he, hFb, hdiff⟩ := k4at_envelope hP horb hz hzN hphi htH
  have hNμ : ∫⁻ s in Set.Icc (0 : ℝ) a, N s < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hsub') hN
  have hFn : ∀ n : ℕ, AEStronglyMeasurable
      (fun s => z s (propagatorW C s t (k4hs (wholeSpaceIndex d : ℝ) n phi)))
      (volume.restrict (Set.Icc (0 : ℝ) a)) := fun n =>
    ((hdm t ht _ (k4hs_combo _ n phi)).mono_measure (Measure.restrict_mono hsub le_rfl)).aestronglyMeasurable
  have hdiff' : ∀ᶠ n : ℕ in atTop, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) a)),
      ‖z s (propagatorW C s t (k4hs (wholeSpaceIndex d : ℝ) n phi)) - z s (propagatorW C s t phi)‖ₑ ≤
        N s * e n := by
    filter_upwards [hdiff] with n hn
    exact ae_restrict_of_forall_mem measurableSet_Icc fun s hs => hn s (hsub hs)
  have hFb' : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) a)), ‖z s (propagatorW C s t phi)‖ₑ ≤ N s * c :=
    ae_restrict_of_forall_mem measurableSet_Icc fun s hs => hFb s (hsub hs)
  obtain ⟨hFi, hlim⟩ := k4at_int_limit hNm hNμ hc he hFn hdiff' hFb'
  have hset : Set.Ioc 0 v ∩ Set.Icc 0 t = Set.Ioc 0 a := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, hadef, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h4⟩; exact ⟨⟨h1, h2⟩, h1.le, h4⟩
  have hDn : ∀ n : ℕ, OscDual.eval (OscPath.at' D tau) (k4hs (wholeSpaceIndex d : ℝ) n phi) =
      ∫ s in Set.Icc (0 : ℝ) a, z s (propagatorW C s t (k4hs (wholeSpaceIndex d : ℝ) n phi)) := by
    intro n
    rw [hDt _ (k4hs_combo _ n phi), hset]
    exact setIntegral_congr_set Ioc_ae_eq_Icc
  refine ⟨hFi, ?_⟩
  exact tendsto_nhds_unique (k4hs_tendsto _ (OscPath.at' D tau) hphi.2)
    (hlim.congr fun n => (hDn n).symm)

end HRS.MS.S111K4AT
