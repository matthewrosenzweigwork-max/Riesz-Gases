import HRS.MS.S111K4ATI
import HRS.MS.S111K4ATJ
import HRS.MS.S111K4J01D

/-!
# S11.1 / all-tests boundary (S111K4AT), piece K: `boundary_covariance_coordinates_all_tests`

Pro `r26t6_boundary_covariance_coordinates_all_tests`, from the orbit approximation `K4OscOrbitApprox`: the dual-combination
formula `ShiftedJValue` extends to all oscillator tests (`AllShiftedJValue`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole HRS.MS.S111K4J01

variable {d : ℕ}

theorem k4_all_tests_cov {r : ℕ} {Pw T u : ℝ} (hu : 0 ≤ u) (hP : (d : ℝ) < 2 * Pw) {C : WholeCoeff d}
    (horb : K4OscOrbitApprox C (wholeSpaceIndex d : ℝ) (u + T) r) {z : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r Pw (u + T) z) {N : ℝ → ℝ≥0∞} (hNm : Measurable N)
    (hN : ∫⁻ s in Set.Icc (0 : ℝ) (u + T), N s < ⊤)
    (hzN : ∀ s ∈ Set.Icc (0 : ℝ) (u + T), dualNormE r Pw (z s) ≤ N s)
    (hJm : R2JIntegrandMeas C (wholeSpaceIndex d : ℝ) (u + T) z)
    {v : ℝ} (J : projTensor (OscPath d (wholeSpaceIndex d : ℝ) T) 2)
    (hJ : ShiftedJValue C (wholeSpaceIndex d : ℝ) T u z 0 v J) :
    AllShiftedJValue C (wholeSpaceIndex d : ℝ) T u z v J := by
  intro ta tb φ ψ hφ hψ
  have hta0 := ta.2.1
  have htaT := ta.2.2
  have htb0 := tb.2.1
  have htbT := tb.2.2
  have hJ' := hJ ta tb
  obtain ⟨Ta, hTadef⟩ : ∃ t : ℝ, t = u + (ta : ℝ) := ⟨_, rfl⟩
  obtain ⟨Tb, hTbdef⟩ : ∃ t : ℝ, t = u + (tb : ℝ) := ⟨_, rfl⟩
  have hTaH : Ta ∈ Set.Icc (0 : ℝ) (u + T) := ⟨by rw [hTadef]; linarith, by rw [hTadef]; linarith⟩
  have hTbH : Tb ∈ Set.Icc (0 : ℝ) (u + T) := ⟨by rw [hTbdef]; linarith, by rw [hTbdef]; linarith⟩
  rw [← hTadef, ← hTbdef] at hJ' ⊢
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = min v (min Ta Tb) := ⟨_, rfl⟩
  rw [← hadef]
  have hsub : Set.Icc (0 : ℝ) a ⊆ Set.Icc (0 : ℝ) (min Ta Tb) := by
    rw [hadef]; exact Set.Icc_subset_Icc_right (min_le_right _ _)
  have hsub' : Set.Icc (0 : ℝ) a ⊆ Set.Icc (0 : ℝ) (u + T) :=
    hsub.trans (Set.Icc_subset_Icc_right ((min_le_left _ _).trans hTaH.2))
  have e : ∀ f h : Euc d → ℝ, (fun x => inner ℝ (gradient f x) (gradient h x)) = k4Gf f h :=
    fun f h => funext (k4_inner_grad_eq f h)
  simp only [e] at hJ' ⊢
  obtain ⟨c, hc, en, hen, hFb, hdiff⟩ := k4at_cov_envelope hP horb hz hzN hφ hψ hTaH hTbH
  have hNμ : ∫⁻ s in Set.Icc (0 : ℝ) a, N s < ⊤ := lt_of_le_of_lt (lintegral_mono_set hsub') hN
  have hFn : ∀ n : ℕ, AEStronglyMeasurable
      (fun s => z s (k4Gf (propagatorW C s Ta (k4hs (wholeSpaceIndex d : ℝ) n φ))
        (propagatorW C s Tb (k4hs (wholeSpaceIndex d : ℝ) n ψ)))) (volume.restrict (Set.Icc (0 : ℝ) a)) := by
    intro n
    have := hJm Ta Tb _ _ (k4hs_combo _ n φ) (k4hs_combo _ n ψ) hTaH hTbH
    simp only [e] at this
    exact (this.mono_measure (Measure.restrict_mono hsub le_rfl)).aestronglyMeasurable
  have hdiff' : ∀ᶠ n : ℕ in atTop, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) a)),
      ‖z s (k4Gf (propagatorW C s Ta (k4hs (wholeSpaceIndex d : ℝ) n φ))
          (propagatorW C s Tb (k4hs (wholeSpaceIndex d : ℝ) n ψ))) -
        z s (k4Gf (propagatorW C s Ta φ) (propagatorW C s Tb ψ))‖ₑ ≤ N s * en n := by
    filter_upwards [hdiff] with n hn
    exact ae_restrict_of_forall_mem measurableSet_Icc fun s hs => hn s (hsub hs)
  have hFb' : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) a)),
      ‖z s (k4Gf (propagatorW C s Ta φ) (propagatorW C s Tb ψ))‖ₑ ≤ N s * c :=
    ae_restrict_of_forall_mem measurableSet_Icc fun s hs => hFb s (hsub hs)
  obtain ⟨hFi, hlim⟩ := k4at_int_limit hNm hNμ hc hen hFn hdiff' hFb'
  refine ⟨hFi, ?_⟩
  intro l1 l2 hl1 hl2
  -- the sections of the test functions
  have hl1n : ∀ n : ℕ, ∀ w, k4ell (m := (wholeSpaceIndex d : ℝ)) ta n φ w =
      OscDual.eval (OscPath.at' w ta) (k4hs (wholeSpaceIndex d : ℝ) n φ) := fun n w => k4ell_apply ta n φ w
  have hl2n : ∀ n : ℕ, ∀ w, k4ell (m := (wholeSpaceIndex d : ℝ)) tb n ψ w =
      OscDual.eval (OscPath.at' w tb) (k4hs (wholeSpaceIndex d : ℝ) n ψ) := fun n w => k4ell_apply tb n ψ w
  have hset : Set.Ioc 0 v ∩ Set.Icc 0 (min Ta Tb) = Set.Ioc 0 a := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, hadef, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h4, h5⟩; exact ⟨h1, h2, h4, h5⟩
    · rintro ⟨h1, h2, h4, h5⟩; exact ⟨⟨h1, h2⟩, h1.le, h4, h5⟩
  have hJn : ∀ n : ℕ, (J : TensorDual (OscPath d (wholeSpaceIndex d : ℝ) T) 2)
      (k4M (k4ell ta n φ) (k4ell tb n ψ)) = 2 * C.ν *
      ∫ s in Set.Icc (0 : ℝ) a, z s (k4Gf (propagatorW C s Ta (k4hs (wholeSpaceIndex d : ℝ) n φ))
        (propagatorW C s Tb (k4hs (wholeSpaceIndex d : ℝ) n ψ))) := by
    intro n
    have := hJ' _ _ (k4ell ta n φ) (k4ell tb n ψ) (k4hs_combo _ n φ) (k4hs_combo _ n ψ) (hl1n n) (hl2n n)
    rw [hset] at this
    refine this.trans ?_
    congr 1
    exact setIntegral_congr_set Ioc_ae_eq_Icc
  have hn1 := k4at_eta_tendsto (wholeSpaceIndex d : ℝ) hφ.2
  have hn2 := k4at_eta_tendsto (wholeSpaceIndex d : ℝ) hψ.2
  have h1 : Tendsto (fun n => ‖k4ell ta n φ - l1‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => k4ell_dist ta n hφ.2 hl1) hn1
  have h2 : Tendsto (fun n => ‖k4ell tb n ψ - l2‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => k4ell_dist tb n hψ.2 hl2) hn2
  have hJt := k4J_tendsto J h1 h2
  have hlim2 : Tendsto (fun n : ℕ => 2 * C.ν *
      ∫ s in Set.Icc (0 : ℝ) a, z s (k4Gf (propagatorW C s Ta (k4hs (wholeSpaceIndex d : ℝ) n φ))
        (propagatorW C s Tb (k4hs (wholeSpaceIndex d : ℝ) n ψ)))) atTop
      (𝓝 (2 * C.ν * ∫ s in Set.Icc (0 : ℝ) a, z s (k4Gf (propagatorW C s Ta φ) (propagatorW C s Tb ψ)))) :=
    hlim.const_mul _
  exact tendsto_nhds_unique (hJt.congr hJn) hlim2

end HRS.MS.S111K4AT
