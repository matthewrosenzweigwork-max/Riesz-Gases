import HRS.MS.S111X2Aux28

/-!
# S11.1 X2, packet E07 (part 4): `φ + ∫_r^H h` is a classical adjoint solution with terminal datum `φ`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34
open HRS.MS.S111X1 (EnData KData Nnl)

variable {d : ℕ}

section Classical

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

theorem s111x2_cb2_bounds {φ : Euc d → ℝ} (hφ : MemCb 2 φ) :
    ∃ A0 A1 A2 : ℝ, 0 ≤ A0 ∧ (∀ x, ‖φ x‖ ≤ A0) ∧ CbD φ A1 A2 := by
  obtain ⟨A1, A2, hC⟩ := s111x2_cbD_of_memCb2 hφ
  obtain ⟨A0, h0⟩ := hφ.2 0 (by norm_num)
  refine ⟨max A0 0, A1, A2, le_max_right _ _, fun x => ?_, hC⟩
  have := h0 ⟨x, rfl⟩
  simp only [norm_iteratedFDeriv_zero] at this
  exact this.trans (le_max_left _ _)

theorem s111x2_ftil_classical (T : TD d s β ρ M C) {H : ℝ} (hH : 0 < H) {φ : Euc d → ℝ} (hφ : MemCb 2 φ)
    {h : ℝ → Euc d → ℝ} (hh : IsClassicalAdjointW C H (generatorW C 0 φ) h) :
    IsClassicalAdjointW C H φ (s111x2_Ftil φ (fun u => h (s111x2_clamp H u)) H) := by
  obtain ⟨A0, A1, A2, hA0, hA0', hφC⟩ := s111x2_cb2_bounds hφ
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hfam, hB0'⟩ := s111x2_clamp_fam hH.le hh
  set hb : ℝ → Euc d → ℝ := fun u => h (s111x2_clamp H u) with hbdef
  have hC : ∀ r ∈ Icc (0 : ℝ) H, CbD (s111x2_Ftil φ hb H r) (A1 + (H - r) * B1) (A2 + (H - r) * B2) :=
    fun r hr => s111x2_cbD_add_param hfam hφC hr.2
  have hgen : ∀ r ∈ Icc (0 : ℝ) H, ∀ x, generatorW C r (s111x2_Ftil φ hb H r) x = h r x := fun r hr x => by
    rw [s111x2_gen_auto T (hC r hr) r]
    exact s111x2_ftil_gen T hφC hh hfam hr x
  have hc0 : Continuous fun p : ℝ × Euc d => hb p.1 p.2 := hfam.c0
  have hqc : Continuous fun p : Icc (0 : ℝ) H × Euc d => (p.1.1, p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  refine
  { c2 := fun r hr => (hC r hr).smooth
    bdd := ?_
    cont_c2 := ?_
    terminal := ?_
    time_deriv := ?_
    cont_time_deriv := ?_
    bdd_time_deriv := ⟨B0, fun r hr x => ?_⟩ }
  · intro j hj
    interval_cases j
    · refine ⟨A0 + H * B0, fun r hr x => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      unfold s111x2_Ftil
      have h1 : ‖∫ u in r..H, hb u x‖ ≤ B0 * (H - r) := by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := H) (C := B0)
          (f := fun u => hb u x) (fun u _ => by rw [Real.norm_eq_abs]; exact hB0' u x)
        rwa [abs_of_nonneg (sub_nonneg.2 hr.2)] at this
      refine (norm_add_le _ _).trans ?_
      have := hA0' x
      nlinarith [hr.1]
    · refine ⟨A1 + H * B1, fun r hr x => ?_⟩
      rw [norm_iteratedFDeriv_one]
      have := (hC r hr).d1 x
      nlinarith [hr.1]
    · refine ⟨A2 + H * B2, fun r hr x => ?_⟩
      have e1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := s111x2_Ftil φ hb H r) (x := x) (n := 1)
      rw [norm_iteratedFDeriv_one] at e1
      have h2 := (hC r hr).d2 x
      have e2 : ‖iteratedFDeriv ℝ 2 (s111x2_Ftil φ hb H r) x‖ = ‖fderiv ℝ (fderiv ℝ (s111x2_Ftil φ hb H r)) x‖ := by
        rw [← e1]
      rw [e2]
      nlinarith [hr.1]
  · refine HRS.movb_iter_cont_of (ι := Icc (0 : ℝ) H) (F := fun r => s111x2_Ftil φ hb H r.1) ?_ ?_ ?_
    · unfold s111x2_Ftil
      exact (hφC.smooth.continuous.comp continuous_snd).add
        ((s111x2_cont_param_left hb hc0 H).comp hqc)
    · have e : (fun p : Icc (0 : ℝ) H × Euc d => fderiv ℝ (s111x2_Ftil φ hb H p.1.1) p.2) =
          fun p => fderiv ℝ φ p.2 + ∫ u in p.1.1..H, fderiv ℝ (hb u) p.2 :=
        funext fun p => s111x2_ftil_fderiv hfam hφC H p.1.1 p.2
      rw [e]
      exact ((hφC.smooth.continuous_fderiv (by norm_num)).comp continuous_snd).add
        ((s111x2_cont_param_left (fun u => fderiv ℝ (hb u)) hfam.c1 H).comp hqc)
    · have e : (fun p : Icc (0 : ℝ) H × Euc d => fderiv ℝ (fderiv ℝ (s111x2_Ftil φ hb H p.1.1)) p.2) =
          fun p => fderiv ℝ (fderiv ℝ φ) p.2 + ∫ u in p.1.1..H, fderiv ℝ (fderiv ℝ (hb u)) p.2 :=
        funext fun p => s111x2_ftil_fderiv₂ hfam hφC H p.1.1 p.2
      rw [e]
      have hφ2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
        (hφC.smooth.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
      exact (hφ2.comp continuous_snd).add
        ((s111x2_cont_param_left (fun u => fderiv ℝ (fderiv ℝ (hb u))) hfam.c2 H).comp hqc)
  · funext y
    simp [s111x2_Ftil]
  · intro x r hr
    have hrI : r ∈ Icc (0 : ℝ) H := ⟨hr.1.le, hr.2.le⟩
    have hcont : Continuous fun u => hb u x := hc0.comp (continuous_id.prodMk continuous_const)
    have hd := (intervalIntegral.integral_hasDerivAt_left (f := fun u => hb u x) (a := r) (b := H)
      (hcont.intervalIntegrable _ _) hcont.stronglyMeasurable.stronglyMeasurableAtFilter
      hcont.continuousAt).const_add (φ x)
    have e : hb r x = generatorW C r (s111x2_Ftil φ hb H r) x := by
      rw [hgen r hrI x, hbdef]; simp only; rw [s111x2_clamp_id hrI]
    rw [← e]
    exact hd
  · have := (hfam.c0.comp hqc)
    refine this.congr fun p => ?_
    simp only [Function.comp_apply]
    rw [hgen p.1.1 p.1.2 p.2, hbdef]; simp only; rw [s111x2_clamp_id p.1.2]
  · rw [hgen r hr x]
    have h1 := hB0' r x
    simp only [hbdef, s111x2_clamp_id hr] at h1
    have : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith

end Classical

end HRS.MS.S111X2
