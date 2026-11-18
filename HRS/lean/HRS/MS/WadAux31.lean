import HRS.MS.WadAux30

/-!
# S8.3, packet D5^10 (Route A): the frozen classical adjoint solutions satisfy the a priori estimate

`s84_sol_of_classical`: an `IsClassicalAdjointW (critCoeff d a β ρβ) t φ f` (the classical solutions of
the frozen vocabulary, bounded `C²`, repaired growth of `∂_r f`) is an `S84Sol` for `ρ = ρβ`, `ν = β⁻¹`,
by `s83_mild_form` and the splitting `s84_generator_decomp`.  Consequently (`s84_apriori_classical`)
`|f_r(y)| ≤ K Φ ⟨y⟩^M` with `K` independent of the solution.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s84_cont_D0 {X : Type*} [TopologicalSpace X] {F : X → Euc d → ℝ} {x : X → Euc d}
    (h : Continuous fun p : X => iteratedFDeriv ℝ 0 (F p) (x p)) : Continuous fun p : X => F p (x p) := by
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (0 : Fin 0 → Euc d)).continuous.comp h
  refine this.congr fun p => ?_
  simp [Function.comp_def]

theorem s84_cont_D1 {X : Type*} [TopologicalSpace X] {F : X → Euc d → ℝ} {x : X → Euc d}
    (h : Continuous fun p : X => iteratedFDeriv ℝ 1 (F p) (x p)) :
    Continuous fun p : X => fderiv ℝ (F p) (x p) := by
  rw [continuous_clm_apply]
  intro v
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ (fun _ => v)).continuous.comp h
  refine this.congr fun p => ?_
  simp [Function.comp_def, iteratedFDeriv_one_apply]

theorem s84_cont_D2 {X : Type*} [TopologicalSpace X] {F : X → Euc d → ℝ} {x : X → Euc d}
    (h : Continuous fun p : X => iteratedFDeriv ℝ 2 (F p) (x p)) :
    Continuous fun p : X => fderiv ℝ (fderiv ℝ (F p)) (x p) := by
  rw [continuous_clm_apply]
  intro v
  rw [continuous_clm_apply]
  intro w
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ ![v, w]).continuous.comp h
  refine this.congr fun p => ?_
  simp [Function.comp_def, iteratedFDeriv_two_apply]

theorem s84_contOn_of_subtype {t : ℝ} {Y : Type*} [TopologicalSpace Y] {F : ℝ × Euc d → Y}
    (h : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => F (p.1.1, p.2)) :
    ContinuousOn F (Set.Icc 0 t ×ˢ Set.univ) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmap : Continuous fun q : (Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))) =>
      ((⟨q.1.1, q.2.1⟩ : Set.Icc (0 : ℝ) t), q.1.2) :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd)
  exact h.comp hmap

theorem s84_sol_of_classical (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρβ : Euc d → ℝ) {t M Φ : ℝ} (ht : 0 < t)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW (critCoeff d a β ρβ) t φ f)
    (hφ : Wt M Φ φ) : S84Sol ρβ a β⁻¹ t M Φ f := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have htI : t ∈ Set.Icc (0 : ℝ) t := ⟨ht.le, le_rfl⟩
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 (by norm_num)
  have hb0 : ∀ r ∈ Set.Icc 0 t, ∀ y, |f r y| ≤ B0 := fun r hr y => by
    have := hB0 r hr y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hb1 : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (f r) y‖ ≤ B1 := fun r hr y => by
    have := hB1 r hr y
    rwa [norm_iteratedFDeriv_one] at this
  have hb2 : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (fderiv ℝ (f r)) y‖ ≤ B2 := fun r hr y => by
    have := hB2 r hr y
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  have hbnn : 0 ≤ max B0 (max B1 B2) := by
    have := (abs_nonneg (f 0 0)).trans (hb0 0 h0I 0)
    exact le_max_of_le_left this
  have hB0' : ∀ r ∈ Set.Icc 0 t, ∀ y, |f r y| ≤ max B0 (max B1 B2) := fun r hr y =>
    (hb0 r hr y).trans (le_max_left _ _)
  have hB1' : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (f r) y‖ ≤ max B0 (max B1 B2) := fun r hr y =>
    (hb1 r hr y).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hB2' : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (fderiv ℝ (f r)) y‖ ≤ max B0 (max B1 B2) := fun r hr y =>
    (hb2 r hr y).trans ((le_max_right _ _).trans (le_max_right _ _))
  -- joint continuity
  have hwc : ContinuousOn (fun q : ℝ × Euc d => f q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D0 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 0 (by norm_num)))
  have hD1 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D1 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 1 (by norm_num)))
  have hD2 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (f q.1)) q.2)
      (Set.Icc 0 t ×ˢ Set.univ) :=
    s84_contOn_of_subtype (s84_cont_D2 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 2 (by norm_num)))
  have hGc : ContinuousOn (fun q : ℝ × Euc d => generatorW (critCoeff d a β ρβ) q.1 (f q.1) q.2)
      (Set.Icc 0 t ×ˢ Set.univ) := s84_contOn_of_subtype hf.cont_time_deriv
  obtain ⟨BG, hBG⟩ := hf.bdd_time_deriv
  have hmild := fun (r : ℝ) (hr : r ∈ Set.Icc 0 t) (x : Euc d) => s83_mild_form (a := a) (ν := β⁻¹) (t := t) (w := f)
    (G := fun r y => generatorW (critCoeff d a β ρβ) r (f r) y) ha hν hf.c2 hB0' hB1' hB2' hwc hD1 hD2 hGc
    hf.time_deriv hBG hr x
  have hq : ∀ s y, generatorW (critCoeff d a β ρβ) s (f s) y - s83_L0 a β⁻¹ (f s) y =
      s84_Bop ρβ (f s) y := fun s y => by
    rw [s84_generator_decomp]; ring
  refine ⟨hf.c2, ?_, ?_, ?_, ?_, ?_, ⟨max B1 B2, max B1 B2, fun r hr y => ⟨?_, ?_⟩⟩⟩
  · have := hGc.sub (s83_L0_contOn a β⁻¹ hD1 hD2)
    refine this.congr fun q _ => ?_
    simp only [Pi.sub_apply]
    rw [hq]
  · refine ⟨BG + (|β⁻¹| * d * max B0 (max B1 B2) + |a| * max B0 (max B1 B2)), 1, fun s hs y => ?_⟩
    rw [← hq]
    have h1 := hBG s hs y
    have h2 := s83_L0_bound (hB1' s hs) (hB2' s hs) a β⁻¹ y
    rw [pow_one]
    refine (abs_sub _ _).trans ?_
    nlinarith [abs_nonneg (generatorW (critCoeff d a β ρβ) s (f s) y)]
  · intro r hr x
    rw [hmild r hr x]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hfun : (fun y => generatorW (critCoeff d a β ρβ) s (f s) y - s83_L0 a β⁻¹ (f s) y) =
        fun y => s84_Bop ρβ (f s) y := funext (hq s)
    show s83_P a β⁻¹ (s - r) (fun y => generatorW (critCoeff d a β ρβ) s (f s) y -
        s83_L0 a β⁻¹ (f s) y) x = s83_P a β⁻¹ (s - r) (fun y => s84_Bop ρβ (f s) y) x
    rw [hfun]
  · exact (hf.c2 t htI).continuous
  · rw [hf.terminal]; exact hφ
  · exact (hb1 r hr y).trans (le_max_left _ _)
  · exact (hb2 r hr y).trans (le_max_right _ _)

/-- **The a priori estimate for the frozen classical adjoint solutions.** -/
theorem s84_apriori_classical (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ f → Wt M Φ φ →
      ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d, |f r y| ≤ K * Φ * jbracket y ^ M := by
  obtain ⟨K, hK0, hK⟩ := s84_apriori hd ha (inv_pos.2 hβ) hT hM (s84_thermal_gaussReg hd ha hβ hρ)
  exact ⟨K, hK0, fun ht htT hf hφ => hK ht htT (s84_sol_of_classical a β ha hβ ρβ ht hf hφ)⟩

end HRS.MS.Wad
