import HRS.MC.CepH2Loc1

/-!
# CEPH2, G3 (b): the strong solutions for the frozen potentials converge pathwise (eventually equal)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N] {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem h2_gradient_eq_of_eq_near {f g : Ch N → ℝ} {x : Ch N} (h : f =ᶠ[𝓝 x] g) : gradient f x = gradient g x := by
  simp only [gradient]
  rw [h.fderiv_eq]

theorem cepH2_loc_tendsto [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} {π : Ω → Equiv.Perm (Fin N)}
    {U : Ch N → ℝ} (hU : ContDiff ℝ 2 U) {Un : ℕ → Ch N → ℝ} {K : ℕ → ℝ≥0}
    (hLip : ∀ n, LipschitzWith (K n) (gradient (Un n)))
    (hUnU : ∀ (n : ℕ) (z : Ch N), ‖h2_perp z‖ < (n : ℝ) → Un n z = U z) {θ : ℝ}
    {z₀ : Ω → Ch N} {Z : ℝ → Ω → Ch N} {Zn : ℕ → ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * θ)) (fun z => -(gradient U z)) z₀ Z)
    (hZn : ∀ n, cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * θ)) (fun z => -(gradient (Un n) z)) z₀ (Zn n))
    {t : ℝ} (ht : 0 ≤ t) {g : Ch N → ℝ} (hg : Measurable g) (hb : ∃ C : ℝ, ∀ z, |g z| ≤ C) :
    Tendsto (fun n => ∫ ω, g (cep_reduce (Zn n t ω)) ∂P) atTop (𝓝 (∫ ω, g (cep_reduce (Z t ω)) ∂P)) := by
  obtain ⟨C, hC⟩ := hb
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hBc : Continuous (fun z : Ch N => -(gradient U z)) := (h2_continuous_gradient hU1).neg
  have hZmeas : ∀ n, Measurable (Zn n t) := fun n => (hZn n).2.1 t ht |>.mono (ℱ.le t) le_rfl
  have hgm : ∀ n, Measurable fun ω => g (cep_reduce (Zn n t ω)) := fun n =>
    hg.comp (h2_measurable_reduce.comp (hZmeas n))
  refine tendsto_integral_of_dominated_convergence (fun _ => |C|) (fun n => (hgm n).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun ω => ?_) ?_
  · rw [Real.norm_eq_abs]; exact (hC _).trans (le_abs_self C)
  · have hae : ∀ᵐ ω ∂P, (∀ s : ℝ, 0 ≤ s → Z s ω = z₀ ω + (∫ r in (0 : ℝ)..s, -(gradient U (Z r ω))) +
        Real.sqrt (2 * θ) • cep_noise π W' s ω) ∧
        ∀ n, ∀ s : ℝ, 0 ≤ s → Zn n s ω = z₀ ω + (∫ r in (0 : ℝ)..s, -(gradient (Un n) (Zn n r ω))) +
          Real.sqrt (2 * θ) • cep_noise π W' s ω := by
      filter_upwards [hZ.2.2, ae_all_iff.2 fun n => (hZn n).2.2] with ω h1 h2
      exact ⟨h1, h2⟩
    filter_upwards [hae] with ω ⟨h1, h2⟩
    have hZc : Continuous fun s => Z s ω := hZ.1 ω
    obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
      ((h2_continuous_perp.comp hZc).norm.continuousOn)
    obtain ⟨n0, hn0⟩ := exists_nat_gt R
    have hev : ∀ᶠ n in atTop, Zn n t ω = Z t ω := by
      filter_upwards [eventually_ge_atTop n0] with n hn
      have hnR : R < (n : ℝ) := lt_of_lt_of_le hn0 (by exact_mod_cast hn)
      have hgrad : ∀ r ∈ Icc (0 : ℝ) t, -(gradient U (Z r ω)) = -(gradient (Un n) (Z r ω)) := by
        intro r hr
        have hlt : ‖h2_perp (Z r ω)‖ < (n : ℝ) := by
          have := hR r hr
          simp only [Function.comp, norm_norm] at this
          linarith
        have hopen : IsOpen {z : Ch N | ‖h2_perp z‖ < (n : ℝ)} :=
          isOpen_lt (h2_continuous_perp.norm) continuous_const
        have hev' : Un n =ᶠ[𝓝 (Z r ω)] U :=
          Filter.mem_of_superset (hopen.mem_nhds hlt) fun z hz => hUnU n z hz
        rw [h2_gradient_eq_of_eq_near hev'.symm]
      have := h2_path_eq (B := fun z => -(gradient U z)) (B' := fun z => -(gradient (Un n) z)) hBc
        (L := K n) ((hLip n).neg) (z₀ := z₀ ω) (w := fun s => Real.sqrt (2 * θ) • cep_noise π W' s ω)
        hZc ((hZn n).1 ω) (fun s hs => h1 s hs) (fun s hs => h2 n s hs) ht hgrad t ⟨ht, le_rfl⟩
      exact this
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hn]

end HRS.MC.CepH2
