import HRS.Sections.AdjKGlueAux9

/-!
# ADJK-GLUE, part 10: tightness of the fluctuation paths in `C([0,T];E_m)` (`m > d + 4`, `T > 0`)

The tail combination for `Ξ_n = Φ_n - Lin(η⁰_n) = Z_n + Rem_n` from the per-system bundle `adjkg_sys` (BCONV, B2, B3, KOLM),
the finite-`n` modulus, and `adjkg_tight_of_components`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

theorem adjkg_rem_energy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m m₂ T : ℝ}
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (H0 : Ω → NegSobolev d m)
    (Ht Z : ℝ → Ω → NegSobolev d m) (F : NonzeroLattice d → ℝ → Ω → ℝ)
    (h : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
      NegSobolev.fourierCoeff (Ht t ω) k = NegSobolev.fourierCoeff (Vev t 0 (H0 ω)) k +
        NegSobolev.fourierCoeff (Z t ω) k + F k t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, adjkEnergy m₂ m (Ht t ω - Vev t 0 (H0 ω) - Z t ω) =
      ∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m₂) * F k t ω ^ 2) := by
  filter_upwards [h] with ω hω t ht
  rw [adjkg_energy_eq_fourier]
  refine tsum_congr fun k => ?_
  congr 2
  rw [adjkg_fourier_sub, adjkg_fourier_sub, hω t ht k]
  ring

theorem adjkg_exists_pos_le (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (N : ℕ) :
    ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ n < N, δ₂ ≤ δ n := by
  induction N with
  | zero => exact ⟨1, one_pos, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨δ₂, hδ₂, h2⟩ := ih
    refine ⟨min δ₂ (δ k), lt_min hδ₂ (hδ k), fun n hn => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | h
    · exact (min_le_left _ _).trans (h2 n h)
    · subst h; exact min_le_right _ _

theorem adjkg_tight (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T : ℝ} (hT : 0 < T) (S : ParticleSeq d)
    (hS : S.IsSolutionOn htr.dyn T)
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hfin : ∀ n, relEntropy ((S.P n).map (S.X₀ n))
      (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤)
    (hB : Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
          Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0))
    {m : ℝ} (hm : (d : ℝ) + 4 < m)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {η₀' : Ω' → NegSobolev d m}
    (hlaw : MeasureTheory.TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω) (withDensityReal (ρ 0))) atTop η₀' S.P P') :
    IsTightMeasureSet (Set.range fun n => (S.P n).map
      (fun ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmd2 : (d : ℝ) / 2 < m := by linarith
  -- levels
  obtain ⟨f, hf1, hf2⟩ : ∃ f : ℕ, (d : ℝ) + 4 ≤ f ∧ (f : ℝ) ≤ m := by
    refine ⟨⌊m⌋₊, ?_, Nat.floor_le (by linarith)⟩
    have : d + 4 ≤ ⌊m⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have h2f : 2 ≤ f := by
    have : (2 : ℝ) ≤ f := by linarith
    exact_mod_cast this
  have hjc : (((f - 2 : ℕ)) : ℝ) = (f : ℝ) - 2 := by
    rw [Nat.cast_sub h2f]; norm_num
  set j : ℕ := f - 2 with hjdef
  have hj : (d : ℝ) + 2 ≤ j := by rw [hjc]; linarith
  have hjm : (j : ℝ) + 2 ≤ m := by rw [hjc]; linarith
  set m₂ : ℝ := ((j : ℝ) + m) / 2 with hm₂def
  have hm₂ : (d : ℝ) + 2 < m₂ := by rw [hm₂def]; linarith
  have hm₂m : m₂ < m := by rw [hm₂def]; linarith
  have hjm₂ : (j : ℝ) ≤ m₂ := by rw [hm₂def]; linarith
  -- the per-system bundle
  obtain ⟨Vev, hdual, hplain, CL, hCL0, hCL, Cz, Cr, hCz0, hCr0, hsys⟩ :=
    adjkg_sys hd htr hm hT hj hjm hm₂
  have hc : ∀ z, Continuous fun t : Set.Icc (0 : ℝ) T => Vev t 0 z := fun z =>
    adjk_orbit_continuous (hplain T hT.le) z
  have hLin : Continuous (adjkLin m T Vev hc) :=
    adjkLin_continuous hc hCL0 (fun t ht => hCL 0 t le_rfl ht.1)
  have hsysn : ∀ n : ℕ, ∃ Z : ℝ → S.Ω n → NegSobolev d m, (∀ t, Measurable (Z t)) ∧
      (∀ ω, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) ∧
      ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, adjkEnergy (j : ℝ) m (Z t ω) ∂(S.P n) ≤ ENNReal.ofReal Cz ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ‖Z t ω - Z s ω‖ₑ ^ (4 : ℝ) ∂(S.P n) ≤ ENNReal.ofReal (Cz * |t - s| ^ 2)) ∧
      ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (∑' k : NonzeroLattice d,
          ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m₂) *
            evolvingForcingCoord htr.dyn ρ (S.X n) k t ω ^ 2)) ^ (1 / 2 : ℝ) ∂(S.P n) ≤
        ENNReal.ofReal (Cr * entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
          (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
            Real.sqrt ((n + 2 : ℕ) : ℝ)) ∧
      ∀ᵐ ω ∂(S.P n), ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
        NegSobolev.fourierCoeff (etaE m (S.X n t.toNNReal ω) (withDensityReal (ρ t))) k =
          NegSobolev.fourierCoeff (Vev t 0 (etaE m (S.X n 0 ω) (withDensityReal (ρ 0)))) k +
            NegSobolev.fourierCoeff (Z t ω) k + evolvingForcingCoord htr.dyn ρ (S.X n) k t ω :=
    fun n => hsys (n + 2) (by omega) (S.P n) (S.X₀ n) (S.W n) (S.X n) (hS n) (hSF n) (hfin n)
  choose Zs hZm hZc hZ1 hZ2 hZ3 hZ4 using hsysn
  -- the objects
  set Lin := adjkLin m T Vev hc with hLinDef
  set b : ℕ → ℝ := fun n => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
    (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
      Real.sqrt ((n + 2 : ℕ) : ℝ) with hbdef
  set Φ : ∀ n, S.Ω n → PathSpace d m T := fun n ω =>
    flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω with hΦ
  set η₀ : ∀ n, S.Ω n → NegSobolev d m := fun n ω =>
    etaE m (S.X₀ n ω) (withDensityReal (ρ 0)) with hη₀
  set Ξ : ∀ n, S.Ω n → PathSpace d m T := fun n ω => Φ n ω - Lin (η₀ n ω) with hΞ
  set Ξh : ∀ n, ℝ → S.Ω n → NegSobolev d m := fun n t ω =>
    etaE m (S.X n t.toNNReal ω) (withDensityReal (ρ t)) -
      Vev t 0 (etaE m (S.X n 0 ω) (withDensityReal (ρ 0))) with hΞh
  have hΦm : ∀ n, AEMeasurable (Φ n) (S.P n) := fun n =>
    adjk_flucPath_aemeasurable_proof hd htr m hmd2 T hT.le (by omega : 2 ≤ n + 2) (S.P n)
      (S.X₀ n) (S.W n) (S.X n) (hS n)
  have hηm : ∀ n, AEMeasurable (η₀ n) (S.P n) := fun n => hlaw.forall_aemeasurable n
  have hΞm : ∀ n, AEMeasurable (Ξ n) (S.P n) := fun n =>
    (hΦm n).sub (hLin.aemeasurable.comp_aemeasurable (hηm n))
  have hΞhm : ∀ n t, Measurable (Ξh n t) := fun n t =>
    (adjkg_etaE_measurable m hmd2 _ _ ((hS n).sol.adapted _)).sub
      ((Vev t 0).continuous.measurable.comp
        (adjkg_etaE_measurable m hmd2 _ _ ((hS n).sol.adapted _)))
  -- good events
  have hcont : ∀ n, ∀ᵐ ω ∂(S.P n), Continuous fun t : Set.Icc (0 : ℝ) T =>
      Real.sqrt ((n + 2 : ℕ) : ℝ) • NegSobolev.ofMeasureDiff m
        (empirical (S.X n (Real.toNNReal t) ω)) (withDensityReal (ρ t)) := by
    intro n
    filter_upwards [(hS n).sol.cont] with ω hω
    exact adjkd_fluc_cont_path hd htr m hmd2 T hT.le (S.X n) _ ω hω
  have hΞeq : ∀ n, ∀ᵐ ω ∂(S.P n), ∀ t : Set.Icc (0 : ℝ) T, (Ξ n ω).at' t = Ξh n t ω := by
    intro n
    filter_upwards [hcont n, (hS n).sol.init] with ω hcω hi t
    show (Φ n ω - Lin (η₀ n ω)).at' t = _
    rw [adjkg_at_sub, adjkg_flucPath_at m T _ (S.X n) ρ ω hcω t]
    show _ - Vev (t : ℝ) 0 (etaE m (S.X₀ n ω) (withDensityReal (ρ 0))) = _
    rw [← hi]
    rfl
  have hΞhc : ∀ n, ∀ᵐ ω ∂(S.P n), ContinuousOn (fun t => Ξh n t ω) (Set.Icc 0 T) := by
    intro n
    filter_upwards [hcont n] with ω hcω
    have h1 : ContinuousOn (fun t : ℝ => etaE m (S.X n t.toNNReal ω) (withDensityReal (ρ t)))
        (Set.Icc 0 T) := continuousOn_iff_continuous_restrict.2 hcω
    have h2 : ContinuousOn (fun t : ℝ => Vev t 0 (etaE m (S.X n 0 ω) (withDensityReal (ρ 0))))
        (Set.Icc 0 T) := continuousOn_iff_continuous_restrict.2 (hc _)
    exact h1.sub h2
  have hRc : ∀ n, ∀ᵐ ω ∂(S.P n), ContinuousOn (fun t => Ξh n t ω - Zs n t ω) (Set.Icc 0 T) := by
    intro n
    filter_upwards [hΞhc n] with ω hω
    exact hω.sub (hZc n ω)
  -- the remainder integral
  have hRint : ∀ n, ∫⁻ ω, ⨆ t ∈ ratIcc 0 T,
      (adjkEnergy m₂ m (Ξh n t ω - Zs n t ω)) ^ (1 / 2 : ℝ) ∂(S.P n) ≤ ENNReal.ofReal (Cr * b n) := by
    intro n
    have hae := adjkg_rem_energy (m₂ := m₂) Vev (fun ω => etaE m (S.X n 0 ω) (withDensityReal (ρ 0)))
      (fun t ω => etaE m (S.X n t.toNNReal ω) (withDensityReal (ρ t))) (Zs n)
      (fun k t ω => evolvingForcingCoord htr.dyn ρ (S.X n) k t ω) (hZ4 n)
    calc ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (adjkEnergy m₂ m (Ξh n t ω - Zs n t ω)) ^ (1 / 2 : ℝ) ∂(S.P n)
        = ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (∑' k : NonzeroLattice d,
            ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m₂) *
              evolvingForcingCoord htr.dyn ρ (S.X n) k t ω ^ 2)) ^ (1 / 2 : ℝ) ∂(S.P n) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          exact biSup_congr fun t ht => by rw [hω t ht.1]
      _ ≤ ENNReal.ofReal (Cr * entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
          (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
            Real.sqrt ((n + 2 : ℕ) : ℝ)) := hZ3 n
      _ = ENNReal.ofReal (Cr * b n) := by rw [mul_div_assoc]
  -- tightness
  obtain ⟨KB, hKB⟩ := hB.bddAbove_range
  set KB' : ℝ := max KB 0 with hKB'
  have hbKB : ∀ n, b n ≤ KB' := fun n => (hKB ⟨n, rfl⟩).trans (le_max_left _ _)
  have hCrKB : 0 ≤ Cr * KB' := mul_nonneg hCr0 (le_max_right _ _)
  have hsup : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n,
      (S.P n) {ω | ∃ t, ENNReal.ofReal (R ^ 2) < adjkEnergy m₂ m ((Ξ n ω).at' t)} ≤
        ENNReal.ofReal ε := by
    intro ε hε
    set K : ℝ := 1 + Cz + Cr * KB' with hK
    have hK1 : 1 ≤ K := by rw [hK]; linarith
    refine ⟨2 * K / ε, fun n => ?_⟩
    have hR : 0 < 2 * K / ε := by positivity
    have hmain := adjkg_sup_tail (m₁ := m₂) (j := (j : ℝ)) hjm₂ hT (S.P n) (Ξh n) (Zs n) (hΞhm n)
      (hZm n) (hΞhc n) hCz0 hCrKB (hZ1 n)
      ((hRint n).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hbKB n) hCr0))) hR
    refine le_trans (measure_mono_ae ?_) (hmain.trans (le_of_eq ?_))
    · filter_upwards [hΞeq n] with ω hω hbad
      obtain ⟨t, ht⟩ := hbad
      exact ⟨t, t.2, by rw [← hω t]; exact ht⟩
    · congr 1
      rw [hK]
      field_simp
  have hequi : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ n,
      (S.P n) {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧
        η < ‖(Ξ n ω).at' s - (Ξ n ω).at' t‖} ≤ ENNReal.ofReal ε := by
    intro ε η hε hη
    obtain ⟨δ₁, hδ₁, hK⟩ := adjkg_kolm hT hCz0 S.P Zs hZm hZc hZ2 (ε / 2) (η / 2)
      (half_pos hε) (half_pos hη)
    -- the remainder is uniformly small for large `n`
    have hsmall : ∀ᶠ n in atTop, b n ≤ (ε * η / 8) / (Cr + 1) := by
      have : (0 : ℝ) < (ε * η / 8) / (Cr + 1) := by positivity
      exact hB.eventually (gt_mem_nhds this) |>.mono fun n hn => hn.le
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hsmall
    -- finitely many `n < n₀`
    have hmod : ∀ n, ∃ δ : ℝ, 0 < δ ∧ (S.P n) {ω | ∃ s t : Set.Icc (0 : ℝ) T,
        |(s : ℝ) - t| ≤ δ ∧ η < ‖(Ξ n ω).at' s - (Ξ n ω).at' t‖} ≤ ENNReal.ofReal ε :=
      fun n => adjkg_modulus_small hT.le (S.P n) (Ξ n) (hΞm n) hη hε
    choose δn hδn hδnb using hmod
    obtain ⟨δ₂, hδ₂, hδ₂le⟩ := adjkg_exists_pos_le δn hδn n₀
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun n => ?_⟩
    by_cases hn : n < n₀
    · refine le_trans (measure_mono ?_) (hδnb n)
      rintro ω ⟨s, t, hst, h⟩
      exact ⟨s, t, hst.trans ((min_le_right _ _).trans (hδ₂le n hn)), h⟩
    · push_neg at hn
      have hbn := hn₀ n hn
      set AZ : Set (S.Ω n) := {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ₁ ∧
        η / 2 < ‖Zs n s ω - Zs n t ω‖} with hAZ
      set AR : Set (S.Ω n) := {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, η / 4 < ‖Ξh n t ω - Zs n t ω‖} with hAR
      have hZtail : (S.P n) AZ ≤ ENNReal.ofReal (ε / 2) := hK n
      have hRtail : (S.P n) AR ≤ ENNReal.ofReal (ε / 2) := by
        have h1 := adjkg_rem_tail (m₁ := m₂) hm₂m.le hT (S.P n) (fun t ω => Ξh n t ω - Zs n t ω)
          (fun t => (hΞhm n t).sub (hZm n t)) (hRc n) (hRint n) (show 0 < η / 4 by positivity)
        refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
        have hc1 : Cr * b n ≤ ε * η / 8 := by
          calc Cr * b n ≤ Cr * ((ε * η / 8) / (Cr + 1)) := mul_le_mul_of_nonneg_left hbn hCr0
            _ ≤ (Cr + 1) * ((ε * η / 8) / (Cr + 1)) :=
                mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = ε * η / 8 := by field_simp
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      refine le_trans (measure_mono_ae ?_) ((measure_union_le AZ AR).trans ?_)
      · filter_upwards [hΞeq n] with ω hω hbad
        obtain ⟨s, t, hst, h⟩ := hbad
        by_contra hnot
        simp only [Set.mem_union, not_or, hAZ, hAR, Set.mem_setOf_eq, not_exists, not_and, not_lt] at hnot
        obtain ⟨hn1, hn2⟩ := hnot
        have h1 := hn1 s t (hst.trans (min_le_left _ _))
        have h2 := hn2 s s.2
        have h3 := hn2 t t.2
        rw [hω s, hω t] at h
        have e : Ξh n s ω - Ξh n t ω = (Zs n s ω - Zs n t ω) +
            ((Ξh n s ω - Zs n s ω) - (Ξh n t ω - Zs n t ω)) := by abel
        rw [e] at h
        have := norm_add_le (Zs n s ω - Zs n t ω)
          ((Ξh n s ω - Zs n s ω) - (Ξh n t ω - Zs n t ω))
        have := norm_sub_le (Ξh n s ω - Zs n s ω) (Ξh n t ω - Zs n t ω)
        linarith
      · calc (S.P n) AZ + (S.P n) AR ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
              add_le_add hZtail hRtail
          _ = ENNReal.ofReal ε := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1; ring
  have hid : ∀ n, ∀ᵐ ω ∂(S.P n), Φ n ω = Lin (η₀ n ω) + Ξ n ω := fun n =>
    Filter.Eventually.of_forall fun ω => by simp [Ξ]
  exact adjkg_tight_of_components (m₁ := m₂) hm₂m S.P Φ Ξ η₀ Lin hLin hηm hΞm P' η₀' hlaw hsup hequi hid

end HRS.AdjK
