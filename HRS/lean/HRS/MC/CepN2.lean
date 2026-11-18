import HRS.MC.CepC0

/-!
# Packet CEPN2: deterministic tube stability for the additive-noise ODE on `liftedFree`

Gronwall (integral form, via the monotone function `F(t) e^{-Lt}`) plus a first-exit argument.
The frozen statement lives in `HRS/MC/CepaSpec.lean` (`HRS.MC.Cepa.cep_N2_tube_stability`); the tie is in
`HRS/MC/CepN2Tie.lean`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN2

open HRS

/-- Integral Gronwall for a continuous nonnegative-rate bound. -/
theorem cepn2_gronwall {e : ℝ → ℝ} (he : Continuous e) {T a L : ℝ} (hL : 0 ≤ L)
    (h : ∀ t ∈ Set.Icc 0 T, e t ≤ a + L * ∫ u in (0 : ℝ)..t, e u) :
    ∀ t ∈ Set.Icc 0 T, e t ≤ a * Real.exp (L * t) := by
  set F : ℝ → ℝ := fun t => a + L * ∫ u in (0 : ℝ)..t, e u with hF
  set G : ℝ → ℝ := fun t => F t * Real.exp (-(L * t)) with hG
  have hFd : ∀ t, HasDerivAt F (L * e t) t := fun t => by
    have := (he.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul L
    simpa [hF] using this.const_add a
  have hGd : ∀ t, HasDerivAt G (L * e t * Real.exp (-(L * t)) + F t * (Real.exp (-(L * t)) * (-L))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(L * t)) (-L) t := by
      have := ((hasDerivAt_id' t).const_mul L).neg
      exact this.congr_deriv (by ring)
    exact (hFd t).mul h1.exp
  have hanti : AntitoneOn G (Set.Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (fun t _ => (hGd t).continuousAt.continuousWithinAt)
      (fun t _ => (hGd t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [(hGd t).deriv]
    have := h t ⟨(interior_subset ht).1, (interior_subset ht).2⟩
    have hx := Real.exp_pos (-(L * t))
    have : L * e t * Real.exp (-(L * t)) + F t * (Real.exp (-(L * t)) * (-L)) =
        L * Real.exp (-(L * t)) * (e t - F t) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 (h t ⟨(interior_subset ht).1, (interior_subset ht).2⟩))
  intro t ht
  have h0 : G 0 = a := by simp [hG, hF]
  have hGt : G t ≤ a := by
    have := hanti ⟨le_refl 0, ht.1.trans ht.2⟩ ht ht.1
    simpa [h0] using this
  have hFt : F t ≤ a * Real.exp (L * t) := by
    have hx := Real.exp_pos (L * t)
    have : F t = G t * Real.exp (L * t) := by
      simp only [hG]; rw [mul_assoc, ← Real.exp_add]; simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hGt hx.le
  exact (h t ht).trans hFt


/-- **N2 (deterministic tube stability for the additive-noise ODE on `liftedFree`)**.  Statement verbatim from
`HRS.MC.Cepa.cep_N2_tube_stability` (with the duplicated predicate `cep_IsC11`). -/
theorem cep_N2_tube_stability_proof {N : ℕ} {D : DynData 1} (hs : D.s = 0)
    (hV : HRS.MC.CepC0.cep_IsC11 D.V)
    {T' : ℝ} (hT' : 0 < T') {c v : ℝ → Fin N → Euc 1} (hc : Continuous c) (hv : Continuous v) (hv0 : v 0 = 0)
    (hcfree : ∀ t ∈ Set.Icc 0 T', c t ∈ liftedFree 1 N)
    (hceq : ∀ t ∈ Set.Icc 0 T', c t = c 0 + (∫ u in (0 : ℝ)..t, liftedDrift D (c u)) + v t) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∃ η : ℝ, 0 < η ∧
      ∀ (y V : ℝ → Fin N → Euc 1) (s : ℝ), 0 ≤ s → s ≤ T' → Continuous y →
        ‖y 0 - c 0‖ < η → (∀ t ∈ Set.Icc 0 s, ‖V t - v t‖ < η) →
        (∀ t ∈ Set.Icc 0 s, y t ∈ liftedFree 1 N) →
        (∀ t ∈ Set.Icc 0 s, y t = y 0 + (∫ u in (0 : ℝ)..t, liftedDrift D (y u)) + V t) →
        ∀ t ∈ Set.Icc 0 s, ‖y t - c t‖ < ε := by
  have hK : Torus.IsSmoothOffZero (periodicRieszGrad 1 D.s) :=
    (kernelLocal_d1 (by rw [hs]) (by rw [hs]; norm_num)).smoothOffZero
  have hloc : IsLocLipschitzDrift (liftedFree 1 N) (fun _ Z => liftedDrift (N := N) D Z) :=
    HRS.MC.CepC0.cep_C0_locLipschitz_proof (d := 1) (N := N) D hK hV
  have hUo : IsOpen (liftedFree 1 N) := isOpen_liftedFree 1 N
  have hKc : IsCompact (c '' Set.Icc 0 T') := isCompact_Icc.image hc
  have hKU : c '' Set.Icc 0 T' ⊆ liftedFree 1 N := by
    rintro _ ⟨t, ht, rfl⟩; exact hcfree t ht
  obtain ⟨r, hr, hrK⟩ := hKc.exists_cthickening_subset_open hUo hKU
  have hKrc : IsCompact (Metric.cthickening r (c '' Set.Icc 0 T')) := hKc.cthickening
  obtain ⟨L, hL⟩ := hloc.lip _ hKrc hrK 0
  have hL' : LipschitzOnWith L (liftedDrift D) (Metric.cthickening r (c '' Set.Icc 0 T')) :=
    hL 0 ⟨le_refl _, le_refl _⟩
  have hcontU : ContinuousOn (liftedDrift (N := N) D) (liftedFree 1 N) := by
    have hg : ContinuousOn (fun z : Fin N → Euc 1 => ((0 : ℝ), z)) (liftedFree 1 N) :=
      continuousOn_const.prodMk continuousOn_id
    have hmap : Set.MapsTo (fun z : Fin N → Euc 1 => ((0 : ℝ), z)) (liftedFree 1 N)
        (Set.Ici (0 : ℝ) ×ˢ liftedFree 1 N) := fun z hz => Set.mk_mem_prod (Set.mem_Ici.2 le_rfl) hz
    have h := ContinuousOn.comp (g := Function.uncurry fun (_ : ℝ) (Z : Fin N → Euc 1) => liftedDrift D Z)
      hloc.cont hg hmap
    refine h.congr fun z _ => ?_
    simp only [Function.comp_apply, Function.uncurry_apply_pair]
  refine ⟨r, hr, fun ε hε hεr => ?_⟩
  have hE : 1 ≤ Real.exp ((L : ℝ) * T') := Real.one_le_exp (by positivity)
  have hEpos : 0 < Real.exp ((L : ℝ) * T') := Real.exp_pos _
  refine ⟨ε / (4 * Real.exp ((L : ℝ) * T')), by positivity, ?_⟩
  set η := ε / (4 * Real.exp ((L : ℝ) * T')) with hη
  have hηε : η < ε := by
    rw [hη, div_lt_iff₀ (by positivity)]; nlinarith
  have h2η : 2 * η * Real.exp ((L : ℝ) * T') = ε / 2 := by
    rw [hη]; field_simp; ring
  intro y V s hs0 hsT hy hy0 hVv _ hyeq t ht
  by_contra hcon
  set e : ℝ → ℝ := fun t => ‖y t - c t‖ with he_def
  have he : Continuous e := (hy.sub hc).norm
  set S : Set ℝ := {u | u ∈ Set.Icc 0 s ∧ ε ≤ e u} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const he)
  have hne : S.Nonempty := ⟨t, ht, not_lt.1 hcon⟩
  have hbdd : BddBelow S := ⟨0, fun u hu => hu.1.1⟩
  have ht1 : sInf S ∈ S := hSc.csInf_mem hne hbdd
  set t1 := sInf S with ht1_def
  have hlt : ∀ u ∈ Set.Icc 0 s, u < t1 → e u < ε := by
    intro u hu hu1
    by_contra hh
    exact absurd (csInf_le hbdd ⟨hu, not_lt.1 hh⟩) (not_le.2 hu1)
  have ht1pos : 0 < t1 := by
    rcases ht1.1.1.eq_or_lt with h0 | h0
    · exfalso
      have := ht1.2
      rw [← h0] at this
      have h00 : e 0 < η := hy0
      linarith
    · exact h0
  have hbound : ∀ u ∈ Set.Icc 0 t1, e u ≤ ε := by
    have hcl : closure (Set.Ico 0 t1) ⊆ {u | e u ≤ ε} :=
      (isClosed_le he continuous_const).closure_subset_iff.2
        (fun u hu => (hlt u ⟨hu.1, hu.2.le.trans ht1.1.2⟩ hu.2).le)
    rw [closure_Ico ht1pos.ne] at hcl
    exact fun u hu => hcl hu
  have hmem : ∀ u ∈ Set.Icc 0 t1, y u ∈ Metric.cthickening r (c '' Set.Icc 0 T') := by
    intro u hu
    exact Metric.mem_cthickening_of_dist_le (y u) (c u) r _
      ⟨u, ⟨hu.1, hu.2.trans (ht1.1.2.trans hsT)⟩, rfl⟩
      (by rw [dist_eq_norm]; exact (hbound u hu).trans hεr)
  have hcmem : ∀ u ∈ Set.Icc 0 t1, c u ∈ Metric.cthickening r (c '' Set.Icc 0 T') := fun u hu =>
    Metric.self_subset_cthickening _ ⟨u, ⟨hu.1, hu.2.trans (ht1.1.2.trans hsT)⟩, rfl⟩
  have hyc : ContinuousOn (fun u => liftedDrift (N := N) D (y u)) (Set.Icc 0 t1) :=
    hcontU.comp hy.continuousOn (fun u hu => hrK (hmem u hu))
  have hcc : ContinuousOn (fun u => liftedDrift (N := N) D (c u)) (Set.Icc 0 t1) :=
    hcontU.comp hc.continuousOn (fun u hu => hrK (hcmem u hu))
  have hgr : ∀ t ∈ Set.Icc 0 t1, e t ≤ 2 * η + (L : ℝ) * ∫ u in (0 : ℝ)..t, e u := by
    intro t ht
    have hts : t ∈ Set.Icc 0 s := ⟨ht.1, ht.2.trans ht1.1.2⟩
    have htT : t ∈ Set.Icc 0 T' := ⟨ht.1, ht.2.trans (ht1.1.2.trans hsT)⟩
    have hi1 : IntervalIntegrable (fun u => liftedDrift (N := N) D (y u)) MeasureTheory.volume 0 t :=
      (hyc.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hi2 : IntervalIntegrable (fun u => liftedDrift (N := N) D (c u)) MeasureTheory.volume 0 t :=
      (hcc.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    have hdec : y t - c t = (y 0 - c 0) + (∫ u in (0 : ℝ)..t, (liftedDrift D (y u) - liftedDrift D (c u)))
        + (V t - v t) := by
      rw [intervalIntegral.integral_sub hi1 hi2]
      have h1 := hyeq t hts
      have h2 := hceq t htT
      calc y t - c t = (y 0 + (∫ u in (0 : ℝ)..t, liftedDrift D (y u)) + V t) -
            (c 0 + (∫ u in (0 : ℝ)..t, liftedDrift D (c u)) + v t) := by rw [← h1, ← h2]
        _ = _ := by abel
    have hint : ‖∫ u in (0 : ℝ)..t, (liftedDrift D (y u) - liftedDrift D (c u))‖ ≤
        (L : ℝ) * ∫ u in (0 : ℝ)..t, e u := by
      refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on ht.1 (hi1.sub hi2).norm
        ((continuous_const.mul he).intervalIntegrable _ _) fun u hu => ?_
      have hu' : u ∈ Set.Icc 0 t1 := ⟨hu.1, hu.2.trans ht.2⟩
      have := hL'.dist_le_mul (y u) (hmem u hu') (c u) (hcmem u hu')
      rw [dist_eq_norm, dist_eq_norm] at this
      exact this
    have hV1 := hVv t hts
    calc e t = ‖y t - c t‖ := rfl
      _ = ‖(y 0 - c 0) + (∫ u in (0 : ℝ)..t, (liftedDrift D (y u) - liftedDrift D (c u)))
        + (V t - v t)‖ := by rw [hdec]
      _ ≤ ‖y 0 - c 0‖ + ‖∫ u in (0 : ℝ)..t, (liftedDrift D (y u) - liftedDrift D (c u))‖ +
          ‖V t - v t‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 2 * η + (L : ℝ) * ∫ u in (0 : ℝ)..t, e u := by linarith
  have hG := cepn2_gronwall he (T := t1) (a := 2 * η) (L := (L : ℝ)) L.2 hgr t1 ⟨ht1pos.le, le_refl _⟩
  have hexp : Real.exp ((L : ℝ) * t1) ≤ Real.exp ((L : ℝ) * T') :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (ht1.1.2.trans hsT) L.2)
  have : e t1 ≤ ε / 2 := by
    rw [← h2η]
    exact hG.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have := ht1.2
  linarith

end HRS.MC.CepN2
