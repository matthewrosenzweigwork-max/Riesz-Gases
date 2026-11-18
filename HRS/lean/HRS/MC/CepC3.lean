import HRS.MC.CepC0

/-!
# Packet CEPC3: collision alternative for the maximal particle solution under a `C^{1,1}` potential

Copy-adapted from `HRS.liftedDrift_bounded_of_sep` and `HRS.IsMaximalParticleSolution.collision_alternative`
(`HRS/Stochastic/Particle.lean`).  `Torus.IsCk 2 D.V` is used there only through the continuity of the lifted
drift on the collision-free region; under `cep_IsC11` this continuity is supplied by `HRS.MC.CepC0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepC3

open HRS HRS.MC.CepC0

section Aux

variable {d N : ℕ}

/-- The lifted drift is continuous on the collision-free region under `cep_IsC11`. -/
theorem cepc3_continuousOn_drift (D : DynData d)
    (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s)) (hV : cep_IsC11 D.V) :
    ContinuousOn (liftedDrift (N := N) D) (liftedFree d N) := by
  obtain ⟨_, LV, hLV⟩ := hV
  have hC := cepc0_contDiffOn_pair (N := N) D hK
  have hP := cepc0_lipschitz_pot (N := N) D hLV
  have e : (liftedDrift (N := N) D) = fun Y => cepc0_pair D Y - cepc0_pot D Y :=
    funext fun Y => cepc0_drift_eq D Y
  rw [e]
  exact hC.continuousOn.sub hP.continuous.continuousOn

/-- The lifted drift is bounded on `ε`-separated configurations (`cep_IsC11` version). -/
theorem cepc3_liftedDrift_bounded_of_sep (D : DynData d)
    (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s)) (hV : cep_IsC11 D.V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ Z : Fin N → Euc d,
      (∀ i j : Fin N, i ≠ j → ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))) →
        ‖liftedDrift D Z‖ ≤ B := by
  let Box : Set (Fin N → Euc d) :=
    Set.pi Set.univ fun _ => (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
  have hBox : IsCompact Box :=
    isCompact_univ_pi fun _ => (isCompact_univ_pi fun _ => isCompact_Icc).image
      (PiLp.continuous_toLp 2 _)
  have hF : IsCompact (Box ∩ {Z : Fin N → Euc d | ∀ i j : Fin N, i ≠ j →
      ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))}) :=
    hBox.inter_right (isClosed_sepSet d N ε)
  have hcont : ContinuousOn (liftedDrift (N := N) D) (Box ∩ {Z : Fin N → Euc d | ∀ i j : Fin N,
      i ≠ j → ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))}) :=
    (cepc3_continuousOn_drift D hK hV).mono fun Z hZ => mem_liftedFree_of_sep hε hZ.2
  obtain ⟨B, hB⟩ := hF.exists_bound_of_continuousOn hcont
  refine ⟨B, fun Z hZ => ?_⟩
  let Z' : Fin N → Euc d := fun i => Torus.rep (Torus.mk (Z i))
  have hmk : (fun i => Torus.mk (Z' i)) = fun i => Torus.mk (Z i) :=
    funext fun i => Torus.mk_rep _
  have hdr : liftedDrift D Z = liftedDrift D Z' := by
    unfold liftedDrift
    rw [hmk]
  rw [hdr]
  refine hB Z' ⟨?_, ?_⟩
  · intro i _
    refine ⟨fun a => Torus.rep (Torus.mk (Z i)) a, fun a _ => ?_, rfl⟩
    have := (AddCircle.equivIco (1 : ℝ) 0 (Torus.mk (Z i) a)).2
    simp only [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  · intro i j hij
    have := hZ i j hij
    have e : Torus.mk (Z' i) = Torus.mk (Z i) := congrFun hmk i
    have e' : Torus.mk (Z' j) = Torus.mk (Z j) := congrFun hmk j
    rw [e, e']
    exact this

end Aux

section Probabilistic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

/-- **C3 (collision alternative under `C^{1,1}`)**.  Statement verbatim from
`HRS.MC.Cepa.cep_C3_collision_alternative` (with the duplicated predicate `cep_IsC11`). -/
theorem cep_C3_collision_alternative_proof [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (D : DynData d) (hK : KernelLocal d D.s)
    (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) :
    ∀ᵐ ω ∂P, τ ω < ⊤ → ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℝ, 0 ≤ t₀ → (t₀ : WithTop ℝ) < τ ω →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ω ∧
        ∃ i j : Fin N, i ≠ j ∧ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < ε := by
  filter_upwards [hsol.sol.eq] with ω hω hτ ε hε t₀ ht₀ ht₀τ
  by_contra hcon
  have hsep : ∀ t : ℝ, t₀ < t → (t : WithTop ℝ) < τ ω → ∀ i j : Fin N, i ≠ j →
      ε ≤ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) := by
    intro t ht htτ i j hij
    by_contra h
    exact hcon ⟨t, ht, htτ, i, j, hij, not_le.1 h⟩
  obtain ⟨T₁, hT₁⟩ := WithTop.ne_top_iff_exists.1 hτ.ne
  have hlt : ∀ t : ℝ, (t : WithTop ℝ) < τ ω → t < T₁ := fun t ht => by
    rw [← hT₁] at ht
    exact_mod_cast ht
  have ht₀T : t₀ < T₁ := hlt t₀ ht₀τ
  obtain ⟨B, hB⟩ := cepc3_liftedDrift_bounded_of_sep (N := N) D hK.smoothOffZero hV hε
  -- bound on `[0, t₀]`
  obtain ⟨R₁, hR₁⟩ := (isCompact_Icc.image_of_continuousOn
    (hsol.sol.cont ω t₀ ht₀ ht₀τ)).isBounded.exists_norm_le
  have hY₁ : ‖Y t₀ ω‖ ≤ R₁ := hR₁ _ ⟨t₀, ⟨ht₀, le_rfl⟩, rfl⟩
  -- bound on the noise
  have hNc : Continuous (addNoise (liftedNoise (N := N) D) fun s => W' s ω) :=
    continuous_addNoise _ (hW'.cont ω)
  obtain ⟨R₂, hR₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T₁)).exists_bound_of_continuousOn
    hNc.continuousOn
  -- the path stays in a ball
  have hbound : ∀ t : ℝ, t₀ < t → (t : WithTop ℝ) < τ ω →
      ‖Y t ω‖ ≤ R₁ + |B| * |T₁| + 2 * R₂ := by
    intro t ht htτ
    have htT := hlt t htτ
    have ht0 : 0 ≤ t := ht₀.trans ht.le
    obtain ⟨hi₀, he₀⟩ := hω t₀ ht₀ ht₀τ
    obtain ⟨hi, he⟩ := hω t ht0 htτ
    have hii₀ : IntervalIntegrable (fun s => liftedDrift D (Y s ω)) volume 0 t₀ :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht₀).2 hi₀
    have hii : IntervalIntegrable (fun s => liftedDrift D (Y s ω)) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht0).2 hi
    have hI : ∀ u : ℝ, 0 ≤ u → ∫ s in Set.Icc 0 u, liftedDrift D (Y s ω) =
        ∫ s in (0 : ℝ)..u, liftedDrift D (Y s ω) := fun u hu => by
      rw [intervalIntegral.integral_of_le hu, integral_Icc_eq_integral_Ioc]
    have hdiff : ∫ s in t₀..t, liftedDrift D (Y s ω) =
        (∫ s in Set.Icc 0 t, liftedDrift D (Y s ω)) -
          ∫ s in Set.Icc 0 t₀, liftedDrift D (Y s ω) := by
      rw [hI t ht0, hI t₀ ht₀, intervalIntegral.integral_interval_sub_left hii hii₀]
    have hint : ‖∫ s in t₀..t, liftedDrift D (Y s ω)‖ ≤ B * |t - t₀| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
      rw [Set.uIoc_of_le ht.le] at hs
      exact hB _ (hsep s hs.1 (by
        rw [← hT₁]; exact_mod_cast lt_of_le_of_lt hs.2 htT))
    have hnt := hR₂ t ⟨ht0, htT.le⟩
    have hnt₀ := hR₂ t₀ ⟨ht₀, ht₀T.le⟩
    have hNN : ∀ u : ℝ, ∑ k, ofNNRealTime W' u ω k • liftedNoise (N := N) D k =
        addNoise (liftedNoise (N := N) D) (fun s => W' s ω) u := fun u => rfl
    rw [hNN] at he he₀
    have hYt : Y t ω = Y t₀ ω + (∫ s in t₀..t, liftedDrift D (Y s ω)) +
        (addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t -
          addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t₀) := by
      rw [hdiff, he, he₀]
      abel
    have habs : |t - t₀| ≤ |T₁| := by
      rw [abs_of_nonneg (by linarith)]
      exact (by linarith : t - t₀ ≤ T₁).trans (le_abs_self T₁)
    have hBt : B * |t - t₀| ≤ |B| * |T₁| :=
      (mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left habs (abs_nonneg _))
    rw [hYt]
    have h1 := norm_add_le (Y t₀ ω + ∫ s in t₀..t, liftedDrift D (Y s ω))
      (addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t -
        addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t₀)
    have h2 := norm_add_le (Y t₀ ω) (∫ s in t₀..t, liftedDrift D (Y s ω))
    have h3 := norm_sub_le (addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t)
      (addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t₀)
    linarith
  -- the compact set
  set R := R₁ + |B| * |T₁| + 2 * R₂ with hR
  let K : Set (Fin N → Euc d) := Metric.closedBall 0 R ∩ {Z : Fin N → Euc d | ∀ i j : Fin N,
    i ≠ j → ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))}
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right (isClosed_sepSet d N ε)
  have hKU : K ⊆ liftedFree d N := fun Z hZ => mem_liftedFree_of_sep hε hZ.2
  obtain ⟨t, ht, htτ, hnot⟩ := hsol.exit ω hτ K hKc hKU t₀ ht₀τ
  refine hnot ⟨?_, hsep t ht htτ⟩
  rw [mem_closedBall_zero_iff]
  exact hbound t ht htτ

end Probabilistic

end HRS.MC.CepC3
