import HRS.ME.EVUB

/-!
# Chunk E, packet EVC: V-uniform `H^K` bound by Volterra bootstrapping (`_unifV`)

Copies in namespace `HRS.ME.EVU` of the Volterra chain of `HRS/PDE/MeanFieldAprioriSobolev.lean`, with every constant chosen
before the potential `V` (`Bv` fixed first):
* `duhamel_core_unifV` of `HRS.PDE.MFApriori.duhamel_core` (`MeanFieldAprioriSobolev.lean:176`): the only `V`-dependent
  constant of the original is `Cn` of `exists_nl_loss`, replaced by `exists_nl_loss_unifV` (EVUB);
* `exists_volterra_step_unifV` of `exists_volterra_step` (`:337`);
* `exists_short_time_bound_unifV` of `exists_short_time_bound` (`:388`);
* `exists_hK_bound_unifV` of `HRS.PDE.MFApriori.exists_hK_bound` (`:451`): the statement is the original with `(Bv : ℝ)` before
  `∃ C` and `∀ V, IsCk (K+2) V → cbNorm (K+2) V ≤ Bv → …` in front of the solution data.

Qualitative per-`V` facts (`mild_eq_Icc`, `rhs_continuousInHsOn_vt`, the continuity of the solution, `H.sol.init`) are used
as in the original with `V` at hand. Internal per-solution constants (`Bψ` in `exists_volterra_step`, `Bφ` in
`exists_short_time_bound`, the phase constants of `exists_hK_bound`) enter only as bounds in the proofs of the inequalities and
never in the final constants: those are `C' * (Ch * (1 + νm^(-1/2)))`, `max (C' * (Ch * 2)) 1`, and
`max BK (Cs' ^ (K+1) * ‖ρ̂₀‖_{H^K})`, all built from the `V`-uniform lemmas.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS.PDE HRS.PDE.MFApriori

namespace HRS.ME.EVU

variable {d : ℕ}

/-- `V`-uniform version of `HRS.PDE.MFApriori.duhamel_core` (`MeanFieldAprioriSobolev.lean:176`). -/
theorem duhamel_core_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (νm νp : ℝ)
    (hνm : 0 < νm) (Λ : ℝ) (j : ℝ) (hj1 : 1 ≤ j) (hjK : j ≤ K) (Bv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V → Torus.cbNorm (K + 2) V ≤ Bv →
      ∀ ν ∈ Set.Icc νm νp, ∀ (ρ₀ : Torus d → ℝ) (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ v, 0 ≤ v → ∀ t, 0 < t → t ≤ 1 → v + t ≤ T →
        hsNorm j (ρc (v + t)) ≤ hsNorm j (fun k => (heatMult (ν * t) k : ℂ) * ρc v k) +
          C * ∫ σ in (0 : ℝ)..t, (t - σ) ^ (-((1 + bExp d s) / 2)) * hsNorm j (ρc (v + σ)) := by
  obtain ⟨hb, hb1', hb0⟩ := bExp_spec (d := d) s hsd
  set b := bExp d s with hbdef
  have hb1 : b ≤ 1 := hb1'.le
  set γ : ℝ := (1 + b) / 2 with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ < 1 := by rw [hγ]; linarith
  obtain ⟨Cn, hCn0, hCn⟩ := exists_nl_loss_unifV hd s hs0 hsd b hb hb1 K j hj1 hjK Bv
  obtain ⟨Ch, hCh0, hCh⟩ := exists_heat_smoothing (d := d) (j - (1 + b)) (1 + b)
    (by linarith) (by linarith)
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  refine ⟨Ch * Cn * (Λ' + 1) * (1 + νm ^ (-γ)), ?_, ?_⟩
  · have : 0 ≤ νm ^ (-γ) := Real.rpow_nonneg hνm.le _
    positivity
  intro V hV hVB ν hν ρ₀ T ρc H hΛ v hv t ht0 ht1 hvt
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hKd : (d : ℝ) / 2 < K := by linarith
  have hmem : ∀ σ ∈ Set.Icc (0 : ℝ) t, v + σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨add_nonneg hv hσ.1, by linarith [hσ.2]⟩
  have hcontj : ContinuousInHsOn j ρc (Set.Icc 0 T) := continuousInHsOn_mono_idx (by exact_mod_cast hjK) H.sol.cont
  have hψc : ContinuousOn (fun σ => hsNorm j (ρc (v + σ))) (Set.Icc 0 t) :=
    (continuousOn_hsNorm_path hcontj).comp (continuousOn_const.add continuousOn_id) (fun σ hσ => hmem σ hσ)
  have heq : ∀ k, ∀ u ∈ Set.Icc 0 T,
      ρc u k = ρc 0 k + ∫ σ in (0 : ℝ)..u, mfRhsCoeff d s V ν (ρc σ) k := by
    intro k u hu
    rw [H.sol.eq k u hu, H.sol.init]
  have hmild := fun k => mild_eq_Icc hd s hs0 hsd K (by linarith) V hV ν hν0 ρc T H.sol.cont heq k
    hv ht0.le hvt
  -- the integrand
  set Fc : ℝ → Coeff d := fun σ k => (heatMult (ν * (t - σ)) k : ℂ) *
    Aux.nlCoeff d s V (ρc (v + σ)) k with hFc
  have hsplit : ρc (v + t) = (fun k => (heatMult (ν * t) k : ℂ) * ρc v k) +
      fun k => ∫ σ in (0 : ℝ)..t, Fc σ k := by
    funext k
    rw [hmild k]
    simp only [Pi.add_apply]
    congr 1
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [hFc]
    have := congr_fun (rhs_sub_laplace_eq s V ν (ρc (v + σ))) k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
  -- pointwise estimates
  set Cg : ℝ := Ch * Cn * (Λ' + 1) * (1 + νm ^ (-γ)) with hCg
  have hpt : ∀ σ ∈ Set.Ioo (0 : ℝ) t, MemHs j (Fc σ) ∧
      hsNorm j (Fc σ) ≤ Cg * ((t - σ) ^ (-γ) * hsNorm j (ρc (v + σ))) := by
    intro σ hσ
    have hσ' : v + σ ∈ Set.Icc (0 : ℝ) T := hmem σ ⟨hσ.1.le, hσ.2.le⟩
    have hfc := H.continuous_mfPath hKd hσ'
    have hco := H.coeffOf_mfPath hKd hσ'
    have hfj : MemHs j (coeffOf (mfPath ρc (v + σ))) := by
      rw [hco]; exact memHs_mono' (by exact_mod_cast hjK) (H.sol.cont.1 _ hσ')
    have hsup : Torus.supNorm (mfPath ρc (v + σ)) ≤ Λ' :=
      ProdAux.supNorm_le_of_bdd fun x => (hΛ _ hσ' x).trans (le_max_left _ _)
    obtain ⟨hNm, hNb⟩ := hCn V hV hVB _ hfc hfj
    rw [hco] at hNm hNb
    have htσ : 0 < t - σ := by linarith [hσ.2]
    obtain ⟨hHm, hHb⟩ := hCh ν (t - σ) hν0 htσ _ hNm
    rw [sub_add_cancel] at hHm hHb
    refine ⟨hHm, hHb.trans ?_⟩
    have hk := kernel_le hνm hν.1 htσ (by linarith [hσ.1]) hγ0
    have hnn := hsNorm_nonneg' (j - (1 + b)) (Aux.nlCoeff d s V (ρc (v + σ)))
    have hψ0 := hsNorm_nonneg' j (ρc (v + σ))
    have hsn0 : 0 ≤ Torus.supNorm (mfPath ρc (v + σ)) + 1 := by
      have : 0 ≤ Torus.supNorm (mfPath ρc (v + σ)) := by
        unfold Torus.supNorm
        exact Real.iSup_nonneg fun x => norm_nonneg _
      linarith
    have h1 : hsNorm (j - (1 + b)) (Aux.nlCoeff d s V (ρc (v + σ))) ≤
        Cn * (Λ' + 1) * hsNorm j (ρc (v + σ)) :=
      hNb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCn0) hψ0)
    calc Ch * (1 + (ν * (t - σ)) ^ (-γ)) * hsNorm (j - (1 + b)) (Aux.nlCoeff d s V (ρc (v + σ)))
        ≤ Ch * ((1 + νm ^ (-γ)) * (t - σ) ^ (-γ)) * (Cn * (Λ' + 1) * hsNorm j (ρc (v + σ))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hk hCh0) h1 hnn ?_
          exact mul_nonneg hCh0 (mul_nonneg (by have := Real.rpow_nonneg hνm.le (-γ); linarith) (Real.rpow_nonneg htσ.le _))
      _ = Cg * ((t - σ) ^ (-γ) * hsNorm j (ρc (v + σ))) := by rw [hCg]; ring
  -- measurability and integrability
  have hcm : ∀ k, ContinuousOn (fun σ => Fc σ k) (Set.Icc 0 t) := by
    intro k
    have hR : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Icc 0 T) :=
      Aux.continuousOn_mode (rhs_continuousInHsOn_vt hd s hs0 hsd K (by linarith) V hV ν ρc _ H.sol.cont) k
    have hy : ContinuousOn (fun σ => ρc σ k) (Set.Icc 0 T) := Aux.continuousOn_mode H.sol.cont k
    have hshift : ContinuousOn (fun σ => v + σ) (Set.Icc (0 : ℝ) t) :=
      continuousOn_const.add continuousOn_id
    have hRs := hR.comp hshift (fun σ hσ => hmem σ hσ)
    have hys := hy.comp hshift (fun σ hσ => hmem σ hσ)
    have hN : ContinuousOn (fun σ => Aux.nlCoeff d s V (ρc (v + σ)) k) (Set.Icc 0 t) := by
      have : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc (v + σ)) k -
          (ν : ℂ) * laplaceCoeff (ρc (v + σ)) k) (Set.Icc 0 t) := by
        refine hRs.sub (continuousOn_const.mul ?_)
        simp only [laplaceCoeff]
        exact continuousOn_const.mul hys
      refine this.congr fun σ _ => ?_
      have := congr_fun (rhs_sub_laplace_eq s V ν (ρc (v + σ))) k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this.symm
    have hheat : ContinuousOn (fun σ : ℝ => ((heatMult (ν * (t - σ)) k : ℝ) : ℂ)) (Set.Icc 0 t) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      unfold heatMult
      exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
    exact hheat.mul hN
  have hmeas : ∀ k, AEStronglyMeasurable (fun σ => Fc σ k) (volume.restrict (Set.Ioc 0 t)) :=
    fun k => ((hcm k).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hgint : IntervalIntegrable
      (fun σ => Cg * ((t - σ) ^ (-γ) * hsNorm j (ρc (v + σ)))) volume 0 t := by
    refine IntervalIntegrable.const_mul ?_ _
    refine (intervalIntegrable_sub_rpow_neg γ hγ1 t).mul_continuousOn ?_
    rwa [Set.uIcc_of_le ht0.le]
  have hae := ae_Ioo_of_Ioc 0 t
  have hint : IntegrableOn (fun σ => hsNorm j (Fc σ)) (Set.Ioc 0 t) := by
    refine Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).1 hgint)
      (aestronglyMeasurable_hsNorm j Fc hmeas) ?_
    filter_upwards [hae] with σ hσ
    rw [Real.norm_of_nonneg (hsNorm_nonneg' _ _)]
    exact (hpt σ hσ).2
  obtain ⟨hIm, hIb⟩ := hsNorm_intervalIntegral_le j Fc 0 t ht0.le hmeas (fun σ hσ => (hpt σ hσ).1) hint
  have hmono : ∫ σ in (0 : ℝ)..t, hsNorm j (Fc σ) ≤
      ∫ σ in (0 : ℝ)..t, Cg * ((t - σ) ^ (-γ) * hsNorm j (ρc (v + σ))) := by
    rw [intervalIntegral.integral_of_le ht0.le, intervalIntegral.integral_of_le ht0.le]
    refine integral_mono_ae hint ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).1 hgint) ?_
    filter_upwards [hae] with σ hσ using (hpt σ hσ).2
  have hdat : MemHs j (fun k => (heatMult (ν * t) k : ℂ) * ρc v k) :=
    memHs_heat (memHs_mono' (by exact_mod_cast hjK) (H.sol.cont.1 v ⟨hv, by linarith⟩))
      (mul_nonneg hν0.le ht0.le)
  rw [hsplit]
  refine (Aux.memHs_add_le j hdat hIm).2.trans ?_
  rw [intervalIntegral.integral_const_mul] at hmono
  linarith

/-- `V`-uniform version of `HRS.PDE.MFApriori.exists_volterra_step` (`MeanFieldAprioriSobolev.lean:337`). -/
theorem exists_volterra_step_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (Λ : ℝ) (j : ℝ) (hj1 : 1 ≤ j) (hjK : j ≤ K) (Bv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V → Torus.cbNorm (K + 2) V ≤ Bv →
      ∀ ν ∈ Set.Icc νm νp, ∀ (ρ₀ : Torus d → ℝ) (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ v, 0 ≤ v → v + 1 ≤ T → ∀ B, (∀ r ∈ Set.Icc 0 1, hsNorm (j - 1) (ρc (v + r)) ≤ B) →
        hsNorm j (ρc (v + 1)) ≤ C * B := by
  obtain ⟨hb, hb1', hb0⟩ := bExp_spec (d := d) s hsd
  set γ : ℝ := (1 + bExp d s) / 2 with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ < 1 := by rw [hγ]; linarith
  obtain ⟨C2, hC20, hC2⟩ := duhamel_core_unifV hd s hs0 hsd K hK νm νp hνm Λ j hj1 hjK Bv
  obtain ⟨C', hC'0, hC'⟩ := singular_gronwall γ C2 hγ0 hγ1 hC20
  obtain ⟨Ch, hCh0, hCh⟩ := exists_heat_smoothing (d := d) (j - 1) 1 (by norm_num) (by norm_num)
  have hn0 : 0 ≤ νm ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hνm.le _
  refine ⟨C' * (Ch * (1 + νm ^ (-(1 / 2 : ℝ)))), by positivity, ?_⟩
  intro V hV hVB ν hν ρ₀ T ρc H hΛ v hv hvT B hB
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hB0 : 0 ≤ B := (hsNorm_nonneg' _ _).trans (by simpa using hB 0 ⟨le_rfl, zero_le_one⟩)
  have hmem : ∀ σ ∈ Set.Icc (0 : ℝ) 1, v + σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨add_nonneg hv hσ.1, by linarith [hσ.2]⟩
  have hcontj : ContinuousInHsOn j ρc (Set.Icc 0 T) :=
    continuousInHsOn_mono_idx (by exact_mod_cast hjK) H.sol.cont
  have hψc : ContinuousOn (fun σ => hsNorm j (ρc (v + σ))) (Set.Icc 0 1) :=
    (continuousOn_hsNorm_path hcontj).comp (continuousOn_const.add continuousOn_id)
      (fun σ hσ => hmem σ hσ)
  obtain ⟨Bψ, hBψ⟩ := isCompact_Icc.exists_bound_of_continuousOn hψc
  set A : ℝ := Ch * (1 + νm ^ (-(1 / 2 : ℝ))) * B with hA
  have hA0 : 0 ≤ A := by positivity
  have hmv : MemHs (j - 1) (ρc v) :=
    memHs_mono' (by have : (j : ℝ) ≤ K := hjK; linarith) (H.sol.cont.1 v ⟨hv, by linarith⟩)
  have key := hC' (fun σ => hsNorm j (ρc (v + σ))) A Bψ hA0 hψc
    (fun t ht => ⟨hsNorm_nonneg' _ _, (le_abs_self _).trans (by simpa using hBψ t ht)⟩) (by
      intro t ht
      have hcore := hC2 V hV hVB ν hν ρ₀ T ρc H hΛ v hv t ht.1 ht.2 (by linarith [ht.2])
      obtain ⟨-, hh⟩ := hCh ν t hν0 ht.1 (ρc v) hmv
      rw [sub_add_cancel] at hh
      have hk := kernel_le hνm hν.1 ht.1 ht.2 (γ := 1 / 2) (by norm_num)
      have hB' : hsNorm (j - 1) (ρc v) ≤ B := by simpa using hB 0 ⟨le_rfl, zero_le_one⟩
      have hdat : hsNorm j (fun k => (heatMult (ν * t) k : ℂ) * ρc v k) ≤
          A * t ^ (-(1 / 2 : ℝ)) := by
        refine hh.trans ?_
        calc Ch * (1 + (ν * t) ^ (-(1 / 2 : ℝ))) * hsNorm (j - 1) (ρc v)
            ≤ Ch * ((1 + νm ^ (-(1 / 2 : ℝ))) * t ^ (-(1 / 2 : ℝ))) * B := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hk hCh0) hB' (hsNorm_nonneg' _ _) ?_
              exact mul_nonneg hCh0 (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1.le _))
          _ = A * t ^ (-(1 / 2 : ℝ)) := by rw [hA]; ring
      linarith)
  calc hsNorm j (ρc (v + 1)) ≤ C' * A := key
    _ = C' * (Ch * (1 + νm ^ (-(1 / 2 : ℝ)))) * B := by rw [hA]; ring

/-- `V`-uniform version of `HRS.PDE.MFApriori.exists_short_time_bound` (`MeanFieldAprioriSobolev.lean:388`). -/
theorem exists_short_time_bound_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (Λ : ℝ) (Bv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V → Torus.cbNorm (K + 2) V ≤ Bv →
      ∀ ν ∈ Set.Icc νm νp, ∀ (ρ₀ : Torus d → ℝ) (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ v, 0 ≤ v → ∀ t ∈ Set.Icc 0 1, v + t ≤ T →
        hsNorm K (ρc (v + t)) ≤ C * hsNorm K (ρc v) := by
  obtain ⟨hb, hb1', hb0⟩ := bExp_spec (d := d) s hsd
  set γ : ℝ := (1 + bExp d s) / 2 with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ < 1 := by rw [hγ]; linarith
  have hK1 : (1 : ℝ) ≤ K := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  obtain ⟨C2, hC20, hC2⟩ := duhamel_core_unifV hd s hs0 hsd K hK νm νp hνm Λ K hK1 le_rfl Bv
  obtain ⟨C', hC'0, hC'⟩ := gronwall_Ioc γ C2 hγ0 hγ1 hC20
  obtain ⟨Ch, hCh0, hCh⟩ := exists_heat_smoothing (d := d) (K : ℝ) 0 le_rfl (by norm_num)
  refine ⟨max (C' * (Ch * 2)) 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro V hV hVB ν hν ρ₀ T ρc H hΛ v hv t ht hvt
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hCge : 1 ≤ max (C' * (Ch * 2)) 1 := le_max_right _ _
  rcases ht.1.eq_or_lt with h0 | hτ0
  · rw [← h0, add_zero]
    nlinarith [hsNorm_nonneg' (K : ℝ) (ρc v)]
  set τ : ℝ := t with hτ
  have hτ1 : τ ≤ 1 := ht.2
  have hmemT : ∀ σ ∈ Set.Icc (0 : ℝ) τ, v + σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨add_nonneg hv hσ.1, by linarith [hσ.2]⟩
  have hmv : MemHs (K : ℝ) (ρc v) := H.sol.cont.1 v ⟨hv, by linarith⟩
  set A : ℝ := Ch * 2 * hsNorm K (ρc v) with hA
  have hA0 : 0 ≤ A := by have := hsNorm_nonneg' (K : ℝ) (ρc v); positivity
  set ψ : ℝ → ℝ := fun σ => hsNorm K (ρc (v + σ)) with hψ
  have hψnn : ∀ σ ∈ Set.Icc (0 : ℝ) τ, 0 ≤ ψ σ := fun σ _ => hsNorm_nonneg' _ _
  have hE : ∀ r ∈ Set.Ioc (0 : ℝ) τ, ψ r ≤ A + C2 * ∫ q in (0 : ℝ)..r, (r - q) ^ (-γ) * ψ q := by
    intro r hr
    have hcore := hC2 V hV hVB ν hν ρ₀ T ρc H hΛ v hv r hr.1 (hr.2.trans hτ1) (by linarith [hr.2])
    obtain ⟨-, hh⟩ := hCh ν r hν0 hr.1 (ρc v) hmv
    rw [add_zero] at hh
    simp only [zero_div, neg_zero, Real.rpow_zero] at hh
    have : hsNorm K (fun k => (heatMult (ν * r) k : ℂ) * ρc v k) ≤ A := by
      refine hh.trans (le_of_eq ?_)
      rw [hA]; ring
    show hsNorm K (ρc (v + r)) ≤ _
    linarith
  have hS := rescale_step_le γ C2 hγ1 hC20 ψ A (lt_of_lt_of_le hτ0 le_rfl) hτ1 hψnn hE
  have hcontK : ContinuousOn (fun σ => hsNorm K (ρc σ)) (Set.Icc 0 T) :=
    continuousOn_hsNorm_path H.sol.cont
  have hφc : ContinuousOn (fun u => ψ (τ * u)) (Set.Icc 0 1) := by
    refine hcontK.comp (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) ?_
    intro u hu
    exact hmemT _ ⟨mul_nonneg hτ0.le hu.1, by nlinarith [hu.2]⟩
  obtain ⟨Bφ, hBφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφc
  have key := hC' (fun u => ψ (τ * u)) A Bφ hA0 hφc
    (fun u hu => ⟨hsNorm_nonneg' _ _, (le_abs_self _).trans (by simpa using hBφ u hu)⟩)
    (fun u hu => hS u hu) 1 ⟨one_pos, le_rfl⟩
  have hfin : hsNorm K (ρc (v + τ)) ≤ C' * A := by
    have : ψ (τ * 1) = hsNorm K (ρc (v + τ)) := by simp [hψ]
    simpa [this] using key
  calc hsNorm K (ρc (v + t)) ≤ C' * A := hfin
    _ = (C' * (Ch * 2)) * hsNorm K (ρc v) := by rw [hA]; ring
    _ ≤ max (C' * (Ch * 2)) 1 * hsNorm K (ρc v) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hsNorm_nonneg' _ _)

/-- `V`-uniform version of `HRS.PDE.MFApriori.exists_hK_bound` (`MeanFieldAprioriSobolev.lean:451`):
the constant `C` is chosen before `V` (`Bv` fixed before `∃ C`). -/
theorem exists_hK_bound_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (ρ₀ : Torus d → ℝ) (hρ₀H : MemSobolev K ρ₀) (Λ : ℝ) (Bv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V → Torus.cbNorm (K + 2) V ≤ Bv →
      ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ t ∈ Set.Icc 0 T, hsNorm K (ρc t) ≤ C := by
  have hKd : (d : ℝ) / 2 < K := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  -- Phase 1: large times, by induction on the regularity index
  have phase1 : ∀ n : ℕ, n ≤ K → ∃ B : ℝ, ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V →
      Torus.cbNorm (K + 2) V ≤ Bv → ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ t ∈ Set.Icc 0 T, (n : ℝ) ≤ t → hsNorm (n : ℝ) (ρc t) ≤ B := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨Λ, fun V _ _ ν _ T ρc H hΛ t ht _ => ?_⟩
      have h := hsNorm_zero_coeffOf_le (mfPath ρc t) (H.continuous_mfPath hKd ht) Λ (hΛ t ht)
      rw [H.coeffOf_mfPath hKd ht] at h
      simpa using h
    | succ n ih =>
      intro hn
      obtain ⟨Bn, hBn⟩ := ih (by omega)
      obtain ⟨C, hC0, hC⟩ := exists_volterra_step_unifV hd s hs0 hsd K hK νm νp hνm hνν Λ
        ((n + 1 : ℕ) : ℝ) (by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        (by exact_mod_cast hn) Bv
      refine ⟨C * Bn, fun V hV hVB ν hν T ρc H hΛ t ht htn => ?_⟩
      have hn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hn1] at htn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hv : 0 ≤ t - 1 := by linarith
      have hvT : t - 1 + 1 ≤ T := by linarith [ht.2]
      have := hC V hV hVB ν hν ρ₀ T ρc H hΛ (t - 1) hv hvT Bn (fun r hr => by
        have hmem : t - 1 + r ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hr.1], by linarith [hr.2, ht.2]⟩
        have := hBn V hV hVB ν hν T ρc H hΛ (t - 1 + r) hmem (by linarith [hr.1])
        rwa [show ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) by rw [hn1]; ring])
      rw [sub_add_cancel] at this
      exact this
  obtain ⟨BK, hBK⟩ := phase1 K le_rfl
  -- Phase 2: bounded times, by iterating the short-time bound
  obtain ⟨Cs, hCs0, hCs⟩ := exists_short_time_bound_unifV hd s hs0 hsd K hK νm νp hνm hνν Λ Bv
  set Cs' : ℝ := max Cs 1 with hCs'
  have hCs'1 : 1 ≤ Cs' := le_max_right _ _
  have phase2 : ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V → Torus.cbNorm (K + 2) V ≤ Bv →
      ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ m : ℕ, ∀ t ∈ Set.Icc 0 T, t ≤ m → hsNorm K (ρc t) ≤ Cs' ^ (m + 1) * hsNorm K (ρc 0) := by
    intro V hV hVB ν hν T ρc H hΛ m
    have h0 := hsNorm_nonneg' (K : ℝ) (ρc 0)
    induction m with
    | zero =>
      intro t ht htm
      have : t = 0 := le_antisymm (by simpa using htm) ht.1
      subst this
      simpa using mul_le_mul_of_nonneg_right hCs'1 h0
    | succ m ih =>
      intro t ht htm
      have hpow : Cs' ≤ Cs' ^ (m + 1 + 1) := by
        calc Cs' = Cs' ^ 1 := (pow_one _).symm
          _ ≤ Cs' ^ (m + 1 + 1) := pow_le_pow_right₀ hCs'1 (by omega)
      by_cases ht1 : t ≤ 1
      · have := hCs V hV hVB ν hν ρ₀ T ρc H hΛ 0 le_rfl t ⟨ht.1, ht1⟩ (by simpa using ht.2)
        rw [zero_add] at this
        calc hsNorm K (ρc t) ≤ Cs * hsNorm K (ρc 0) := this
          _ ≤ Cs' * hsNorm K (ρc 0) := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
          _ ≤ Cs' ^ (m + 1 + 1) * hsNorm K (ρc 0) := mul_le_mul_of_nonneg_right hpow h0
      · replace ht1 := not_le.mp ht1
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hv : t - 1 ∈ Set.Icc (0 : ℝ) T := ⟨by linarith, by linarith [ht.2]⟩
        have h1 := ih (t - 1) hv (by push_cast at htm; linarith)
        have h2 := hCs V hV hVB ν hν ρ₀ T ρc H hΛ (t - 1) hv.1 1 ⟨zero_le_one, le_rfl⟩
          (by linarith [ht.2])
        rw [sub_add_cancel] at h2
        calc hsNorm K (ρc t) ≤ Cs * hsNorm K (ρc (t - 1)) := h2
          _ ≤ Cs' * (Cs' ^ (m + 1) * hsNorm K (ρc 0)) :=
              mul_le_mul (le_max_left _ _) h1 (hsNorm_nonneg' _ _) (by linarith)
          _ = Cs' ^ (m + 1 + 1) * hsNorm K (ρc 0) := by ring
  refine ⟨max BK (Cs' ^ (K + 1) * hsNorm K (coeffOf ρ₀)), ?_, ?_⟩
  · exact le_trans (mul_nonneg (pow_nonneg (by linarith) _) (hsNorm_nonneg' _ _)) (le_max_right _ _)
  intro V hV hVB ν hν T ρc H hΛ t ht
  by_cases htK : (K : ℝ) ≤ t
  · exact (hBK V hV hVB ν hν T ρc H hΛ t ht htK).trans (le_max_left _ _)
  · replace htK := not_le.mp htK
    have := phase2 V hV hVB ν hν T ρc H hΛ K t ht htK.le
    rw [H.sol.init] at this
    exact this.trans (le_max_right _ _)

end HRS.ME.EVU
