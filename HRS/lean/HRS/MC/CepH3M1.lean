import HRS.MC.CepH3L1

/-!
# Packet CEPH3, part M1: assembly of part (b), lower semicontinuity of the integrated Fisher information
-/


open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {J : ℝ → Ch N → Ch N} {Φn : ℝ → Ch N → ℝ} {Ψ : Ch N → ℝ} {L : ℝ≥0}

lemma h3m_cont_integral [IsProbabilityMeasure P] {X : ℝ → Ω → Ch N} (hX : ∀ r, AEMeasurable (X r) P)
    (hXc : ∀ ω, Continuous fun r => X r ω) {F : Ch N → ℝ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ x, |F x| ≤ C) : Continuous fun r => ∫ ω, F (X r ω) ∂P := by
  refine continuous_of_dominated (bound := fun _ => C) (fun r => ?_) (fun r => Eventually.of_forall fun ω => ?_)
    (integrable_const C) (Eventually.of_forall fun ω => hF.comp (hXc ω))
  · exact hF.aestronglyMeasurable.comp_aemeasurable (hX r)
  · simpa using hC _

lemma h3m_iSup_ofReal (x : ℝ) : ⨆ m : ℕ, ENNReal.ofReal (x - 1 / ((m : ℝ) + 1)) = ENNReal.ofReal x := by
  have hmono : Monotone fun m : ℕ => ENNReal.ofReal (x - 1 / ((m : ℝ) + 1)) := by
    intro m m' hmm
    refine ENNReal.ofReal_le_ofReal ?_
    have : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm 1)
    linarith
  have h1 := tendsto_atTop_iSup hmono
  have h2 : Tendsto (fun m : ℕ => ENNReal.ofReal (x - 1 / ((m : ℝ) + 1))) atTop (𝓝 (ENNReal.ofReal x)) := by
    have : Tendsto (fun m : ℕ => x - 1 / ((m : ℝ) + 1)) atTop (𝓝 (x - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at this
    exact (ENNReal.continuous_ofReal.tendsto x).comp this
  exact tendsto_nhds_unique h1 h2

lemma h3m_fisher_int [NeZero N] [IsProbabilityMeasure P] {D : DynData 1} (σ₀ : Equiv.Perm (Fin N))
    (hΨ : ContDiff ℝ 1 Ψ)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = h3i_za σ₀ ζ w) {Zr : Ω → Ch N}
    (hZr : AEMeasurable Zr P) (hA : ∀ᵐ ω ∂P, Zr ω ∈ closure (cep_Alcove N)) :
    ∫ X, h3j_Fint D ζ X ∂(P.map fun ω => h3d_Q σ₀ (Zr ω)) = ∫ ω, h3k_Finf D.invβ Ψ σ₀ ζ δ (Zr ω) ∂P := by
  have hQ : AEMeasurable (fun ω => h3d_Q σ₀ (Zr ω)) P := (h3d_Q_measurable σ₀).comp_aemeasurable hZr
  rw [integral_map hQ (h3j_Fint_measurable D hζ).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hA] with ω hω
  exact h3k_Fint_Q σ₀ hΨ hΨtot hζ hδ hev hω

lemma h3m_fisherInfo_eq [NeZero N] [IsProbabilityMeasure P] {D : DynData 1} (σ₀ : Equiv.Perm (Fin N))
    (hΨ : ContDiff ℝ 1 Ψ)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {δ : {ζ : Config 1 N → (Fin N → Euc 1) // IsFisherTestField ζ} → ℝ} (hδ : ∀ ζ, 0 < δ ζ)
    (hev : ∀ ζ, ∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ.1 (δ ζ) w = h3i_za σ₀ ζ.1 w) {Zr : Ω → Ch N}
    (hZr : AEMeasurable Zr P) (hA : ∀ᵐ ω ∂P, Zr ω ∈ closure (cep_Alcove N)) :
    fisherInfo D N (P.map fun ω => h3d_Q σ₀ (Zr ω)) =
      ⨆ ζ : {ζ : Config 1 N → (Fin N → Euc 1) // IsFisherTestField ζ},
        ENNReal.ofReal (∫ ω, h3k_Finf D.invβ Ψ σ₀ ζ.1 (δ ζ) (Zr ω) ∂P) := by
  rw [h3j_fisher_eq, iSup_subtype']
  refine iSup_congr fun ζ => ?_
  rw [h3m_fisher_int σ₀ hΨ hΨtot ζ.2 (hδ ζ) (hev ζ) hZr hA]

/-- **(b)** at the level of a fixed time horizon, in terms of the pushed-forward laws. -/
theorem h3m_fisher_liminf [NeZero N] [IsProbabilityMeasure P] {D : DynData 1} (h : H3 N D.invβ J Φn Ψ L)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    (σ₀ : Equiv.Perm (Fin N)) {Z : ℕ → ℝ → Ω → Ch N} {Zl : ℝ → Ω → Ch N}
    (hZc : ∀ n, 1 ≤ n → ∀ ω, Continuous fun s => Z n s ω)
    (hZm : ∀ n, 1 ≤ n → ∀ s, 0 ≤ s → Measurable (Z n s))
    (hZlc : ∀ ω, Continuous fun s => Zl s ω)
    (hZlA : ∀ᵐ ω ∂P, ∀ s, 0 ≤ s → Zl s ω ∈ closure (cep_Alcove N))
    (hconv : ∀ s, 0 ≤ s → ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω | ε ≤ ‖Z n s ω - Zl s ω‖}) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ r in Icc (0 : ℝ) t, fisherInfo D N (P.map fun ω => h3d_Q σ₀ (Zl r ω)) ≤
      liminf (fun n : ℕ => ∫⁻ r in Icc (0 : ℝ) t, cep_cylFisher D.invβ (fun w => Φn n w + Ψ w)
        (P.map fun ω => cep_reduce (Z n r ω))) atTop := by
  classical
  have hZlm : ∀ s, 0 ≤ s → AEMeasurable (Zl s) P := fun s hs =>
    h3f_aemeasurable (fun n hn => hZm n hn s hs) (hconv s hs)
  have hδex : ∀ ζ : {ζ : Config 1 N → (Fin N → Euc 1) // IsFisherTestField ζ},
      ∃ δ > 0, ∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ.1 δ w = h3i_za σ₀ ζ.1 w :=
    fun ζ => h3j_zt_eventually_eq σ₀ ζ.2
  choose δ hδpos hδev using hδex
  set Fz : {ζ : Config 1 N → (Fin N → Euc 1) // IsFisherTestField ζ} → Ch N → ℝ :=
    fun ζ => h3k_Finf D.invβ Ψ σ₀ ζ.1 (δ ζ) with hFz
  have hFc : ∀ ζ, Continuous (Fz ζ) := fun ζ => h3k_Finf_continuous σ₀ h.hΨ h.hΨL ζ.2 (hδpos ζ)
  have hFb : ∀ ζ, ∃ B, ∀ z, |Fz ζ z| ≤ B := fun ζ => h3k_Finf_bdd σ₀ h.hΨ h.hΨL hΨtot ζ.2 (hδpos ζ) (hδev ζ)
  choose B hB using hFb
  let ι := {ζ : Config 1 N → (Fin N → Euc 1) // IsFisherTestField ζ} × ℕ
  let a : ι → ℝ → ℝ≥0∞ := fun i r =>
    ENNReal.ofReal (∫ ω, Fz i.1 (Zl (max r 0) ω) ∂P - 1 / ((i.2 : ℝ) + 1))
  let A : ι → ℕ → ℝ → ℝ≥0∞ := fun i n r =>
    if 1 ≤ n then ENNReal.ofReal (∫ ω, Fz i.1 (Z n (max r 0) ω) ∂P - 1 / ((i.2 : ℝ) + 1)) else 0
  let c : ℕ → ℝ → ℝ≥0∞ := fun n r => cep_cylFisher D.invβ (fun w => Φn n w + Ψ w)
    (P.map fun ω => cep_reduce (Z n r ω))
  have hac : ∀ i, Continuous (a i) := by
    intro i
    have := h3m_cont_integral (P := P) (X := fun r => Zl (max r 0)) (fun r => hZlm _ (le_max_right _ _))
      (fun ω => (hZlc ω).comp (continuous_id.max continuous_const)) (hFc i.1) (hB i.1)
    exact ENNReal.continuous_ofReal.comp (this.sub continuous_const)
  have hAm : ∀ i n, Measurable (A i n) := by
    intro i n
    by_cases hn : 1 ≤ n
    · simp only [A, if_pos hn]
      have := h3m_cont_integral (P := P) (X := fun r => Z n (max r 0)) (fun r => (hZm n hn _ (le_max_right _ _)).aemeasurable)
        (fun ω => (hZc n hn ω).comp (continuous_id.max continuous_const)) (hFc i.1) (hB i.1)
      exact (ENNReal.continuous_ofReal.comp (this.sub continuous_const)).measurable
    · simp only [A, if_neg hn]; exact measurable_const
  have hAc : ∀ i, ∀ᶠ n in atTop, ∀ r ∈ Icc (0 : ℝ) t, A i n r ≤ c n r := by
    intro i
    have hε : (0 : ℝ) < 1 / ((i.2 : ℝ) + 1) := by positivity
    filter_upwards [h3k_cylFisher_lower h hΨtot i.1.2 (hδpos i.1) (hδev i.1) hε, eventually_ge_atTop 1]
      with n hn hn1 r hr
    simp only [A, if_pos hn1, c]
    rw [max_eq_left hr.1]
    have hZnr : Measurable (Z n r) := hZm n hn1 r hr.1
    have hred : Measurable (fun ω => cep_reduce (Z n r ω)) := h3d_reduce_measurable.comp hZnr
    haveI : IsProbabilityMeasure (P.map fun ω => cep_reduce (Z n r ω)) := h3h_isProb_map hred.aemeasurable
    have hcell : (P.map fun ω => cep_reduce (Z n r ω)) (cep_cell N)ᶜ = 0 := by
      rw [Measure.map_apply hred (h3e_cell_measurable.compl)]
      have : (fun ω => cep_reduce (Z n r ω)) ⁻¹' (cep_cell N)ᶜ = ∅ := by
        ext ω; simp [h3d_reduce_mem_cell]
      rw [this, measure_empty]
    have key := hn _ inferInstance hcell
    have hint : ∫ z, Fz i.1 z ∂(P.map fun ω => cep_reduce (Z n r ω)) = ∫ ω, Fz i.1 (Z n r ω) ∂P := by
      rw [integral_map hred.aemeasurable (hFc i.1).aestronglyMeasurable]
      exact integral_congr_ae (Eventually.of_forall fun ω => h3k_Finf_reduce σ₀ h.hΨ hΨtot i.1.2 (hδpos i.1) (hδev i.1) _)
    rw [hFz] at hint
    simp only [hFz] at key ⊢
    rw [hint] at key
    exact key
  have hlim : ∀ i, ∀ r ∈ Icc (0 : ℝ) t, a i r ≤ liminf (fun n => A i n r) atTop := by
    intro i r hr
    have hr0 : max r 0 = r := max_eq_left hr.1
    have hT : Tendsto (fun n : ℕ => ∫ ω, Fz i.1 (Z (n + 1) r ω) ∂P) atTop (𝓝 (∫ ω, Fz i.1 (Zl r ω) ∂P)) := by
      refine h3f_integral_tendsto (Zn := fun n => Z (n + 1) r) (fun n => hZm (n + 1) (by omega) r hr.1)
        (fun ε hε => (hconv r hr.1 ε hε).comp (tendsto_add_atTop_nat 1)) (hFc i.1) (hB i.1)
    have hT' : Tendsto (fun n : ℕ => ∫ ω, Fz i.1 (Z n r ω) ∂P) atTop (𝓝 (∫ ω, Fz i.1 (Zl r ω) ∂P)) :=
      (tendsto_add_atTop_iff_nat 1).mp hT
    have hT2 : Tendsto (fun n : ℕ => A i n r) atTop (𝓝 (a i r)) := by
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (∫ ω, Fz i.1 (Z n r ω) ∂P - 1 / ((i.2 : ℝ) + 1))) atTop
          (𝓝 (ENNReal.ofReal (∫ ω, Fz i.1 (Zl r ω) ∂P - 1 / ((i.2 : ℝ) + 1)))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hT'.sub_const _)
      refine (tendsto_congr' ?_).mp (by simpa only [a, hr0] using h1)
      filter_upwards [eventually_ge_atTop 1] with n hn
      simp only [A, if_pos hn, hr0]
    rw [hT2.liminf_eq]
  have hfi : ∀ r ∈ Icc (0 : ℝ) t, fisherInfo D N (P.map fun ω => h3d_Q σ₀ (Zl r ω)) = ⨆ i, a i r := by
    intro r hr
    have hr0 : max r 0 = r := max_eq_left hr.1
    rw [h3m_fisherInfo_eq σ₀ h.hΨ hΨtot hδpos hδev (hZlm r hr.1)
      (by filter_upwards [hZlA] with ω hω using hω r hr.1)]
    simp only [a, hr0]
    rw [iSup_prod]
    refine iSup_congr fun ζ => ?_
    exact (h3m_iSup_ofReal _).symm
  calc ∫⁻ r in Icc (0 : ℝ) t, fisherInfo D N (P.map fun ω => h3d_Q σ₀ (Zl r ω))
      = ∫⁻ r in Icc (0 : ℝ) t, ⨆ i, a i r := setLIntegral_congr_fun measurableSet_Icc hfi
    _ ≤ _ := h3l_assembly a A c t hac hAm hAc hlim

end
end HRS.MC.CepH3
