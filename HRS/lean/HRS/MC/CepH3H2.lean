import HRS.MC.CepH3H1

/-!
# Packet CEPH3, part H2: assembly of part (c), initial entropies
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

lemma h3h_mE_ac [NeZero N] (β : ℝ) (U : Ch N → ℝ) :
    h3e_mE β U ≪ volume.restrict (cep_cell N ∩ cep_Alcove N) := by
  have hA := h3b_alcove_isOpen (N := N).measurableSet
  unfold h3e_mE
  rw [withDensity_indicator hA, Measure.restrict_restrict hA, inter_comm (cep_Alcove N) (cep_cell N)]
  exact withDensity_absolutelyContinuous _ _

lemma h3h_mE_compl [NeZero N] (β : ℝ) (U : Ch N → ℝ) :
    h3e_mE β U (cep_cell N ∩ cep_Alcove N)ᶜ = 0 := by
  refine h3h_mE_ac β U ?_
  rw [Measure.restrict_apply h3g_E_measurable.compl, compl_inter_self, measure_empty]

section Assembly
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {J : ℝ → Ch N → Ch N} {Φn : ℝ → Ch N → ℝ} {Ψ : Ch N → ℝ} {L : ℝ≥0}

lemma h3h_map_Q_reduce [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {z : Ω → Ch N} (hz : Measurable z) :
    (P.map fun ω => cep_reduce (z ω)).map (h3d_Q σ₀) = P.map fun ω => h3d_Q σ₀ (z ω) := by
  have hm : Measurable fun ω => cep_reduce (z ω) := h3d_reduce_measurable.comp hz
  rw [Measure.map_map (h3d_Q_measurable σ₀) hm]
  congr 1
  funext ω
  exact h3d_Q_reduce σ₀ (z ω)

/-- **(c)**: the initial regularised entropies are bounded by the limit entropy. -/
theorem h3h_initial_limsup [NeZero N] {D : DynData 1} (h : H3 N D.invβ J Φn Ψ L)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    (σ₀ : Equiv.Perm (Fin N)) {z₀ : Ω → Ch N} (hz₀m : Measurable z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    {Zl0 : Ω → Ch N} (hZl0 : ∀ᵐ ω ∂P, Zl0 ω = z₀ ω) :
    limsup (fun n : ℕ => cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w)
        (P.map fun ω => cep_reduce (z₀ ω))) atTop ≤
      gibbsEntropy D (P.map fun ω => h3d_Q σ₀ (Zl0 ω)) := by
  classical
  have hβ : 0 < D.invβ := h.hβ
  obtain ⟨n₀, K, hn₀, hK, hdom⟩ := h3e_dominated h.hJ h.hΦ h.hΦlim h.hΨ h.hΨL hβ
  have hQc := h3d_Q_continuous σ₀
  set E := cep_cell N ∩ cep_Alcove N with hE
  have hΦΨm : Measurable (fun w => cep_chamberPot 1 N w + Ψ w) :=
    h3e_chamberPot_measurable.add h.hΨ.continuous.measurable
  have hUc : ∀ n : ℕ, n₀ ≤ n → Continuous (fun w => Φn n w + Ψ w) := fun n hn =>
    h.U_cont (by exact_mod_cast hn₀.trans hn)
  have hmnfin : ∀ n, n₀ ≤ n → IsFiniteMeasure (h3e_mn D.invβ (fun w => Φn n w + Ψ w)) := fun n hn =>
    h3e_mn_finite hβ K (fun z hz => hdom n hn z hz)
  have hmE_le : ∀ n, n₀ ≤ n → h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w) ≤
      h3e_mn D.invβ (fun w => Φn n w + Ψ w) := fun n hn =>
    h3e_mE_le_mn hβ (fun z hz => add_le_add_left (h.hΦle n z (by exact_mod_cast hn₀.trans hn) hz) _)
  haveI hmEfin : IsFiniteMeasure (h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w)) :=
    haveI := hmnfin n₀ le_rfl
    isFiniteMeasure_of_le _ (hmE_le n₀ le_rfl)
  have hmEne := h3e_mE_ne_zero hΦΨm D.invβ
  haveI hνprob : IsProbabilityMeasure (P.map fun ω => cep_reduce (z₀ ω)) :=
    h3h_isProb_map (h3d_reduce_measurable.comp hz₀m).aemeasurable
  set ν := P.map fun ω => cep_reduce (z₀ ω) with hν
  have hνE : ν Eᶜ = 0 := by
    have hm : Measurable fun ω => cep_reduce (z₀ ω) := h3d_reduce_measurable.comp hz₀m
    rw [hν, Measure.map_apply hm h3g_E_measurable.compl]
    convert measure_empty (μ := P)
    ext ω
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact ⟨h3d_reduce_mem_cell _, h3d_reduce_mem_alcove (hz₀A ω)⟩
  have hGfin : IsFiniteMeasure (h3g_mG (N := N) D) :=
    ⟨by rw [h3g_mG_univ]; exact lt_top_iff_ne_top.mpr (h3g_partition_ne_top hβ h.hΨ h.hΨL hΨtot)⟩
  have hQE := h3g_QE_measurable σ₀
  have hmapE := h3g_map_mE hβ σ₀ h.hΨ.continuous.measurable hΨtot
  have hRne : ((h3g_mG (N := N) D).restrict (h3d_Q σ₀ '' E)) univ ≠ 0 := by
    rw [← hmapE, Measure.map_apply (h3d_Q_measurable σ₀) MeasurableSet.univ, preimage_univ]; exact hmEne
  have hlaw : ν.map (h3d_Q σ₀) = P.map fun ω => h3d_Q σ₀ (Zl0 ω) := by
    rw [hν, h3h_map_Q_reduce σ₀ hz₀m]
    refine Measure.map_congr ?_
    filter_upwards [hZl0] with ω hω using by rw [hω]
  have hνQ : (ν.map (h3d_Q σ₀)) (h3d_Q σ₀ '' E)ᶜ = 0 := by
    rw [Measure.map_apply (h3d_Q_measurable σ₀) hQE.compl]
    exact measure_mono_null (fun x hx => fun hxE => hx ⟨x, hxE, rfl⟩) hνE
  haveI : IsProbabilityMeasure (ν.map (h3d_Q σ₀)) := h3h_isProb_map (h3d_Q_measurable σ₀).aemeasurable
  have hfinal : ∀ n, n₀ ≤ n → cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w) ν ≤
      gibbsEntropy D (P.map fun ω => h3d_Q σ₀ (Zl0 ω)) := by
    intro n hn
    haveI := hmnfin n hn
    rw [h3e_cyl_eq_F]
    calc h3c_F ν (h3e_mn D.invβ (fun w => Φn n w + Ψ w))
        ≤ h3c_F ν (h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w)) :=
          h3c_F_mono _ _ _ (hmE_le n hn) hmEne
      _ = h3c_F (ν.map (h3d_Q σ₀)) ((h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w)).map (h3d_Q σ₀)) :=
          (h3c_F_map_eq _ _ (h3d_Q_measurable σ₀) (h3d_g_measurable σ₀) h3g_E_measurable
            (fun x hx => h3d_g_Q σ₀ hx) hνE (h3h_mE_compl _ _) hmEne).symm
      _ = h3c_F (ν.map (h3d_Q σ₀)) ((h3g_mG D).restrict (h3d_Q σ₀ '' E)) := by rw [hmapE]
      _ ≤ h3c_F (ν.map (h3d_Q σ₀)) (h3g_mG D) := h3c_F_restrict _ _ hQE hνQ hRne
      _ = gibbsEntropy D (P.map fun ω => h3d_Q σ₀ (Zl0 ω)) := by rw [← hlaw, h3g_entropy_eq]
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop n₀] with n hn
  exact hfinal n hn
end Assembly
end
end HRS.MC.CepH3
