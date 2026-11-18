import HRS.MC.CepH3F1

/-!
# Packet CEPH3, part H1: assembly of part (a), lower semicontinuity of the entropy
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

lemma h3d_reduce_measurable [NeZero N] : Measurable (cep_reduce : Ch N → Ch N) := by
  unfold cep_reduce
  have h1 : Measurable fun z : Ch N => ((⌊z 0⌋ : ℤ) : ℝ) :=
    (measurable_from_top (f := fun n : ℤ => (n : ℝ))).comp (Int.measurable_floor.comp (by fun_prop : Measurable fun z : Ch N => z 0))
  exact measurable_id.sub (h1.smul_const _)

lemma h3d_reduce_mem_cell [NeZero N] (z : Ch N) : cep_reduce z ∈ cep_cell N := by
  simp only [cep_cell, cep_reduce, cep_diag, mem_setOf_eq]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, mul_one]
  exact ⟨by linarith [Int.floor_le (z 0)], by linarith [Int.lt_floor_add_one (z 0)]⟩

lemma h3d_reduce_mem_alcove [NeZero N] {z : Ch N} (hz : z ∈ cep_Alcove N) : cep_reduce z ∈ cep_Alcove N := by
  refine ⟨fun k l hkl => ?_, fun k l => ?_⟩
  · simp only [cep_reduce, cep_diag, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, mul_one]
    linarith [hz.1 k l hkl]
  · simp only [cep_reduce, cep_diag, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, mul_one]
    linarith [hz.2 k l]

lemma h3g_mG_univ (D : DynData 1) : (h3g_mG (N := N) D) univ = gibbsPartition D N := by
  unfold h3g_mG gibbsPartition
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

lemma h3h_isProb_map {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → β} (hf : AEMeasurable f P) : IsProbabilityMeasure (P.map f) :=
  ⟨by rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ, preimage_univ, measure_univ]⟩

section Assembly
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {β : ℝ} {J : ℝ → Ch N → Ch N} {Φn : ℝ → Ch N → ℝ} {Ψ : Ch N → ℝ} {L : ℝ≥0}

/-- **(a)**: lower semicontinuity of the entropy at a fixed time. -/
theorem h3h_entropy_liminf [NeZero N] {D : DynData 1} (h : H3 N D.invβ J Φn Ψ L)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    (σ₀ : Equiv.Perm (Fin N))
    {Zn : ℕ → Ω → Ch N} {Zlt : Ω → Ch N} (hZm : ∀ n, 1 ≤ n → Measurable (Zn n)) (hZlm : AEMeasurable Zlt P)
    (hconv : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω | ε ≤ ‖Zn n ω - Zlt ω‖}) atTop (𝓝 0)) :
    gibbsEntropy D (P.map fun ω => h3d_Q σ₀ (Zlt ω)) ≤
      liminf (fun n : ℕ => cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w)
        (P.map fun ω => cep_reduce (Zn n ω))) atTop := by
  classical
  have hβ : 0 < D.invβ := h.hβ
  obtain ⟨n₀, K, hn₀, hK, hdom⟩ := h3e_dominated h.hJ h.hΦ h.hΦlim h.hΨ h.hΨL hβ
  have hQc := h3d_Q_continuous σ₀
  have hUc : ∀ n : ℕ, n₀ ≤ n → Continuous (fun w => Φn n w + Ψ w) := fun n hn =>
    h.U_cont (by exact_mod_cast hn₀.trans hn)
  have hmnfin : ∀ n, n₀ ≤ n → IsFiniteMeasure (h3e_mn D.invβ (fun w => Φn n w + Ψ w)) := fun n hn =>
    h3e_mn_finite hβ K (fun z hz => hdom n hn z hz)
  have hΦΨm : Measurable (fun w => cep_chamberPot 1 N w + Ψ w) :=
    h3e_chamberPot_measurable.add h.hΨ.continuous.measurable
  have hmE_le : ∀ n, n₀ ≤ n → h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w) ≤
      h3e_mn D.invβ (fun w => Φn n w + Ψ w) := fun n hn =>
    h3e_mE_le_mn hβ (fun z hz => add_le_add_left (h.hΦle n z (by exact_mod_cast hn₀.trans hn) hz) _)
  haveI hmEfin : IsFiniteMeasure (h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w)) :=
    haveI := hmnfin n₀ le_rfl
    isFiniteMeasure_of_le _ (hmE_le n₀ le_rfl)
  have hmEne := h3e_mE_ne_zero hΦΨm D.invβ
  set mC := (h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w)).map (h3d_Q σ₀) with hmC
  haveI : IsFiniteMeasure mC := Measure.isFiniteMeasure_map _ _
  have hmCne : mC univ ≠ 0 := by
    rw [hmC, Measure.map_apply hQc.measurable MeasurableSet.univ, preimage_univ]; exact hmEne
  have hμ : IsProbabilityMeasure (P.map fun ω => h3d_Q σ₀ (Zlt ω)) :=
    h3h_isProb_map (hQc.measurable.comp_aemeasurable hZlm)
  set U : ℕ → Ch N → ℝ := fun n w => Φn n w + Ψ w with hU
  set ν' : ℕ → Measure (Config 1 N) := fun k =>
    (P.map fun ω => cep_reduce (Zn (k + n₀) ω)).map (h3d_Q σ₀) with hν'
  set m' : ℕ → Measure (Config 1 N) := fun k => (h3e_mn D.invβ (U (k + n₀))).map (h3d_Q σ₀) with hm'
  have hZk : ∀ k, Measurable (Zn (k + n₀)) := fun k => hZm _ (hn₀.trans (Nat.le_add_left _ _))
  have hredprob : ∀ k, IsProbabilityMeasure (P.map fun ω => cep_reduce (Zn (k + n₀) ω)) := fun k =>
    h3h_isProb_map (h3d_reduce_measurable.comp (hZk k)).aemeasurable
  haveI : ∀ k, IsProbabilityMeasure (ν' k) := fun k =>
    h3h_isProb_map hQc.aemeasurable
  haveI hmnfin' : ∀ k, IsFiniteMeasure (h3e_mn D.invβ (U (k + n₀))) := fun k =>
    hmnfin _ (Nat.le_add_left _ _)
  haveI : ∀ k, IsFiniteMeasure (m' k) := fun k => Measure.isFiniteMeasure_map _ _
  have hν : ∀ φ : Config 1 N → ℝ, Continuous φ → Tendsto (fun k => ∫ x, φ x ∂(ν' k)) atTop
      (𝓝 (∫ x, φ x ∂(P.map fun ω => h3d_Q σ₀ (Zlt ω)))) := by
    intro φ hφ
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
    have e1 : ∀ k, ∫ x, φ x ∂(ν' k) = ∫ ω, φ (h3d_Q σ₀ (Zn (k + n₀) ω)) ∂P := by
      intro k
      rw [hν', integral_map hQc.aemeasurable hφ.aestronglyMeasurable,
        integral_map (φ := fun ω => cep_reduce (Zn (k + n₀) ω)) (h3d_reduce_measurable.comp (hZk k)).aemeasurable
          (f := fun x => φ (h3d_Q σ₀ x)) (hφ.comp hQc).aestronglyMeasurable]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [h3d_Q_reduce]
    simp_rw [e1]
    rw [integral_map (φ := fun ω => h3d_Q σ₀ (Zlt ω)) (hQc.measurable.comp_aemeasurable hZlm) hφ.aestronglyMeasurable]
    refine h3f_integral_tendsto (Zn := fun k => Zn (k + n₀)) hZk
      (fun ε hε => (hconv ε hε).comp (tendsto_add_atTop_nat n₀)) (hφ.comp hQc) (C := C) fun x => ?_
    simpa using hC _ (mem_univ _)
  have hm : ∀ φ : Config 1 N → ℝ, Continuous φ → Tendsto (fun k => ∫ x, φ x ∂(m' k)) atTop
      (𝓝 (∫ x, φ x ∂mC)) := fun φ hφ => (h3e_conv h σ₀ hφ).comp (tendsto_add_atTop_nat n₀)
  have key := h3c_F_liminf _ mC hmCne ν' m' hν hm
  have hGfin : IsFiniteMeasure (h3g_mG (N := N) D) :=
    ⟨by rw [h3g_mG_univ]; exact lt_top_iff_ne_top.mpr (h3g_partition_ne_top hβ h.hΨ h.hΨL hΨtot)⟩
  have step1 : gibbsEntropy D (P.map fun ω => h3d_Q σ₀ (Zlt ω)) ≤ h3c_F (P.map fun ω => h3d_Q σ₀ (Zlt ω)) mC := by
    rw [h3g_entropy_eq]
    have hle : mC ≤ h3g_mG D := by
      rw [hmC, h3g_map_mE hβ σ₀ h.hΨ.continuous.measurable hΨtot]
      exact Measure.restrict_le_self
    exact h3c_F_mono _ mC _ hle hmCne
  have step2 : ∀ k, h3c_F (ν' k) (m' k) ≤ cep_cylEntropy D.invβ (U (k + n₀))
      (P.map fun ω => cep_reduce (Zn (k + n₀) ω)) := by
    intro k
    rw [h3e_cyl_eq_F]
    exact h3c_F_map_le _ _ (h3e_mn_ne_zero (hUc _ (Nat.le_add_left _ _)).measurable D.invβ) hQc.measurable
  refine step1.trans (key.trans ?_)
  calc liminf (fun k => h3c_F (ν' k) (m' k)) atTop
      ≤ liminf (fun k => cep_cylEntropy D.invβ (U (k + n₀)) (P.map fun ω => cep_reduce (Zn (k + n₀) ω))) atTop :=
        liminf_le_liminf (Eventually.of_forall step2)
    _ = liminf (fun n : ℕ => cep_cylEntropy D.invβ (U n) (P.map fun ω => cep_reduce (Zn n ω))) atTop :=
        liminf_nat_add (fun n : ℕ => cep_cylEntropy D.invβ (U n) (P.map fun ω => cep_reduce (Zn n ω))) n₀
end Assembly
end
end HRS.MC.CepH3
