import HRS.MC.QRVocab
import HRS.MC.QRPChaos
import HRS.MC.QRPChaosAux5

/-!
# Packet CHAOS-LP: `L^p` moments of Gaussian quadratic forms (limit form)

`qrs_chaos_lp_lim_proof` is the relocated proof of `HRS.MC.QRSpec.qrs_chaos_lp_lim` (statement copied
verbatim; the tie `example` is in `HRS/MC/QRPChaosLimTie.lean`).  Route: `qpc_section` (finite form for the
difference of two finite sections), an a.e. convergent subsequence of the `L²`-convergent sections
(`IsHalfWick`), and Fatou for `eLpNorm`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.QRSpec.Chaos

open HRS.Sec7 HRS.MC.QRPChaos

theorem qrs_chaos_lp_lim_proof : ∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (η : Ω → NegSobolev d r), HasFiniteGaussianCoeffs P η → ∀ K : ℝ, 0 ≤ K → ModeCovBound P η K →
      ∀ (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (Q : Ω → ℝ), IsHalfWick P η μ h Q → AEStronglyMeasurable Q P →
      (Summable fun q : NonzeroLattice d × NonzeroLattice d => wickCoeff μ h q.1 q.2 ^ 2) →
      ∀ F : Finset (NonzeroLattice d),
        eLpNorm (fun ω => Q ω - wickSection P η μ h F ω) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (C * K * Real.sqrt (tailHS (wickCoeff μ h) F)) := by
  intro p hp
  obtain ⟨C, hC0, hCfin⟩ := qrs_chaos_lp_fin_proof p hp
  refine ⟨C, hC0, ?_⟩
  intro d r Ω _ P _ η hη K hK0 hK μ h Q hQ hQm hHS F
  set a : NonzeroLattice d → NonzeroLattice d → ℝ := wickCoeff μ h with ha
  set c : NonzeroLattice d → Ω → ℝ := fun k ω => NegSobolev.fourierCoeff (η ω) k with hcdef
  have hcm : ∀ k, AEMeasurable (c k) P := fun k =>
    ((hη {k}).1.eval (⟨k, Finset.mem_singleton_self k⟩ : ({k} : Finset (NonzeroLattice d)))).aemeasurable
  -- sequence of finite sets
  obtain ⟨S, hS⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset (NonzeroLattice d)))
  set u : ℕ → Finset (NonzeroLattice d) := fun n => S n ∪ F with hu
  have hu_tend : Tendsto u atTop atTop :=
    tendsto_atTop_mono (fun n => Finset.subset_union_left) hS
  have hFu : ∀ n, F ⊆ u n := fun n => Finset.subset_union_right
  set sec : Finset (NonzeroLattice d) → Ω → ℝ := wickSection P η μ h with hsec
  have hsecm : ∀ T, AEStronglyMeasurable (sec T) P := by
    intro T
    show AEStronglyMeasurable (fun ω => (1 / 2 : ℝ) * ∑ k ∈ T, ∑ l ∈ T,
      a k l * (c k ω * c l ω - ∫ ω', c k ω' * c l ω' ∂P)) P
    refine AEMeasurable.aestronglyMeasurable ?_
    have hcm' : ∀ k, AEMeasurable (c k) P := hcm
    fun_prop
  -- L² convergence
  have hL2 : Tendsto (fun n => ∫⁻ ω, ‖Q ω - sec (u n) ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := hQ.comp hu_tend
  have hE : Tendsto (fun n => eLpNorm (fun ω => sec (u n) ω - Q ω) 2 P) atTop (𝓝 0) := by
    have h1 : ∀ n, eLpNorm (fun ω => sec (u n) ω - Q ω) 2 P =
        (∫⁻ ω, ‖Q ω - sec (u n) ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
      intro n
      have hm : AEStronglyMeasurable (fun ω => sec (u n) ω - Q ω) P := (hsecm (u n)).sub hQm
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
      simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
      congr 1
      refine lintegral_congr fun ω => ?_
      rw [enorm_sub_rev]
    simp_rw [h1]
    have h0 : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [h0] at this
    exact this.comp hL2
  have hIM : TendstoInMeasure P (fun n => sec (u n)) atTop Q :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hE
  obtain ⟨ns, -, hae⟩ := hIM.exists_seq_tendsto_ae
  -- Fatou
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => sec (u (ns n)) ω - sec F ω) atTop
      (𝓝 (Q ω - sec F ω)) := by
    filter_upwards [hae] with ω hω
    exact (hω.sub_const _).congr fun n => rfl
  have hg : AEStronglyMeasurable (fun ω => Q ω - sec F ω) P := hQm.sub (hsecm F)
  have hfm : ∀ n, AEStronglyMeasurable (fun ω => sec (u (ns n)) ω - sec F ω) P :=
    fun n => (hsecm _).sub (hsecm F)
  have hfat := MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p) hfm
    (fun ω => Q ω - sec F ω) hg hlim
  have hnn : ∀ q, 0 ≤ qpcTail a F q := fun q => by
    unfold qpcTail; split_ifs
    · exact le_rfl
    · positivity
  have hsum : Summable (qpcTail a F) := Summable.of_nonneg_of_le hnn (fun q => by
    unfold qpcTail; split_ifs
    · positivity
    · exact le_rfl) hHS
  have htail : tailHS a F = ∑' q, qpcTail a F q := by
    unfold tailHS qpcTail
    refine tsum_congr fun q => ?_
    split_ifs <;> rfl
  have hb : ∀ n, eLpNorm (fun ω => sec (u (ns n)) ω - sec F ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (C * K * Real.sqrt (tailHS a F)) := by
    intro n
    refine (qpc_section P c (fun T => (hη T).1) (fun k => (hη ∅).2 k) hK0 (fun T b => hK T b)
      a F (u (ns n)) (hFu _) hC0.le (fun {ι} _ ξ hξ hc K hK hKop A =>
        hCfin P ξ hξ hc K hK hKop A)).trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
      (mul_nonneg hC0.le hK0))
    rw [htail]
    exact hsum.sum_le_tsum _ (fun q _ => hnn q)
  exact hfat.trans (liminf_le_of_frequently_le' (Filter.Eventually.frequently
    (Filter.Eventually.of_forall hb)))

end HRS.MC.QRSpec.Chaos

end
