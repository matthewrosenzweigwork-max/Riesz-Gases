import HRS.MC.CepH3J3

/-!
# Packet CEPH3, part K1: the limit chamber functional of a test field (continuity, periodicity, boundedness)
-/


open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

lemma h3k_gradU_eq {Ψ : Ch N → ℝ} (hΨ : ContDiff ℝ 1 Ψ) {w : Ch N} (hw : w ∈ cep_Alcove N) :
    gradient (fun w => cep_chamberPot 1 N w + Ψ w) w = h3a_gam w + gradient Ψ w := by
  have h1 := h3a_hasGradientAt hw
  have h2 : HasGradientAt Ψ (gradient Ψ w) w :=
    ((hΨ.differentiable (by norm_num)) w).hasGradientAt
  have h3 : HasGradientAt (fun w => cep_chamberPot 1 N w + Ψ w) (h3a_gam w + gradient Ψ w) w := by
    show HasFDerivAt _ (InnerProductSpace.toDual ℝ (Ch N) (h3a_gam w + gradient Ψ w)) w
    rw [map_add]
    exact h1.add h2
  exact h3.gradient

lemma h3k_gradU_continuousAt {Ψ : Ch N → ℝ} (hΨ : ContDiff ℝ 1 Ψ) {L : ℝ≥0} (hΨL : LipschitzWith L (gradient Ψ))
    {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ContinuousAt (gradient (fun w => cep_chamberPot 1 N w + Ψ w)) z := by
  have hc : ContinuousAt (fun w => h3a_gam w + gradient Ψ w) z :=
    ((h3a_gam_continuousOn.continuousAt (h3b_alcove_isOpen.mem_nhds hz))).add hΨL.continuous.continuousAt
  refine hc.congr ?_
  filter_upwards [h3b_alcove_isOpen.mem_nhds hz] with w hw
  exact (h3k_gradU_eq hΨ hw).symm

lemma h3k_zt_ev_zero {σ₀ : Equiv.Perm (Fin N)} {ζ : Config 1 N → (Fin N → Euc 1)} {δ : ℝ} (hδ : 0 < δ)
    {z : Ch N} (hz : z ∉ h3i_Ssup δ) : ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = 0 := by
  have hopen : IsOpen (h3i_Ssup (N := N) δ)ᶜ := (h3i_Ssup_closed δ).isOpen_compl
  filter_upwards [hopen.mem_nhds hz] with w hw
  have : h3i_chi δ w = 0 := by
    by_contra hne
    exact hw (h3i_chi_support hδ hne)
  unfold h3i_zt
  ext k
  simp [this]

theorem h3k_Finf_continuous [NeZero N] {β : ℝ} (σ₀ : Equiv.Perm (Fin N)) {Ψ : Ch N → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    {L : ℝ≥0} (hΨL : LipschitzWith L (gradient Ψ)) {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ)
    {δ : ℝ} (hδ : 0 < δ) :
    Continuous (h3j_Fch β (fun w => cep_chamberPot 1 N w + Ψ w) (h3i_zt σ₀ ζ δ)) := by
  have hzt := h3i_zt_contDiff σ₀ hζ.smooth δ
  have hk : ∀ k : Fin N, Continuous fun z => fderiv ℝ (fun w => h3i_zt σ₀ ζ δ w k) z (EuclideanSpace.single k 1) := by
    intro k
    have hd : ContDiff ℝ ∞ (fun w => h3i_zt σ₀ ζ δ w k) :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp hzt
    exact (hd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmid : Continuous fun z => inner ℝ (gradient (fun w => cep_chamberPot 1 N w + Ψ w) z) (h3i_zt σ₀ ζ δ z) := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hzA : z ∈ cep_Alcove N
    · exact (h3k_gradU_continuousAt hΨ hΨL hzA).inner hzt.continuous.continuousAt
    · have hev := h3i_zt_eventually_zero (σ₀ := σ₀) (ζ := ζ) hδ hzA
      refine (continuousAt_const (y := (0:ℝ))).congr ?_
      filter_upwards [hev] with w hw
      simp [hw]
  unfold h3j_Fch
  refine ((continuous_const.mul (continuous_finset_sum _ fun k _ => hk k)).add (continuous_const.mul hmid)).sub ?_
  exact (hzt.continuous.norm).pow 2

lemma h3k_alcove_reduce_iff [NeZero N] (z : Ch N) : cep_reduce z ∈ cep_Alcove N ↔ z ∈ cep_Alcove N := by
  have key : ∀ k, cep_reduce z k = z k - ⌊z 0⌋ := by
    intro k; simp [cep_reduce, cep_diag]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k l hkl => ?_, fun k l => ?_⟩
    · have := h1 k l hkl; rw [key, key] at this; linarith
    · have := h2 k l; rw [key, key] at this; linarith
  · exact h3d_reduce_mem_alcove

/-- The limit chamber functional of a test field. -/
def h3k_Finf (β : ℝ) (Ψ : Ch N → ℝ) (σ₀ : Equiv.Perm (Fin N)) (ζ : Config 1 N → (Fin N → Euc 1)) (δ : ℝ) :
    Ch N → ℝ :=
  h3j_Fch β (fun w => cep_chamberPot 1 N w + Ψ w) (h3i_zt σ₀ ζ δ)

theorem h3k_Fint_Q [NeZero N] {D : DynData 1} (σ₀ : Equiv.Perm (Fin N)) {Ψ : Ch N → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = h3i_za σ₀ ζ w) {z : Ch N}
    (hz : z ∈ closure (cep_Alcove N)) :
    h3j_Fint D ζ (h3d_Q σ₀ z) = h3k_Finf D.invβ Ψ σ₀ ζ δ z := by
  obtain ⟨K, hKc, hKd, hK0⟩ := hζ.support
  exact h3j_Fint_Q σ₀ hΨ hΨtot hζ hδ hev hKc hKd hK0 hz

theorem h3k_Finf_reduce [NeZero N] {D : DynData 1} (σ₀ : Equiv.Perm (Fin N)) {Ψ : Ch N → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = h3i_za σ₀ ζ w) (z : Ch N) :
    h3k_Finf D.invβ Ψ σ₀ ζ δ (cep_reduce z) = h3k_Finf D.invβ Ψ σ₀ ζ δ z := by
  by_cases hzA : z ∈ cep_Alcove N
  · rw [← h3k_Fint_Q σ₀ hΨ hΨtot hζ hδ hev (subset_closure ((h3k_alcove_reduce_iff z).mpr hzA)),
      ← h3k_Fint_Q σ₀ hΨ hΨtot hζ hδ hev (subset_closure hzA), h3d_Q_reduce]
  · have hr : cep_reduce z ∉ cep_Alcove N := fun h => hzA ((h3k_alcove_reduce_iff z).mp h)
    unfold h3k_Finf
    rw [h3j_Fch_zero _ _ (h3i_zt_eventually_zero hδ hzA), h3j_Fch_zero _ _ (h3i_zt_eventually_zero hδ hr)]

/-- A compact fundamental piece of the support of the cut-off. -/
def h3k_S0 [NeZero N] (δ : ℝ) : Set (Ch N) := h3i_Ssup δ ∩ {z | 0 ≤ z 0 ∧ z 0 ≤ 1}

lemma h3k_S0_compact [NeZero N] (δ : ℝ) (hδ : 0 < δ) : IsCompact (h3k_S0 (N := N) δ) := by
  have hcl : IsClosed (h3k_S0 (N := N) δ) := by
    refine (h3i_Ssup_closed δ).inter ?_
    have hc0 : Continuous fun z : Ch N => z 0 := by fun_prop
    exact (isClosed_le continuous_const hc0).inter (isClosed_le hc0 continuous_const)
  have hb : ∀ z ∈ h3k_S0 (N := N) δ, ∀ k, 0 ≤ z k ∧ z k ≤ 2 := by
    rintro z ⟨hS, h0, h1⟩ k
    by_cases hk : k = 0
    · subst hk; constructor <;> linarith
    · have hlt : (0 : Fin N) < k := Fin.pos_iff_ne_zero.mpr hk
      have := hS 0 k hlt
      constructor <;> linarith [this.1, this.2]
  have hbd : Bornology.IsBounded (h3k_S0 (N := N) δ) := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : Ch N)]
    refine ⟨2 * N + 1, fun z hz => ?_⟩
    rw [mem_closedBall_zero_iff]
    have hsq : ‖z‖ ^ 2 ≤ 4 * N := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ k, ‖z k‖ ^ 2 ≤ ∑ _k : Fin N, (4 : ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            have := hb z hz k
            rw [Real.norm_eq_abs, sq_abs]; nlinarith [this.1, this.2]
        _ = 4 * N := by simp [mul_comm]
    by_contra hlt
    push_neg at hlt
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    nlinarith
  exact Metric.isCompact_of_isClosed_isBounded hcl hbd

lemma h3k_S0_subset [NeZero N] {δ : ℝ} (hδ : 0 < δ) : h3k_S0 (N := N) δ ⊆ cep_Alcove N :=
  fun _ hz => h3i_Ssup_subset hδ hz.1

lemma h3k_zt_ne_zero_mem {σ₀ : Equiv.Perm (Fin N)} {ζ : Config 1 N → (Fin N → Euc 1)} {δ : ℝ} (hδ : 0 < δ)
    {z : Ch N} (hz : h3i_zt σ₀ ζ δ z ≠ 0) : z ∈ h3i_Ssup δ := by
  by_contra h
  have := (h3k_zt_ev_zero (σ₀ := σ₀) (ζ := ζ) hδ h).self_of_nhds
  exact hz this

theorem h3k_Finf_bdd [NeZero N] {D : DynData 1} (σ₀ : Equiv.Perm (Fin N)) {Ψ : Ch N → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    {L : ℝ≥0} (hΨL : LipschitzWith L (gradient Ψ))
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = h3i_za σ₀ ζ w) :
    ∃ B : ℝ, ∀ z, |h3k_Finf D.invβ Ψ σ₀ ζ δ z| ≤ B := by
  have hc : Continuous (h3k_Finf D.invβ Ψ σ₀ ζ δ) := h3k_Finf_continuous σ₀ hΨ hΨL hζ hδ
  obtain ⟨B, hB⟩ := (h3k_S0_compact δ hδ).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0, fun z => ?_⟩
  rw [← h3k_Finf_reduce σ₀ hΨ hΨtot hζ hδ hev z]
  set w := cep_reduce z with hw
  have hw0 := h3d_reduce_mem_cell z
  by_cases hS : w ∈ h3i_Ssup δ
  · have : w ∈ h3k_S0 (N := N) δ := ⟨hS, hw0.1, hw0.2.le⟩
    exact (hB w this).trans (le_max_left _ _)
  · have : h3k_Finf D.invβ Ψ σ₀ ζ δ w = 0 := h3j_Fch_zero _ _ (h3k_zt_ev_zero hδ hS)
    rw [this]; simp

end
end HRS.MC.CepH3
