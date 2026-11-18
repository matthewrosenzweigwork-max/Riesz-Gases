import HRS.MC.CepH3J2

/-!
# Packet CEPH3, part J3: the Fisher integrand on `Config` equals the cut-off cylinder integrand on the closed alcove
-/


open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

lemma h3j_rep_measurable : Measurable (Torus.rep : Torus 1 → Euc 1) := by
  have h : Measurable (fun (x : Torus 1) (i : Fin 1) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

lemma h3j_mkvec_continuous : Continuous (fun Y : Fin N → Euc 1 => (fun i => Torus.mk (Y i) : Config 1 N)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun Y : Fin N → Euc 1 => ((Y i j : ℝ) : UnitAddCircle)
  exact (AddCircle.continuous_mk' 1).comp (by fun_prop)

lemma h3j_repvec_measurable : Measurable (fun X : Config 1 N => (fun i => Torus.rep (X i) : Fin N → Euc 1)) :=
  Measurable.of_eval fun i => h3j_rep_measurable.comp (measurable_pi_apply i)

lemma h3j_zeta_eq {ζ : Config 1 N → (Fin N → Euc 1)} (X : Config 1 N) :
    ζ X = ζ (fun i => Torus.mk (Torus.rep (X i))) := by
  simp only [Torus.mk_rep]

lemma h3j_Fint_measurable (D : DynData 1) {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) :
    Measurable (h3j_Fint D ζ) := by
  set L : (Fin N → Euc 1) → (Fin N → Euc 1) := fun Y => ζ (fun i => Torus.mk (Y i)) with hL
  have hLc : Continuous L := hζ.smooth.continuous
  have hLm : Measurable L := hLc.measurable
  set T : (Fin N → Euc 1) → ℝ := fun Z => totalPotential D (fun i => Torus.mk (Z i)) with hT
  set R := fun X : Config 1 N => (fun i => Torus.rep (X i) : Fin N → Euc 1) with hR
  have hRm : Measurable R := h3j_repvec_measurable
  have hdiv : Measurable (configDiv ζ : Config 1 N → ℝ) := by
    unfold configDiv
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (measurable_fderiv_apply_const ℝ _ _).comp hRm
  have hLX : ∀ X, ζ X = L (R X) := fun X => by simp only [hL, hR, Torus.mk_rep]
  have h2 : Measurable fun X : Config 1 N => fderiv ℝ T (R X) (ζ X) := by
    simp_rw [hLX]
    have hev : Continuous (fun p : ((Fin N → Euc 1) →L[ℝ] ℝ) × (Fin N → Euc 1) => p.1 p.2) :=
      isBoundedBilinearMap_apply.continuous
    exact (hev.measurable.comp (((measurable_fderiv ℝ T).comp hRm).prodMk (hLm.comp hRm)))
  have h3 : Measurable fun X : Config 1 N => ∑ i, ‖ζ X i‖ ^ 2 := by
    simp_rw [hLX]
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (((hLm.comp hRm).eval (a := i)).norm).pow_const 2
  unfold h3j_Fint
  exact ((hdiv.const_mul _).add (h2.const_mul _)).sub h3


lemma h3j_Fint_zero (D : DynData 1) {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ)
    {K : Set (Config 1 N)} (hKc : IsCompact K) (hK0 : ∀ X, X ∉ K → ζ X = 0) {X : Config 1 N} (hX : X ∉ K) :
    h3j_Fint D ζ X = 0 := by
  have hopen : IsOpen ((fun Y : Fin N → Euc 1 => (fun i => Torus.mk (Y i) : Config 1 N)) ⁻¹' Kᶜ) :=
    hKc.isClosed.isOpen_compl.preimage h3j_mkvec_continuous
  have hmem : (fun i => Torus.rep (X i) : Fin N → Euc 1) ∈
      ((fun Y : Fin N → Euc 1 => (fun i => Torus.mk (Y i) : Config 1 N)) ⁻¹' Kᶜ) := by
    show (fun i => Torus.mk (Torus.rep (X i))) ∉ K
    simpa only [Torus.mk_rep] using hX
  have hz : ∀ i j, (fun Z : Fin N → Euc 1 => (ζ (fun i => Torus.mk (Z i)) i) j) =ᶠ[𝓝 (fun i => Torus.rep (X i))]
      fun _ => 0 := by
    intro i j
    filter_upwards [hopen.mem_nhds hmem] with Z hZ
    simp [hK0 _ hZ]
  have hd : configDiv ζ X = 0 := by
    unfold configDiv
    simp only
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [(hz k.1 k.2).fderiv_eq]
    simp
  have hζX : ζ X = 0 := hK0 X hX
  unfold h3j_Fint
  rw [hd, hζX]
  simp

lemma h3j_Fch_zero (β : ℝ) (U : Ch N → ℝ) {ζt : Ch N → Ch N} {z : Ch N} (hev : ∀ᶠ w in 𝓝 z, ζt w = 0) :
    h3j_Fch β U ζt z = 0 := by
  have hz : ζt z = 0 := hev.self_of_nhds
  have hk : ∀ k : Fin N, fderiv ℝ (fun w => ζt w k) z = 0 := by
    intro k
    have : (fun w => ζt w k) =ᶠ[𝓝 z] fun _ => 0 := hev.mono fun w hw => by simp [hw]
    rw [this.fderiv_eq]; simp
  unfold h3j_Fch
  simp [hz, hk]

lemma h3j_closure_collision [NeZero N] (σ₀ : Equiv.Perm (Fin N)) {z : Ch N} (hz : z ∈ closure (cep_Alcove N))
    (hnz : z ∉ cep_Alcove N) : h3d_Q σ₀ z ∈ collisionSet 1 N := by
  have hcl : IsClosed {w : Ch N | (∀ k l : Fin N, k < l → w k ≤ w l) ∧ (∀ k l : Fin N, w l ≤ w k + 1)} := by
    have : {w : Ch N | (∀ k l : Fin N, k < l → w k ≤ w l) ∧ (∀ k l : Fin N, w l ≤ w k + 1)} =
        (⋂ k, ⋂ l, ⋂ (_ : k < l), {w : Ch N | w k ≤ w l}) ∩ (⋂ k, ⋂ l, {w : Ch N | w l ≤ w k + 1}) := by
      ext w; simp
    rw [this]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun k => isClosed_iInter fun l => isClosed_iInter fun _ =>
        isClosed_le (by fun_prop) (by fun_prop)
    · exact isClosed_iInter fun k => isClosed_iInter fun l => isClosed_le (by fun_prop) (by fun_prop)
  have hsub : cep_Alcove N ⊆ {w : Ch N | (∀ k l : Fin N, k < l → w k ≤ w l) ∧ (∀ k l : Fin N, w l ≤ w k + 1)} :=
    fun w hw => ⟨fun k l hkl => (hw.1 k l hkl).le, fun k l => (hw.2 k l).le⟩
  obtain ⟨h1, h2⟩ := closure_minimal hsub hcl hz
  have hnot : ¬ ((∀ k l : Fin N, k < l → z k < z l) ∧ (∀ k l : Fin N, z l < z k + 1)) := hnz
  rw [not_and_or] at hnot
  rcases hnot with h | h
  · push_neg at h
    obtain ⟨k, l, hkl, hle⟩ := h
    have heq : z l = z k := le_antisymm hle (h1 k l hkl)
    refine ⟨σ₀ k, σ₀ l, fun h => (ne_of_lt hkl) (σ₀.injective h), ?_⟩
    funext j
    have : h3d_Q σ₀ z (σ₀ k) j = h3d_Q σ₀ z (σ₀ l) j := by
      rw [h3d_Q_apply, h3d_Q_apply]
      simp [heq]
    exact this
  · push_neg at h
    obtain ⟨k, l, hle⟩ := h
    have heq : z l = z k + 1 := le_antisymm (h2 k l) hle
    have hkl : k ≠ l := by
      rintro rfl; linarith
    refine ⟨σ₀ k, σ₀ l, fun h => hkl (σ₀.injective h), ?_⟩
    funext j
    rw [h3d_Q_apply, h3d_Q_apply]
    simp only [Equiv.symm_apply_apply]
    exact (h3d_coe_eq_iff _ _).mpr ⟨-1, by rw [heq]; push_cast; ring⟩

lemma h3j_quad_eq [NeZero N] (σ₀ : Equiv.Perm (Fin N)) (ζ : Config 1 N → (Fin N → Euc 1)) (z : Ch N) :
    ∑ i, ‖ζ (h3d_Q σ₀ z) i‖ ^ 2 = ‖h3i_za σ₀ ζ z‖ ^ 2 := by
  rw [← Equiv.sum_comp σ₀, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  simp [h3i_za]

theorem h3j_Fint_Q [NeZero N] {D : DynData 1} (σ₀ : Equiv.Perm (Fin N)) {Ψ : Ch N → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {ζ : Config 1 N → (Fin N → Euc 1)} (hζ : IsFisherTestField ζ) {δ : ℝ} (hδ : 0 < δ)
    (hev : ∀ z ∈ cep_Alcove N, ∀ᶠ w in 𝓝 z, h3i_zt σ₀ ζ δ w = h3i_za σ₀ ζ w) {K : Set (Config 1 N)}
    (hKc : IsCompact K) (hKd : Disjoint K (collisionSet 1 N)) (hK0 : ∀ X, X ∉ K → ζ X = 0) {z : Ch N}
    (hz : z ∈ closure (cep_Alcove N)) :
    h3j_Fint D ζ (h3d_Q σ₀ z) =
      h3j_Fch D.invβ (fun w => cep_chamberPot 1 N w + Ψ w) (h3i_zt σ₀ ζ δ) z := by
  by_cases hzA : z ∈ cep_Alcove N
  · have hev' := hev z hzA
    have hzt : h3i_zt σ₀ ζ δ z = h3i_za σ₀ ζ z := hev'.self_of_nhds
    unfold h3j_Fint h3j_Fch
    rw [h3j_div_eq σ₀ hζ hev', h3j_DU_eq σ₀ hΨ hΨtot ζ hzA, h3j_quad_eq, hzt]
  · have hcoll := h3j_closure_collision σ₀ hz hzA
    have hnK : h3d_Q σ₀ z ∉ K := fun h => Set.disjoint_left.mp hKd h hcoll
    rw [h3j_Fint_zero D hζ hKc hK0 hnK, h3j_Fch_zero _ _ (h3i_zt_eventually_zero hδ hzA)]

end
end HRS.MC.CepH3
