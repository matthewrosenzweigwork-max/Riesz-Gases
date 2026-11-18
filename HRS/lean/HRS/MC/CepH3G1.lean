import HRS.MC.CepH3E4

/-!
# Packet CEPH3, part G1: the Gibbs measure on the component, finiteness of `Z_G`
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

lemma h3g_stricto_iff (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) :
    cep_StrictlyOrdered σ₀ (cep_unrank σ₀ z) ↔ z ∈ cep_Alcove N := by
  unfold cep_StrictlyOrdered cep_Alcove
  simp [cep_unrank]

lemma h3g_toCh_unrank (σ₀ : Equiv.Perm (Fin N)) (z : Ch N) : cep_toCh σ₀ (cep_unrank σ₀ z) = z := by
  ext k
  simp [cep_toCh, cep_rank, cep_unrank]

lemma h3g_Q_notin_collision (σ₀ : Equiv.Perm (Fin N)) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    h3d_Q σ₀ z ∉ collisionSet 1 N := by
  rintro ⟨i, j, hij, h⟩
  have h0 := congrFun h 0
  rw [h3d_Q_apply, h3d_Q_apply] at h0
  obtain ⟨n, hn⟩ := (h3d_coe_eq_iff _ _).mp h0
  have hne : σ₀.symm i ≠ σ₀.symm j := fun e => hij (σ₀.symm.injective e)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have a1 := hz.1 _ _ hlt; have a2 := hz.2 (σ₀.symm i) (σ₀.symm j)
    have h1 : (n : ℝ) < 0 := by linarith
    have h2 : (-1 : ℝ) < n := by linarith [hz.2 (σ₀.symm j) (σ₀.symm i)]
    have : n < 0 := by exact_mod_cast h1
    have : -1 < n := by exact_mod_cast h2
    omega
  · have a1 := hz.1 _ _ hlt
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith [hz.2 (σ₀.symm j) (σ₀.symm i)]
    have : 0 < n := by exact_mod_cast h1
    have : n < 1 := by exact_mod_cast h2
    omega

theorem h3g_weight_eq {D : DynData 1} (σ₀ : Equiv.Perm (Fin N)) {Ψ : Ch N → ℝ}
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {z : Ch N} (hz : z ∈ cep_Alcove N) :
    gibbsWeight D (h3d_Q σ₀ z) = Real.exp (-(cep_chamberPot 1 N z + Ψ z) / D.invβ) := by
  unfold gibbsWeight
  rw [if_neg (h3g_Q_notin_collision σ₀ hz)]
  have := hΨtot σ₀ (cep_unrank σ₀ z) ((h3g_stricto_iff σ₀ z).mpr hz)
  rw [h3g_toCh_unrank] at this
  have e : totalPotential D (h3d_Q σ₀ z) = cep_chamberPot 1 N z + Ψ z := this
  rw [e]
  congr 1
  field_simp

lemma h3g_mk_rep (a : Torus 1) : Torus.mk (Torus.rep a) = a := by
  funext j
  unfold Torus.mk Torus.rep
  simp only
  have := (AddCircle.equivIco (1:ℝ) 0).symm_apply_apply (a j)
  rw [← this]
  simp

lemma h3g_sort (x : Config 1 N) (hx : x ∉ collisionSet 1 N) :
    ∃ π : Equiv.Perm (Fin N), cep_StrictlyOrdered π (fun i => Torus.rep (x i)) := by
  set y : Fin N → ℝ := fun i => Torus.rep (x i) 0 with hy
  have hyI : ∀ i, 0 ≤ y i ∧ y i < 1 := fun i => by
    have := (AddCircle.equivIco (1:ℝ) 0 (x i 0)).2
    simpa [hy, Torus.rep] using this
  have hinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    apply hx
    refine ⟨i, j, hne, ?_⟩
    funext t
    have t0 : t = 0 := Subsingleton.elim _ _
    subst t0
    have : AddCircle.equivIco (1:ℝ) 0 (x i 0) = AddCircle.equivIco (1:ℝ) 0 (x j 0) := Subtype.ext hij
    exact (AddCircle.equivIco (1:ℝ) 0).injective this
  refine ⟨Tuple.sort y, ?_, ?_⟩
  · intro k k' hkk'
    have hmono := Tuple.monotone_sort y
    have : StrictMono (y ∘ Tuple.sort y) := hmono.strictMono_of_injective (hinj.comp (Tuple.sort y).injective)
    exact this hkk'
  · intro k k'
    have := hyI (Tuple.sort y k'); have := hyI (Tuple.sort y k)
    show y (Tuple.sort y k') < y (Tuple.sort y k) + 1
    linarith

theorem h3g_partition_ne_top {D : DynData 1} (hβ : 0 < D.invβ) {Ψ : Ch N → ℝ} {L : ℝ≥0}
    (hΨ : ContDiff ℝ 1 Ψ) (hΨL : LipschitzWith L (gradient Ψ))
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y)) :
    gibbsPartition D N ≠ ⊤ := by
  classical
  set a : ℝ := ‖gradient Ψ 0‖ with ha
  set B : ℝ := (N : ℝ) * Real.log 2 + |Ψ 0| + a * Real.sqrt N + L * N with hB
  have hbound : ∀ X : Config 1 N, gibbsWeight D X ≤ Real.exp (B / D.invβ) := by
    intro X
    unfold gibbsWeight
    by_cases hX : X ∈ collisionSet 1 N
    · rw [if_pos hX]; exact (Real.exp_pos _).le
    · rw [if_neg hX]
      obtain ⟨π, hπ⟩ := h3g_sort X hX
      set y : Fin N → Euc 1 := fun i => Torus.rep (X i) with hy
      have hXy : X = fun i => Torus.mk (y i) := by funext i; exact (h3g_mk_rep (X i)).symm
      set z : Ch N := cep_toCh π y with hz
      have hzA : z ∈ cep_Alcove N := by
        refine ⟨fun k l hkl => hπ.1 k l hkl, fun k l => hπ.2 k l⟩
      have hU : totalPotential D X = cep_chamberPot 1 N z + Ψ z := by
        rw [hXy]; exact hΨtot π y hπ
      have hzn : ‖z‖ ≤ Real.sqrt N := by
        refine Real.le_sqrt_of_sq_le ?_
        rw [EuclideanSpace.norm_sq_eq]
        calc ∑ k, ‖z k‖ ^ 2 ≤ ∑ _k : Fin N, (1 : ℝ) := by
              refine Finset.sum_le_sum fun k _ => ?_
              have h1 : 0 ≤ y (π k) 0 := by simpa [hy, Torus.rep] using (AddCircle.equivIco (1:ℝ) 0 (X (π k) 0)).2.1
              have h2 : y (π k) 0 < 1 := by simpa [hy, Torus.rep] using (AddCircle.equivIco (1:ℝ) 0 (X (π k) 0)).2.2
              have : z k = y (π k) 0 := rfl
              rw [Real.norm_eq_abs, this, abs_of_nonneg h1]
              nlinarith
          _ = N := by simp
      have hΨb := h3e_Psi_bound hΨ hΨL z
      have hs : ‖z‖ ≤ Real.sqrt N := hzn
      have hΨlow : Ψ 0 - (a * Real.sqrt N + L * N) ≤ Ψ z := by
        have h1 := (abs_le.mp hΨb).1
        have h2 : a * ‖z‖ ≤ a * Real.sqrt N := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
        have h3 : (L : ℝ) * ‖z‖ ^ 2 ≤ L * N := by
          have : ‖z‖ ^ 2 ≤ (N : ℝ) := by
            calc ‖z‖ ^ 2 ≤ Real.sqrt N ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
              _ = N := Real.sq_sqrt (Nat.cast_nonneg N)
          exact mul_le_mul_of_nonneg_left this L.2
        linarith
      have hΦlow := h3a_pot_lower hzA
      have hlow : -B ≤ totalPotential D X := by
        rw [hU]
        have := neg_abs_le (Ψ 0)
        linarith
      refine Real.exp_le_exp.mpr ?_
      have : -(D.invβ⁻¹) * totalPotential D X ≤ D.invβ⁻¹ * B := by
        have := inv_pos.mpr hβ
        nlinarith
      calc -(D.invβ⁻¹) * totalPotential D X ≤ D.invβ⁻¹ * B := this
        _ = B / D.invβ := by ring
  unfold gibbsPartition
  refine (lt_of_le_of_lt (lintegral_mono fun X => ENNReal.ofReal_le_ofReal (hbound X)) ?_).ne
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

/-- The unnormalised Gibbs measure `G dX`. -/
def h3g_mG (D : DynData 1) : Measure (Config 1 N) :=
  volume.withDensity fun X => ENNReal.ofReal (gibbsWeight D X)

lemma h3g_entropy_eq (D : DynData 1) (μ : Measure (Config 1 N)) :
    gibbsEntropy D μ = h3c_F μ (h3g_mG D) := by
  have hu : (h3g_mG (N := N) D) univ = gibbsPartition D N := by
    unfold h3g_mG gibbsPartition
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold gibbsEntropy h3c_F relEntropy gibbsRef
  rw [hu]
  rfl

lemma h3g_E_measurable [NeZero N] : MeasurableSet (cep_cell N ∩ cep_Alcove N) :=
  h3e_cell_measurable.inter h3b_alcove_isOpen.measurableSet

lemma h3g_QE_measurable [NeZero N] (σ₀ : Equiv.Perm (Fin N)) :
    MeasurableSet (h3d_Q σ₀ '' (cep_cell N ∩ cep_Alcove N)) :=
  h3g_E_measurable.image_of_continuousOn_injOn (h3d_Q_continuous σ₀).continuousOn (h3d_Q_injOn σ₀)

theorem h3g_map_mE [NeZero N] {D : DynData 1} (hβ : 0 < D.invβ) (σ₀ : Equiv.Perm (Fin N)) {Ψ : Ch N → ℝ}
    (hΨm : Measurable Ψ)
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y)) :
    (h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w)).map (h3d_Q σ₀) =
      (h3g_mG D).restrict (h3d_Q σ₀ '' (cep_cell N ∩ cep_Alcove N)) := by
  classical
  set E := cep_cell N ∩ cep_Alcove N with hE
  set f : Config 1 N → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-(cep_chamberPot 1 N (h3d_g σ₀ x) + Ψ (h3d_g σ₀ x)) / D.invβ)) with hf
  have hfm : Measurable f := by
    have hg := h3d_g_measurable σ₀
    have h1 : Measurable (fun w : Ch N => cep_chamberPot 1 N w + Ψ w) := h3e_chamberPot_measurable.add hΨm
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp ((h1.comp hg).neg.div_const _))
  have hQE := h3g_QE_measurable σ₀
  have hA := h3b_alcove_isOpen (N := N).measurableSet
  -- pointwise identification on `E`
  have hpt : ∀ z ∈ E, (cep_cylWeight D.invβ (fun w => cep_chamberPot 1 N w + Ψ w) z) = f (h3d_Q σ₀ z) := by
    intro z hz
    simp only [hf, h3d_g_Q σ₀ hz]
    rfl
  have hptG : ∀ z ∈ E, f (h3d_Q σ₀ z) = ENNReal.ofReal (gibbsWeight D (h3d_Q σ₀ z)) := by
    intro z hz
    rw [h3g_weight_eq σ₀ hΨtot hz.2]
    simp only [hf, h3d_g_Q σ₀ hz]
  have s1 : h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w) =
      (volume.restrict E).withDensity (f ∘ h3d_Q σ₀) := by
    unfold h3e_mE
    rw [withDensity_indicator hA, Measure.restrict_restrict hA, inter_comm (cep_Alcove N) (cep_cell N)]
    refine withDensity_congr_ae ?_
    refine (ae_restrict_iff' h3g_E_measurable).mpr (Eventually.of_forall fun z hz => ?_)
    exact hpt z hz
  have s2 : (h3e_mE D.invβ (fun w => cep_chamberPot 1 N w + Ψ w)).map (h3d_Q σ₀) =
      (volume.restrict (h3d_Q σ₀ '' E)).withDensity f := by
    rw [s1, h3e_map_withDensity_comp (h3d_Q_measurable σ₀) hfm, h3d_pushforward σ₀ h3g_E_measurable
      (h3d_Q_injOn σ₀)]
  rw [s2]
  unfold h3g_mG
  rw [restrict_withDensity hQE]
  refine withDensity_congr_ae ?_
  refine (ae_restrict_iff' hQE).mpr (Eventually.of_forall fun x hx => ?_)
  obtain ⟨z, hz, rfl⟩ := hx
  exact hptG z hz
end
end HRS.MC.CepH3
