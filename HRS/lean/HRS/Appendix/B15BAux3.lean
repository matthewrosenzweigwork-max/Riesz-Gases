import HRS.Appendix.B15BAux1

/-!
# Packet B15-BP: proofs of the sorried B15-B statements (relocated copies)

Each frozen statement in `HRS/Appendix/B15BAux1.lean` is proved here as `<name>_proof` with the verbatim
statement, followed by an `example` checking that the statement matches the frozen one.
Helpers are prefixed `b15bp_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ## Target 1: `b15b_gibbsRef_tendsto_weak` -/

/-- Integral against a density `ofReal ∘ g` with `g ≥ 0` measurable. -/
theorem b15bp_integral_withDensity_ofReal {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : α → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (φ : α → ℝ) :
    ∫ x, φ x ∂(μ.withDensity fun x => ENNReal.ofReal (g x)) = ∫ x, g x * φ x ∂μ := by
  have hf : Measurable (fun x => ENNReal.ofReal (g x)) := ENNReal.measurable_ofReal.comp hg
  rw [integral_withDensity_eq_integral_toReal_smul hf
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ]
  have h : ∀ x, (ENNReal.ofReal (g x)).toReal = g x := fun x => ENNReal.toReal_ofReal (hg0 x)
  simp only [h, smul_eq_mul]

theorem b15bp_ofReal_norm_eq (x : ℝ) : ENNReal.ofReal ‖x‖ = ‖x‖ₑ := by
  rw [Real.norm_eq_abs, Real.enorm_eq_ofReal_abs]

theorem b15bp_gibbsWeight_nonneg (D : DynData d) (X : Config d N) : 0 ≤ gibbsWeight D X := by
  unfold gibbsWeight
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

/-- The normalised Gibbs density of the regularised reference measure `Q_{N,ε}` at level `M`. -/
def b15bp_dens (D : DynData d) (M : ℝ) (X : Config d N) : ℝ :=
  (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal⁻¹ *
    b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X

/-- The normalised Gibbs density of the reference measure `Q_N` (with the collision indicator). -/
def b15bp_dens0 (D : DynData d) (X : Config d N) : ℝ :=
  (gibbsPartition D N).toReal⁻¹ * gibbsWeight D X

theorem b15bp_gibbsRef_eq_withDensity (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) :
    gibbsRef D N = (volume : Measure (Config d N)).withDensity fun X =>
      ENNReal.ofReal (b15bp_dens0 D X) := by
  obtain ⟨hpos, hlt⟩ := b15_gibbsPartition_pos_lt_top (N := N) D hV hβ
  have hp : 0 < (gibbsPartition D N).toReal := ENNReal.toReal_pos hpos.ne' hlt.ne
  have hf : ∀ X : Config d N, ENNReal.ofReal (b15bp_dens0 D X) =
      (gibbsPartition D N)⁻¹ • ENNReal.ofReal (gibbsWeight D X) := by
    intro X
    unfold b15bp_dens0
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hp.le), ENNReal.ofReal_inv_of_pos hp,
      ENNReal.ofReal_toReal hlt.ne, smul_eq_mul]
  unfold gibbsRef
  simp only [hf]
  exact (withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hpos.ne')).symm

theorem b15bp_partitionGen_bounds (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℝ} (hM0 : 0 ≤ M) :
    b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) ≠ ⊤ ∧
      b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) ≠ 0 := by
  obtain ⟨hZpos, C, hZb⟩ := b15c_partition_bounds (N := N) D hβ hV
  have h := (hZb M hM0).1
  constructor
  · intro hT
    rw [hT, ENNReal.toReal_top] at h
    linarith
  · intro h0
    rw [h0, ENNReal.toReal_zero] at h
    linarith

theorem b15bp_dens_continuous (D : DynData d) (hV : Continuous D.V) (M : ℝ) :
    Continuous (b15bp_dens (N := N) D M) := by
  unfold b15bp_dens b15c_gibbsWeightGen
  exact continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul (b15c_potentialReg_continuous (N := N) D hV M)))

theorem b15bp_dens_nonneg (D : DynData d) (M : ℝ) (X : Config d N) : 0 ≤ b15bp_dens (N := N) D M X :=
  mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (Real.exp_pos _).le

theorem b15bp_dens0_nonneg (D : DynData d) (X : Config d N) : 0 ≤ b15bp_dens0 D X :=
  mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (b15bp_gibbsWeight_nonneg D X)

theorem b15bp_dens0_measurable (D : DynData d) (hV : Continuous D.V) :
    Measurable (b15bp_dens0 (N := N) D) :=
  measurable_const.mul (b15c_measurable_gibbsWeight (N := N) D hV)

theorem b15b_gibbsRef_tendsto_weak_proof (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {φ : Config d N → ℝ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ x, φ x ∂(b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n))))
      atTop (𝓝 (∫ x, φ x ∂(gibbsRef D N))) := by
  have hVc := b15_continuous_of_isCk hV
  have hZt : Tendsto (fun n => ∫⁻ X : Config d N,
      ENNReal.ofReal ‖b15bp_dens D (M n) X - b15bp_dens0 D X‖) atTop (𝓝 0) :=
    b15c_normDensity_tendsto_L1 (N := N) D hβ hV hM hM0
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hφ.continuousOn
  have e1 : ∀ n, ∫ x, φ x ∂(b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n)))
      = ∫ X, b15bp_dens D (M n) X * φ X := by
    intro n
    rw [b15c_gibbsRefGen_eq_withDensity D.invβ (b15c_potentialReg (N := N) D (M n))
      (b15bp_partitionGen_bounds D hβ hV (hM0 n)).1 (b15bp_partitionGen_bounds D hβ hV (hM0 n)).2]
    exact b15bp_integral_withDensity_ofReal _ _ (b15bp_dens_continuous D hVc (M n)).measurable
      (b15bp_dens_nonneg D (M n)) φ
  have e0 : ∫ x, φ x ∂(gibbsRef D N) = ∫ X, b15bp_dens0 D X * φ X := by
    rw [b15bp_gibbsRef_eq_withDensity D hβ hV]
    exact b15bp_integral_withDensity_ofReal _ _ (b15bp_dens0_measurable D hVc)
      (b15bp_dens0_nonneg D) φ
  have hFi : ∀ n, Integrable (fun X => b15bp_dens D (M n) X * φ X) := fun n =>
    ((b15bp_dens_continuous D hVc (M n)).mul hφ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmeas : AEStronglyMeasurable (fun X => b15bp_dens0 D X * φ X) (volume : Measure (Config d N)) :=
    ((b15bp_dens0_measurable D hVc).mul hφ.measurable).aestronglyMeasurable
  have hbound : ∀ (n : ℕ) (X : Config d N), ‖b15bp_dens D (M n) X * φ X - b15bp_dens0 D X * φ X‖ₑ ≤
      ENNReal.ofReal ‖b15bp_dens D (M n) X - b15bp_dens0 D X‖ * ENNReal.ofReal B := by
    intro n X
    rw [b15bp_ofReal_norm_eq, ← sub_mul, enorm_mul]
    have hφX : |φ X| ≤ B := by
      have := hB X (mem_univ _)
      rwa [Real.norm_eq_abs] at this
    have hφe : ‖φ X‖ₑ ≤ ENNReal.ofReal B := by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal hφX
    gcongr
  have hlin : ∀ n : ℕ, ∫⁻ X : Config d N, ‖b15bp_dens D (M n) X * φ X - b15bp_dens0 D X * φ X‖ₑ ≤
      (∫⁻ X : Config d N, ENNReal.ofReal ‖b15bp_dens D (M n) X - b15bp_dens0 D X‖) * ENNReal.ofReal B := by
    intro n
    rw [← lintegral_mul_const' (ENNReal.ofReal B) _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun X => hbound n X
  have hlim : Tendsto (fun n => ∫⁻ X : Config d N, ‖b15bp_dens D (M n) X * φ X - b15bp_dens0 D X * φ X‖ₑ)
      atTop (𝓝 0) := by
    have h2 := ENNReal.Tendsto.mul_const hZt (Or.inr (ENNReal.ofReal_ne_top (r := B)))
    rw [zero_mul] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => zero_le)
      (fun n => hlin n)
  have key := tendsto_integral_of_L1 (μ := (volume : Measure (Config d N)))
    (fun X => b15bp_dens0 D X * φ X) hmeas
    (F := fun n X => b15bp_dens D (M n) X * φ X) (Eventually.of_forall hFi) hlim
  rw [e0]
  exact Tendsto.congr (fun n => (e1 n).symm) key

example := (@b15b_gibbsRef_tendsto_weak_proof : type_of% @b15b_gibbsRef_tendsto_weak)

/-! ## Target 2: `b15b_totalPotential_c1` -/

theorem b15b_totalPotential_c1_proof (D : DynData d) (hV : Torus.IsCk 2 D.V) :
    B15BUnifC1 (totalPotential (N := N) D) := by
  have hd := b15_one_le_d D
  have hV1 : Torus.IsCk 1 D.V := ContDiff.of_le hV (by norm_num)
  intro Y hY
  apply ContDiffAt.contDiffWithinAt
  have hΦ : (fun Y : Fin N → Euc d => totalPotential (N := N) D (fun i => Torus.mk (Y i))) =
      fun Y : Fin N → Euc d => (1 / (2 * (N : ℝ))) *
        ∑ i, ∑ j ∈ Finset.univ.erase i, Torus.lift (periodicRiesz d D.s) (Y i - Y j)
          + ∑ i, Torus.lift D.V (Y i) := by
    funext Y'
    unfold totalPotential
    simp [Torus.lift, KernelGrad.mk_sub]
  rw [hΦ]
  refine ContDiffAt.add (ContDiffAt.mul contDiffAt_const
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j hj => ?_))
    (ContDiffAt.sum fun i _ => ?_)
  · have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hne : Torus.mk (Y i - Y j) ≠ 0 := by
      intro h0
      apply hY
      have h1 : Torus.mk (Y i) - Torus.mk (Y j) = 0 := by
        rw [← KernelGrad.mk_sub]
        exact h0
      exact ⟨i, j, hij, sub_eq_zero.mp h1⟩
    have hg : ContDiffAt ℝ 1 (Torus.lift (periodicRiesz d D.s)) (Y i - Y j) :=
      (b15c_contDiffAt_lift_periodicRiesz hd D.hs0 D.hsd hne).of_le (by exact_mod_cast le_top)
    have hf : ContDiffAt ℝ 1 (fun Z : Fin N → Euc d => Z i - Z j) Y :=
      ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffAt
    exact ContDiffAt.comp (g := Torus.lift (periodicRiesz d D.s)) (f := fun Z : Fin N → Euc d => Z i - Z j)
      Y hg hf
  · have hg : ContDiffAt ℝ 1 (Torus.lift D.V) (Y i) := (ContDiff.contDiffAt hV1)
    have hf : ContDiffAt ℝ 1 (fun Z : Fin N → Euc d => Z i) Y := (contDiff_apply ℝ (Euc d) i).contDiffAt
    exact ContDiffAt.comp (g := Torus.lift D.V) (f := fun Z : Fin N → Euc d => Z i) Y hg hf

example := (@b15b_totalPotential_c1_proof : type_of% @b15b_totalPotential_c1)

/-! ## Target 3: `b15b_fisherIntegrand_continuous` -/

theorem b15bp_Pi_continuous :
    Continuous (fun Y : Fin N → Euc d => fun i => Torus.mk (Y i)) :=
  continuous_pi fun i => Torus.continuous_mk.comp (continuous_apply i)

theorem b15bp_Pi_isOpenQuotientMap :
    IsOpenQuotientMap (fun Y : Fin N → Euc d => fun i => Torus.mk (Y i)) :=
  IsOpenQuotientMap.piMap fun _ => KernelGrad.isOpenQuotientMap_mk

theorem b15bp_isClosed_collisionSet : IsClosed (collisionSet d N) := by
  have h : collisionSet d N = ⋃ p : Fin N × Fin N, ⋃ _ : p.1 ≠ p.2, {X : Config d N | X p.1 = X p.2} := by
    ext X
    simp [collisionSet]
  rw [h]
  exact isClosed_iUnion_of_finite fun p => isClosed_iUnion_of_finite fun _ =>
    isClosed_eq (continuous_apply _) (continuous_apply _)

theorem b15bp_mk_add_of_mk_eq_zero (x w : Euc d) (hw : Torus.mk w = 0) :
    Torus.mk (x + w) = Torus.mk x := by
  have h1 := KernelGrad.mk_sub (x + w) x
  rw [add_sub_cancel_left, hw] at h1
  exact sub_eq_zero.mp h1.symm

/-- The fderiv of a function of the torus-valued configuration is invariant under changing the
representative `Y` to any `Y'` with the same images in the torus. -/
theorem b15bp_fderiv_eq_of_mk_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : Config d N → E) {Y Y' : Fin N → Euc d} (hY : ∀ i, Torus.mk (Y' i) = Torus.mk (Y i)) :
    fderiv ℝ (fun Z : Fin N → Euc d => Φ (fun i => Torus.mk (Z i))) Y' =
      fderiv ℝ (fun Z : Fin N → Euc d => Φ (fun i => Torus.mk (Z i))) Y := by
  obtain ⟨w, hw_def⟩ : ∃ w : Fin N → Euc d, w = Y' - Y := ⟨_, rfl⟩
  have hw : ∀ i, Torus.mk (w i) = 0 := by
    intro i
    rw [hw_def, Pi.sub_apply, KernelGrad.mk_sub, hY i, sub_self]
  have hYw : Y' = Y + w := by rw [hw_def]; abel
  have e : (fun Z : Fin N → Euc d => Φ (fun i => Torus.mk ((Z + w) i))) =
      fun Z => Φ (fun i => Torus.mk (Z i)) := by
    funext Z
    have hz : (fun i => Torus.mk ((Z + w) i)) = fun i => Torus.mk (Z i) :=
      funext fun i => b15bp_mk_add_of_mk_eq_zero (Z i) (w i) (hw i)
    rw [hz]
  calc fderiv ℝ (fun Z : Fin N → Euc d => Φ (fun i => Torus.mk (Z i))) Y'
      = fderiv ℝ (fun Z : Fin N → Euc d => Φ (fun i => Torus.mk (Z i))) (Y + w) := by rw [hYw]
    _ = fderiv ℝ (fun Z : Fin N → Euc d => Φ (fun i => Torus.mk ((Z + w) i))) Y :=
        (fderiv_comp_add_right w).symm
    _ = fderiv ℝ (fun Z : Fin N → Euc d => Φ (fun i => Torus.mk (Z i))) Y := by rw [e]

/-- The Fisher integrand written in the lifted coordinates `Y` (any representative of `X = mk ∘ Y`). -/
def b15bp_G (invβ : ℝ) (U : Config d N → ℝ) (ζ : Config d N → (Fin N → Euc d))
    (Y : Fin N → Euc d) : ℝ :=
  -2 * (∑ k : Fin N × Fin d,
      fderiv ℝ (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2) Y (configBasis d N k))
    + 2 * invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))) Y
        (ζ (fun i => Torus.mk (Y i)))
    - ∑ i, ‖ζ (fun i => Torus.mk (Y i)) i‖ ^ 2

theorem b15bp_fisherIntegrand_eq (invβ : ℝ) (U : Config d N → ℝ) (ζ : Config d N → (Fin N → Euc d))
    (Y : Fin N → Euc d) :
    b15c_fisherIntegrand invβ U ζ (fun i => Torus.mk (Y i)) = b15bp_G invβ U ζ Y := by
  have hY' : ∀ i, Torus.mk (Torus.rep (Torus.mk (Y i))) = Torus.mk (Y i) := fun i => Torus.mk_rep _
  have c1 : ∀ k : Fin N × Fin d,
      fderiv ℝ (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2)
        (fun i => Torus.rep (Torus.mk (Y i))) =
      fderiv ℝ (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2) Y :=
    fun k => b15bp_fderiv_eq_of_mk_eq (fun X => ζ X k.1 k.2) hY'
  have c2 : fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i)))
        (fun i => Torus.rep (Torus.mk (Y i))) =
      fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))) Y :=
    b15bp_fderiv_eq_of_mk_eq U hY'
  unfold b15c_fisherIntegrand b15bp_G configDiv
  simp only [c1, c2]

theorem b15bp_G_continuousAt (invβ : ℝ) {U : Config d N → ℝ} (hU : B15BUnifC1 U)
    {ζ : Config d N → (Fin N → Euc d)} (hζ : IsFisherTestField ζ) {Y₀ : Fin N → Euc d}
    (hY₀ : (fun i => Torus.mk (Y₀ i)) ∉ collisionSet d N) :
    ContinuousAt (b15bp_G invβ U ζ) Y₀ := by
  have hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Y : Fin N → Euc d => ζ (fun i => Torus.mk (Y i))) :=
    hζ.smooth
  have hζc : Continuous (fun Y : Fin N → Euc d => ζ (fun i => Torus.mk (Y i))) := hζs.continuous
  have hgk : ∀ k : Fin N × Fin d, Continuous
      (fderiv ℝ (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2)) := fun k => by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2) :=
      (EuclideanSpace.proj k.2 : Euc d →L[ℝ] ℝ).contDiff.comp ((contDiff_apply ℝ (Euc d) k.1).comp hζs)
    exact hs.continuous_fderiv (by simp)
  have hA : Continuous (fun Y : Fin N → Euc d => ∑ k : Fin N × Fin d,
      fderiv ℝ (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2) Y (configBasis d N k)) :=
    continuous_finset_sum _ fun k _ => (hgk k).clm_apply continuous_const
  have hO : IsOpen {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N} :=
    (b15bp_isClosed_collisionSet (d := d) (N := N)).isOpen_compl.preimage b15bp_Pi_continuous
  have hU' : ContDiffOn ℝ 1 (fun Y : Fin N → Euc d => U (fun i => Torus.mk (Y i)))
      {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N} := hU
  have hfd : ContinuousAt (fun Y : Fin N → Euc d =>
      fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))) Y) Y₀ :=
    (hU'.continuousOn_fderiv_of_isOpen hO le_rfl).continuousAt (hO.mem_nhds hY₀)
  have hB : ContinuousAt (fun Y : Fin N → Euc d =>
      fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i))) Y (ζ (fun i => Torus.mk (Y i)))) Y₀ :=
    hfd.clm_apply hζc.continuousAt
  have hC : Continuous (fun Y : Fin N → Euc d => ∑ i, ‖ζ (fun i => Torus.mk (Y i)) i‖ ^ 2) :=
    continuous_finset_sum _ fun i _ => (continuous_norm.comp ((continuous_apply i).comp hζc)).pow 2
  unfold b15bp_G
  exact ((continuousAt_const.mul hA.continuousAt).add (continuousAt_const.mul hB)).sub hC.continuousAt

theorem b15b_fisherIntegrand_continuous_proof (invβ : ℝ) {U : Config d N → ℝ} (hU : B15BUnifC1 U)
    {ζ : Config d N → (Fin N → Euc d)} (hζ : IsFisherTestField ζ) :
    Continuous (b15c_fisherIntegrand invβ U ζ) := by
  obtain ⟨K, hKc, hKdisj, hKζ⟩ := hζ.support
  refine continuous_iff_continuousAt.2 fun X => ?_
  by_cases hX : X ∈ collisionSet d N
  · have hXK : X ∉ K := fun h => Set.disjoint_left.mp hKdisj h hX
    have hKo : IsOpen Kᶜ := hKc.isClosed.isOpen_compl
    have hloc : ∀ X' ∈ Kᶜ, b15c_fisherIntegrand invβ U ζ X' = 0 := by
      intro X' hX'
      have hζ0 : ζ X' = 0 := hKζ X' hX'
      have hev : ∀ k : Fin N × Fin d,
          fderiv ℝ (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2)
            (fun i => Torus.rep (X' i)) = 0 := by
        intro k
        have hmem : (fun i => Torus.rep (X' i)) ∈
            (fun Y : Fin N → Euc d => fun i => Torus.mk (Y i)) ⁻¹' Kᶜ := by
          show (fun i => Torus.mk (Torus.rep (X' i))) ∈ Kᶜ
          have : (fun i => Torus.mk (Torus.rep (X' i))) = X' := funext fun i => Torus.mk_rep (X' i)
          rw [this]
          exact hX'
        have hEv : (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2) =ᶠ[𝓝 (fun i => Torus.rep (X' i))]
            fun _ => 0 := by
          filter_upwards [(hKo.preimage b15bp_Pi_continuous).mem_nhds hmem] with Z hZ
          have h0 : ζ (fun i => Torus.mk (Z i)) = 0 := hKζ _ hZ
          simp [h0]
        rw [hEv.fderiv_eq]
        simp
      unfold b15c_fisherIntegrand configDiv
      simp [hζ0, hev]
    refine ContinuousAt.congr (continuousAt_const : ContinuousAt (fun _ : Config d N => (0:ℝ)) X) ?_
    filter_upwards [hKo.mem_nhds hXK] with X' hX'
    exact (hloc X' hX').symm
  · obtain ⟨Y₀, hPY₀⟩ : ∃ Y₀ : Fin N → Euc d, (fun i => Torus.mk (Y₀ i)) = X :=
      ⟨fun i => Torus.rep (X i), funext fun i => Torus.mk_rep (X i)⟩
    have hGc := b15bp_G_continuousAt invβ hU hζ (Y₀ := Y₀) (by rw [hPY₀]; exact hX)
    have hcomp : (b15c_fisherIntegrand invβ U ζ ∘ fun Y : Fin N → Euc d => fun i => Torus.mk (Y i)) =
        b15bp_G invβ U ζ := funext fun Y => b15bp_fisherIntegrand_eq invβ U ζ Y
    have h1 : ContinuousAt (b15c_fisherIntegrand invβ U ζ ∘
        fun Y : Fin N → Euc d => fun i => Torus.mk (Y i)) Y₀ := by
      rw [hcomp]
      exact hGc
    have h2 := (b15bp_Pi_isOpenQuotientMap (d := d) (N := N)).continuousAt_comp_iff.mp h1
    have h3 : ContinuousAt (b15c_fisherIntegrand invβ U ζ) (fun i => Torus.mk (Y₀ i)) := h2
    rw [hPY₀] at h3
    exact h3

example := (@b15b_fisherIntegrand_continuous_proof : type_of% @b15b_fisherIntegrand_continuous)

/-! ## Target 4: `b15b_gibbsEntropy_liminf_le` -/

theorem b15bp_gibbsRefGen_isProb (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℝ} (hM0 : 0 ≤ M) :
    IsProbabilityMeasure (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D M)) := by
  obtain ⟨h1, h2⟩ := b15bp_partitionGen_bounds D hβ hV hM0
  refine ⟨?_⟩
  unfold b15c_gibbsRefGen
  simp only [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel h2 h1

theorem b15b_gibbsEntropy_liminf_le_proof (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {P : Measure (Config d N)} {Pn : ℕ → Measure (Config d N)}
    [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Pn n)]
    (hP : ∀ φ : Config d N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂(Pn n)) atTop (𝓝 (∫ x, φ x ∂P))) :
    gibbsEntropy D P ≤
      liminf (fun n => b15c_gibbsEntropyGen D.invβ (b15c_potentialReg (N := N) D (M n)) (Pn n)) atTop := by
  haveI : IsProbabilityMeasure (gibbsRef D N) := b15b_gibbsRef_isProb D hβ hV
  haveI : ∀ n, IsProbabilityMeasure (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n))) :=
    fun n => b15bp_gibbsRefGen_isProb D hβ hV (hM0 n)
  obtain ⟨hZpos, -⟩ := b15c_partition_bounds (N := N) D hβ hV
  have hkl := b15b_klDiv_liminf_le (P := P) (Q := gibbsRef D N) (Pn := Pn)
    (Qn := fun n => b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n)))
    hP (fun φ hφ => b15b_gibbsRef_tendsto_weak_proof D hβ hV hM hM0 hφ)
  have hZt := b15c_partition_tendsto (N := N) D hβ hV hM hM0
  have hlog : Tendsto (fun n => Real.log
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (M n))).toReal) atTop
      (𝓝 (Real.log (gibbsPartition D N).toReal)) := hZt.log hZpos.ne'
  have hLn : Tendsto (fun n => ((-Real.log
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (M n))).toReal : ℝ) : EReal)) atTop
      (𝓝 ((-Real.log (gibbsPartition D N).toReal : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 hlog.neg
  have hmono : Monotone (fun x : ℝ≥0∞ => ((x : ℝ≥0∞) : EReal)) :=
    fun x y h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  have hcont : Continuous (fun x : ℝ≥0∞ => ((x : ℝ≥0∞) : EReal)) := continuous_coe_ennreal_ereal
  have hc : ((InformationTheory.klDiv P (gibbsRef D N) : ℝ≥0∞) : EReal) ≤
      liminf (fun n => ((InformationTheory.klDiv (Pn n)
        (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n))) : ℝ≥0∞) : EReal)) atTop :=
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hkl).trans
      (hmono.map_liminf_of_continuousAt (F := atTop) (fun n => InformationTheory.klDiv (Pn n)
        (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n)))) hcont.continuousAt).le
  have hfun : (fun n => b15c_gibbsEntropyGen D.invβ (b15c_potentialReg (N := N) D (M n)) (Pn n)) =
      fun n => ((InformationTheory.klDiv (Pn n)
        (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n))) : ℝ≥0∞) : EReal)
        + ((-Real.log (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (M n))).toReal : ℝ) : EReal) := by
    funext n
    unfold b15c_gibbsEntropyGen relEntropy
    rw [sub_eq_add_neg, EReal.coe_neg]
  have hgibbs : gibbsEntropy D P = ((InformationTheory.klDiv P (gibbsRef D N) : ℝ≥0∞) : EReal)
      + ((-Real.log (gibbsPartition D N).toReal : ℝ) : EReal) := by
    unfold gibbsEntropy relEntropy
    rw [sub_eq_add_neg, EReal.coe_neg]
  rw [hfun, hgibbs]
  calc _ ≤ liminf (fun n => ((InformationTheory.klDiv (Pn n)
        (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n))) : ℝ≥0∞) : EReal)) atTop
        + ((-Real.log (gibbsPartition D N).toReal : ℝ) : EReal) := add_le_add hc le_rfl
    _ = liminf (fun n => ((InformationTheory.klDiv (Pn n)
        (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D (M n))) : ℝ≥0∞) : EReal)) atTop
        + liminf (fun n => ((-Real.log
          (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (M n))).toReal : ℝ) : EReal)) atTop := by
          rw [hLn.liminf_eq]
    _ ≤ _ := EReal.le_liminf_add

example := (@b15b_gibbsEntropy_liminf_le_proof : type_of% @b15b_gibbsEntropy_liminf_le)

end HRS
