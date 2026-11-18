import HRS.Energy.Commutator.RenormField

/-!
# Route S, packet S4: the Coulomb slice `l = 0` -- kernel side facts
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.RoughLimit

namespace HRS.Commutator.Renorm

variable {d : ℕ}

/-- the Coulomb normalisation constant -/
def cC (d : ℕ) : ℝ := 4 * Real.pi ^ 2 * KernelAux.subA d ((d : ℝ) - 2)

theorem cC_pos (hd : 2 ≤ d) : 0 < cC d := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  exact mul_pos (by positivity) (CoercAux.subA_pos_one hd1 hs0 hsd)

/-- the Coulomb kernel with the explicit constant `cC d` -/
theorem coulomb_kernel_c (hd : 2 ≤ d) (x : Torus d) (hx : x ≠ 0) :
    periodicRiesz d ((d : ℝ) - 2) x = cC d * sliceG d 0 x := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  have hi := KernelAux.integrableOn_psi hsd x hx
  have hb : (((d : ℝ) - ((d : ℝ) - 2)) / 2 - 1) = 0 := by ring
  rw [hb] at hi
  simp only [Real.rpow_zero, one_mul] at hi
  obtain ⟨-, he⟩ := SliceAux.scale_integral (β := 1) (b := 4 * Real.pi ^ 2) (by positivity)
    (H := fun u => psiFn x u) (by simpa using hi)
  rw [CoercAux.periodicRiesz_eq_integral_one hd1 hs0 hsd x hx, hb]
  simp only [Real.rpow_zero, one_mul, sub_self] at he ⊢
  rw [he, Real.rpow_one]
  unfold sliceG cC
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
  ring

/-- gradient of the Coulomb kernel: `∇g = c₀ ∇𝒢_0` off the origin. -/
theorem coulomb_grad_c (hd : 2 ≤ d) (x : Torus d) (hx : x ≠ 0) :
    periodicRieszGrad d ((d : ℝ) - 2) x = cC d • SliceAux.sgv 0 x := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  obtain ⟨xe, rfl, hxe⟩ := KernelGrad.exists_mk_box x
  have hne : xe ≠ 0 := SliceAux.mk_ne_zero_ne_zero hx
  rw [KernelAux.periodicRieszGrad_eq hsd xe hxe hne]
  ext j
  have hb : (((d : ℝ) - ((d : ℝ) - 2)) / 2 - 1) = 0 := by ring
  have hi := SliceAux.integrableOn_psiG (d := d) (a := 1) one_pos j hx
  simp only [sub_self, Real.rpow_zero, one_mul] at hi
  obtain ⟨-, he⟩ := SliceAux.scale_integral (β := 1) (b := 4 * Real.pi ^ 2) (by positivity)
    (H := fun u => KernelAux.psiG j (Torus.mk xe) u) (by simpa using hi)
  simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one] at he
  show KernelAux.subA d ((d : ℝ) - 2) * ∫ t in Ioi (0 : ℝ), t ^ (((d : ℝ) - ((d : ℝ) - 2)) / 2 - 1) *
      KernelAux.psiG j (Torus.mk xe) t = _
  rw [hb]
  simp only [Real.rpow_zero, one_mul, PiLp.smul_apply, smul_eq_mul]
  unfold SliceAux.sgv SliceAux.sgc cC
  simp only [PiLp.toLp_apply, neg_zero, zero_mul, Real.exp_zero, one_mul]
  rw [he]; ring

theorem offDiagPairing_const_mul {N : ℕ} (c : ℝ) (k : Torus d → Torus d → ℝ) (X : Config d N)
    (μ : Measure (Torus d)) :
    offDiagPairing (fun x y => c * k x y) X μ = c * offDiagPairing k X μ := by
  unfold offDiagPairing
  simp_rw [integral_const_mul, ← Finset.mul_sum]
  ring

theorem commQuantity_coulomb (hd : 2 ≤ d) {N : ℕ} (X : Config d N) (μ : Measure (Torus d))
    (v : Torus d → Euc d) :
    commQuantity d ((d : ℝ) - 2) v X μ = cC d * offDiagPairing (commKernel (SliceAux.sgv 0) v) X μ := by
  unfold commQuantity commQuantityWith
  have : commKernel (periodicRieszGrad d ((d : ℝ) - 2)) v = fun x y => cC d * commKernel (SliceAux.sgv 0) v x y := by
    funext x y
    unfold commKernel
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, if_false]
      rw [coulomb_grad_c hd _ (sub_ne_zero.mpr hxy), inner_smul_right]
  rw [this, offDiagPairing_const_mul]

theorem rieszEnergy_coulomb (hd : 2 ≤ d) {N : ℕ} (X : Config d N) (hX : ∀ i j, i ≠ j → X i ≠ X j)
    (μ : Measure (Torus d)) (hμ : ∀ x, μ {x} = 0) :
    rieszEnergy d ((d : ℝ) - 2) X μ = cC d * modulatedEnergyKernel (sliceG d 0) X μ := by
  unfold rieszEnergy modulatedEnergyKernel modulatedEnergy
  have h1 : ∀ x : Torus d, ∫ y, periodicRiesz d ((d : ℝ) - 2) (x - y) ∂μ = cC d * ∫ y, sliceG d 0 (x - y) ∂μ := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    have : ∀ᵐ y ∂μ, y ≠ x := by
      have h0 : μ {x} = 0 := hμ x
      rw [ae_iff]
      simpa using h0
    filter_upwards [this] with y hy
    exact coulomb_kernel_c hd _ (sub_ne_zero.mpr hy.symm)
  have h2 : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      periodicRiesz d ((d : ℝ) - 2) (X i - X j) = cC d * sliceG d 0 (X i - X j) := by
    intro i j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    exact coulomb_kernel_c hd _ (sub_ne_zero.mpr (hX i j hji.symm))
  simp_rw [h1]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl (h2 i)]
  simp_rw [← Finset.mul_sum, integral_const_mul]
  ring

theorem chC_univ (hd : 1 ≤ d) (η : ℝ) (a : Torus d) : chC d η a Set.univ = 1 := by
  unfold chC
  rw [Measure.map_apply (measurable_add_const a) MeasurableSet.univ, Set.preimage_univ]
  exact EnergyAux.sphereT_univ hd η

theorem chC_atom (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (a x : Torus d) : chC d η a {x} = 0 := by
  unfold chC
  rw [Measure.map_apply (measurable_add_const a) (measurableSet_singleton _)]
  have : (fun y : Torus d => y + a) ⁻¹' {x} = {x - a} := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact (eq_sub_iff_add_eq).symm
  rw [this]
  exact EnergyAux.sphereT_singleton_null hd hη hη2 _

theorem chC_Gii (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d) :
    Integrable (fun p : Torus d × Torus d => sliceGfull d 0 (p.1 - p.2)) ((chC d η a).prod (chC d η a)) := by
  have hd1 : 1 ≤ d := by omega
  haveI := isFiniteMeasure_chC hd1 η a
  obtain ⟨M, hM0, hM0'⟩ := EnergyAux.sliceG_zero_lower d
  have hM : ∀ x, 0 ≤ sliceG d 0 x + M := fun x => by linarith [hM0' x]
  have hmeas : Measurable fun p : Torus d × Torus d => sliceG d 0 (p.1 - p.2) + M :=
    ((EnergyAux.measurable_sliceG 0).comp (measurable_fst.sub measurable_snd)).add measurable_const
  have hfin : ∫⁻ p : Torus d × Torus d, ENNReal.ofReal (sliceG d 0 (p.1 - p.2) + M) ∂((chC d η a).prod (chC d η a)) < ⊤ := by
    rw [lintegral_prod _ hmeas.ennreal_ofReal.aemeasurable]
    unfold chC
    have := EnergyAux.lintegral_self_shift' (sphereT d η) a M
    simp only [] at this ⊢
    rw [this]
    exact EnergyAux.lintegral_self0_lt_top hd hM hη hη2
  have hI : Integrable (fun p : Torus d × Torus d => sliceG d 0 (p.1 - p.2) + M) ((chC d η a).prod (chC d η a)) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hM _)).mp hfin.ne
  have := hI.sub (integrable_const M)
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [sliceGfull]

theorem sliceCharges_coulomb (hd : 2 ≤ d) {N : ℕ} {X : Fin N → Torus d} {η : Fin N → ℝ}
    (hη : ∀ i, 0 < η i ∧ η i < 1 / 2) (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) :
    SliceCharges 0 X η (fun i => chC d (η i) (X i)) := by
  have hd1 : 1 ≤ d := by omega
  exact
    { η0 := fun i => (hη i).1
      fin := fun i => isFiniteMeasure_chC hd1 (η i) (X i)
      supp := fun i => chC_supp hd1 (hη i).1 (hη i).2 (X i)
      rep := fun i y hy => chC_repro hd (hη i).1 (hη i).2 (X i) hy
      sep := hdisj
      atom := fun _ i x => chC_atom hd (hη i).1 (hη i).2 (X i) x
      mass_le := fun i => by
        simp [Measure.real, chC_univ hd1]
      neutral := fun _ i => chC_univ hd1 _ _
      Gii := fun i => chC_Gii hd (hη i).1 (hη i).2 (X i) }

theorem integral_sliceG0 (hd : 2 ≤ d) : ∫ z : Torus d, sliceG d 0 z = 0 := by
  obtain ⟨c, hc, hker⟩ := coulomb_kernel hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  have h := (integral_periodicRiesz hd hs0 hsd).2
  have e : ∀ᵐ x : Torus d, periodicRiesz d ((d : ℝ) - 2) x = c * sliceG d 0 x := by
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with x hx
    exact hker x hx
  rw [integral_congr_ae e, integral_const_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hc.ne'
  · exact h1

theorem integral_fTrunc0 (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    Integrable (fTrunc0 d η) volume ∧ ∫ z, fTrunc0 d η z = η ^ 2 / (2 * d) := by
  have hd1 : 1 ≤ d := by omega
  haveI := EnergyAux.isProbabilityMeasure_sphereT hd1 η
  set τ := sphereT d η with hτ
  have hGi : Integrable (sliceG d 0 : Torus d → ℝ) volume := RoughKernel.integrable_sliceG le_rfl
  have hGm : Measurable (sliceG d 0 : Torus d → ℝ) := EnergyAux.measurable_sliceG 0
  have hPi : Integrable (fun x : Torus d => ∫ y, sliceG d 0 (x - y) ∂τ) volume := by
    have h := (integrable_conv_swap hGm hGi τ).swap
    exact h.integral_prod_left
  have hP0 : ∫ x : Torus d, ∫ y, sliceG d 0 (x - y) ∂τ = 0 := by
    have h := integrable_conv_swap hGm hGi τ
    have h' : Integrable (Function.uncurry fun (x y : Torus d) => sliceG d 0 (x - y)) ((volume : Measure (Torus d)).prod τ) := by
      have := h.swap
      exact this
    rw [integral_integral_swap h']
    simp_rw [integral_sub_right_eq_self (fun x => sliceG d 0 x) _, integral_sliceG0 hd]
    simp
  have hae : ∀ᵐ x : Torus d, fTrunc0 d η x = sliceG d 0 x + η ^ 2 / (2 * d) - ∫ y, sliceG d 0 (x - y) ∂τ := by
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with x hx
    rw [sliceG0_conv_sphere hd hη hη2 x hx]; ring
  have hint : Integrable (fun x : Torus d => sliceG d 0 x + η ^ 2 / (2 * d) - ∫ y, sliceG d 0 (x - y) ∂τ) volume :=
    (hGi.add (integrable_const _)).sub hPi
  refine ⟨hint.congr (hae.mono fun x hx => hx.symm), ?_⟩
  have hA : Integrable (fun x : Torus d => sliceG d 0 x + η ^ 2 / (2 * d)) volume := hGi.add (integrable_const _)
  rw [integral_congr_ae hae, integral_sub hA hPi, integral_add hGi (integrable_const _),
    hP0, integral_sliceG0 hd]
  simp

/-- the self energy `S_0(η) = ∬ 𝒢_0 dτ_η dτ_η` -/
def S0 (d : ℕ) (η : ℝ) : ℝ := ∫ x, ∫ y, sliceG d 0 (x - y) ∂(sphereT d η) ∂(sphereT d η)

theorem sliceGfull_zero (x : Torus d) : sliceGfull d 0 x = sliceG d 0 x := by simp [sliceGfull]

theorem quadForm_chC (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d) :
    quadForm (fun x y => sliceGfull d 0 (x - y)) (chC d η a)
      (ENNReal.ofReal ((chC d η a).real Set.univ) • (volume : Measure (Torus d))) = S0 d η := by
  have hd1 : 1 ≤ d := by omega
  have h1 : (chC d η a).real Set.univ = 1 := by simp [Measure.real, chC_univ hd1]
  rw [h1, ENNReal.ofReal_one, one_smul]
  have hz : ∀ x : Torus d, ∫ y, sliceGfull d 0 (x - y) ∂(volume : Measure (Torus d)) = 0 := by
    intro x
    simp_rw [sliceGfull_zero]
    rw [integral_sub_left_eq_self (fun z => sliceG d 0 z) volume x, integral_sliceG0 hd]
  unfold quadForm
  simp_rw [hz]
  simp only [integral_zero, mul_zero, sub_zero, add_zero]
  unfold S0 chC
  simp_rw [sliceGfull_zero]
  have emb := (MeasurableEquiv.addRight a).measurableEmbedding
  have e1 : (fun y : Torus d => y + a) = ⇑(MeasurableEquiv.addRight a) := rfl
  rw [e1]
  have key : ∀ x : Torus d, ∫ y, sliceG d 0 (x - y) ∂((sphereT d η).map (MeasurableEquiv.addRight a)) =
      ∫ y, sliceG d 0 (x - a - y) ∂(sphereT d η) := by
    intro x
    rw [emb.integral_map]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show sliceG d 0 (x - (y + a)) = _
    congr 1; abel
  simp_rw [key]
  rw [emb.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∫ y, sliceG d 0 (x + a - a - y) ∂(sphereT d η) = _
  simp

theorem integrable_sliceG_sub_mu {l : ℝ} (hl : 0 ≤ l) (x : Torus d) {μ : Measure (Torus d)}
    [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    Integrable (fun y => sliceG d l (x - y)) μ := by
  have h := ((RoughKernel.integrable_sliceG (d := d) hl).comp_sub_left x).smul_measure hc
  exact h.mono_measure hμ

theorem int_f_le (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (a : Torus d) {μ : Measure (Torus d)}
    [IsFiniteMeasure μ] {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) :
    ∫ y, fTrunc0 d η (a - y) ∂μ ≤ Λ * (η ^ 2 / (2 * d)) := by
  obtain ⟨hfi, hfint⟩ := integral_fTrunc0 hd hη hη2
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnn : ∀ y, 0 ≤ fTrunc0 d η (a - y) := fun y => le_max_right _ _
  have hi : Integrable (fun y => fTrunc0 d η (a - y)) (ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
    (hfi.comp_sub_left a).smul_measure hc
  calc ∫ y, fTrunc0 d η (a - y) ∂μ ≤ ∫ y, fTrunc0 d η (a - y) ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
        integral_mono_measure hμ (Filter.Eventually.of_forall hnn) hi
    _ = Λ * (η ^ 2 / (2 * d)) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ0, integral_sub_left_eq_self (fun z => fTrunc0 d η z) volume a,
          hfint]
        rfl

theorem sum_erase_pair_le {N : ℕ} (κ : Fin N → ℝ) (h0 : ∀ i, 0 ≤ κ i) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, (κ i + κ j) ≤ 2 * N * ∑ i, κ i := by
  calc ∑ i, ∑ j ∈ Finset.univ.erase i, (κ i + κ j) ≤ ∑ i, ∑ j, (κ i + κ j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun j _ _ => add_nonneg (h0 i) (h0 j))
    _ = 2 * N * ∑ i, κ i := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        ring

theorem coulomb_energy (hd : 2 ≤ d) {N : ℕ} (hN : N ≠ 0) {X : Fin N → Torus d} {η : Fin N → ℝ}
    (hη : ∀ i, 0 < η i ∧ η i < 1 / 2) (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) :
    quadForm (fun x y => sliceGfull d 0 (x - y)) (avgM fun i => chC d (η i) (X i)) μ ≤
      2 * modulatedEnergyKernel (sliceG d 0) X μ + (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i) +
        (2 * Λ / N) * ∑ i, η i ^ 2 / (2 * d) := by
  have hd1 : 1 ≤ d := by omega
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ0 : ∀ x, μ {x} = 0 := atomless_of_le_vol hd1 hc hμ
  have hμ1' : ∀ x, Integrable (fun y => sliceG d 0 (x - y)) μ := fun x => integrable_sliceG_sub_mu le_rfl x hc hμ
  have hμ2 : Integrable (fun p : Torus d × Torus d => sliceG d 0 (p.1 - p.2)) (μ.prod μ) := by
    have := integrable_G_mu (d := d) (le_refl (0 : ℝ)) μ hc hμ
    simpa [sliceGfull_zero] using this
  have hid := energy_identity_coulomb hd μ hμ0 hμ1' hμ2 X η hη hdisj
  have hE : quadForm (fun x y => sliceGfull d 0 (x - y)) (avgM fun i => chC d (η i) (X i)) μ =
      quadForm (fun x y => sliceG d 0 (x - y)) (chargeMeasure (sphereT d) η X) μ := by
    have : chargeMeasure (sphereT d) η X = avgM fun i => chC d (η i) (X i) := rfl
    rw [this]
    simp_rw [sliceGfull_zero]
  rw [hE, hid]
  haveI : IsProbabilityMeasure μ := ⟨hμ1⟩
  have hTi : ∀ i, ∫ y, (sliceG d 0 (X i - y) - fTrunc0 d (η i) (X i - y) + η i ^ 2 / (2 * d)) ∂μ =
      (∫ y, sliceG d 0 (X i - y) ∂μ) - (∫ y, fTrunc0 d (η i) (X i - y) ∂μ) + η i ^ 2 / (2 * d) := by
    intro i
    have hfi : Integrable (fun y => fTrunc0 d (η i) (X i - y)) μ := by
      have := ((integral_fTrunc0 hd (hη i).1 (hη i).2).1.comp_sub_left (X i)).smul_measure hc
      exact this.mono_measure hμ
    have hsub : Integrable (fun y => sliceG d 0 (X i - y) - fTrunc0 d (η i) (X i - y)) μ := (hμ1' (X i)).sub hfi
    rw [integral_add hsub (integrable_const (η i ^ 2 / (2 * (d : ℝ)))), integral_sub (hμ1' (X i)) hfi, integral_const]
    simp
  simp_rw [hTi]
  have hfle : ∀ i, ∫ y, fTrunc0 d (η i) (X i - y) ∂μ ≤ Λ * (η i ^ 2 / (2 * d)) := fun i =>
    int_f_le hd (hη i).1 (hη i).2 (X i) hΛ0 hμ
  have hκ0 : ∀ i, 0 ≤ η i ^ 2 / (2 * (d : ℝ)) := fun i => by positivity
  set K : ℝ := ∑ i, η i ^ 2 / (2 * (d : ℝ)) with hK
  have hKk : ∑ i, ∑ j ∈ Finset.univ.erase i, (η i ^ 2 / (2 * (d : ℝ)) + η j ^ 2 / (2 * (d : ℝ))) ≤ 2 * N * K :=
    sum_erase_pair_le (fun i => η i ^ 2 / (2 * (d : ℝ))) hκ0
  have hFsum : ∑ i, ∫ y, fTrunc0 d (η i) (X i - y) ∂μ ≤ Λ * K := by
    calc ∑ i, ∫ y, fTrunc0 d (η i) (X i - y) ∂μ ≤ ∑ i, Λ * (η i ^ 2 / (2 * (d : ℝ))) := Finset.sum_le_sum fun i _ => hfle i
      _ = Λ * K := by rw [hK, Finset.mul_sum]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hu : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have h1 : (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, (η i ^ 2 / (2 * (d : ℝ)) + η j ^ 2 / (2 * (d : ℝ))) ≤
      (2 / (N : ℝ)) * K := by
    calc (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, (η i ^ 2 / (2 * (d : ℝ)) + η j ^ 2 / (2 * (d : ℝ)))
        ≤ (1 / (N : ℝ) ^ 2) * (2 * N * K) := mul_le_mul_of_nonneg_left hKk (by positivity)
      _ = (2 / (N : ℝ)) * K := by field_simp
  have h2 : (2 / (N : ℝ)) * ∑ i, ∫ y, fTrunc0 d (η i) (X i - y) ∂μ ≤ (2 / (N : ℝ)) * (Λ * K) :=
    mul_le_mul_of_nonneg_left hFsum (by positivity)
  have hA : ∑ i, ∑ j ∈ Finset.univ.erase i, (sliceG d 0 (X i - X j) + η i ^ 2 / (2 * (d : ℝ)) + η j ^ 2 / (2 * (d : ℝ))) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, sliceG d 0 (X i - X j) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, (η i ^ 2 / (2 * (d : ℝ)) + η j ^ 2 / (2 * (d : ℝ))) := by
    simp_rw [add_assoc, Finset.sum_add_distrib]
  have hT : ∑ i, ((∫ y, sliceG d 0 (X i - y) ∂μ) - (∫ y, fTrunc0 d (η i) (X i - y) ∂μ) + η i ^ 2 / (2 * (d : ℝ))) =
      ∑ i, (∫ y, sliceG d 0 (X i - y) ∂μ) - ∑ i, (∫ y, fTrunc0 d (η i) (X i - y) ∂μ) + K := by
    rw [hK, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hT]
  unfold modulatedEnergyKernel modulatedEnergy
  have hS : ∑ i, S0 d (η i) = ∑ i, ∫ x, ∫ y, sliceG d 0 (x - y) ∂(sphereT d (η i)) ∂(sphereT d (η i)) := rfl
  rw [hS]
  have h3 : (2 * Λ / (N : ℝ)) * K = (2 / (N : ℝ)) * (Λ * K) := by ring
  rw [h3]
  beta_reduce
  rw [one_div_pow]
  generalize (∑ i, ∑ j ∈ Finset.univ.erase i, (η i ^ 2 / (2 * (d : ℝ)) + η j ^ 2 / (2 * (d : ℝ)))) = Kk at h1 ⊢
  generalize (∑ i, ∫ y, fTrunc0 d (η i) (X i - y) ∂μ) = Fs at h2 ⊢
  generalize (∑ i, ∑ j ∈ Finset.univ.erase i, sliceG d 0 (X i - X j)) = A
  generalize (∑ i, ∫ y, sliceG d 0 (X i - y) ∂μ) = Bs
  generalize (∑ i, ∫ x, ∫ y, sliceG d 0 (x - y) ∂(sphereT d (η i)) ∂(sphereT d (η i))) = Sk
  generalize (∫ x, ∫ y, sliceG d 0 (x - y) ∂μ ∂μ) = BB
  ring_nf at h1 h2 ⊢
  linarith

theorem local_sing_unified (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) = selfScale d s ‖x‖ + r (Torus.mk x) := by
  by_cases hs : s = 0
  · subst hs
    obtain ⟨r, δ, hδ, hr, h⟩ := periodicLog_local_singularity (d := d) hd
    refine ⟨r, δ, hδ, hr, fun x hx hx0 => ?_⟩
    rw [h x hx hx0]; simp [selfScale]
  · have hpos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨r, δ, hδ, hr, h⟩ := periodicRiesz_local_singularity hd hpos hsd
    refine ⟨r, δ, hδ, hr, fun x hx hx0 => ?_⟩
    rw [h x hx hx0]; simp [selfScale, hs]

theorem selfScale_nonneg {d : ℕ} {s : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : 0 ≤ selfScale d s t := by
  unfold selfScale
  split_ifs
  · have := Real.log_nonpos ht.le ht1
    linarith
  · exact Real.rpow_nonneg ht.le _

theorem sliceG0_upper (hd : 2 ≤ d) : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ x : Torus d,
    KernelGrad.tdist x 0 ≤ 1 / 8 → x ≠ 0 →
      sliceG d 0 x ≤ (cC d)⁻¹ * selfScale d ((d : ℝ) - 2) (KernelGrad.tdist x 0) + C₂ := by
  have hc : 0 < cC d := cC_pos hd
  have hker := fun x hx => coulomb_kernel_c hd x hx
  set c := cC d with hcdef
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  obtain ⟨r, δ, hδ, hr, hloc⟩ := local_sing_unified hd hs0 hsd
  have hrc : Continuous (Torus.lift r) := (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  obtain ⟨R, hR⟩ := (isCompact_closedBall (0 : Euc d) (δ / 2)).exists_bound_of_continuousOn hrc.continuousOn
  obtain ⟨B, hB⟩ := EnergyAux.sliceG_bdd_away (d := d) (le_refl (0 : ℝ)) (by linarith : 0 < δ / 2)
  refine ⟨c⁻¹ * |R| + |B|, by positivity, fun x hx1 hx0 => ?_⟩
  have ht : 0 < KernelGrad.tdist x 0 := KernelGrad.tdist_pos hx0
  have hss := selfScale_nonneg (d := d) (s := (d : ℝ) - 2) ht (by linarith)
  by_cases hsm : KernelGrad.tdist x 0 < δ / 2
  · set x' : Euc d := KernelGrad.centeredRep x with hx'
    have hn : ‖x'‖ = KernelGrad.tdist x 0 := EnergyAux.norm_centeredRep_eq x
    have hmk : Torus.mk x' = x := KernelGrad.mk_centeredRep x
    have hx'0 : x' ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; linarith
    have h1 := hloc x' (by rw [hn]; linarith) hx'0
    rw [hmk, hker x hx0, hn] at h1
    have h2 : |r x| ≤ |R| := by
      have := hR x' (by simpa [Metric.mem_closedBall, dist_zero_right, hn] using hsm.le)
      have e : Torus.lift r x' = r x := by simp [Torus.lift, hmk]
      rw [e] at this
      exact (Real.norm_eq_abs _ ▸ this).trans (le_abs_self _)
    have h3 : sliceG d 0 x = c⁻¹ * (selfScale d ((d : ℝ) - 2) (KernelGrad.tdist x 0) + r x) := by
      field_simp; linarith
    rw [h3]
    have h6 := mul_le_mul_of_nonneg_left ((le_abs_self (r x)).trans h2) (inv_pos.mpr hc).le
    have h7 := abs_nonneg B
    nlinarith [h6, h7]
  · push Not at hsm
    have := (abs_le.mp (hB x hsm)).2
    have h4 : 0 ≤ c⁻¹ * selfScale d ((d : ℝ) - 2) (KernelGrad.tdist x 0) := mul_nonneg (inv_pos.mpr hc).le hss
    have h5 : 0 ≤ c⁻¹ * |R| := by positivity
    have := le_abs_self B
    linarith

theorem S0_bound (hd : 2 ≤ d) : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 →
    S0 d η ≤ (cC d)⁻¹ * selfScale d ((d : ℝ) - 2) η + C₂ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₂, hC₂, hup⟩ := sliceG0_upper hd
  refine ⟨C₂ + 1, by linarith, fun η hη hη8 => ?_⟩
  have hη2 : η < 1 / 2 := by linarith
  haveI := EnergyAux.isProbabilityMeasure_sphereT hd1 η
  set τ := sphereT d η with hτ
  have hae := EnergyAux.ae_tdist_sphereT hd1 hη hη2
  obtain ⟨B, hB⟩ := EnergyAux.sliceG_bdd_away (d := d) (le_refl (0 : ℝ)) hη
  set κ : ℝ := η ^ 2 / (2 * d) with hκ
  have hκ1 : κ ≤ 1 := by
    rw [hκ, div_le_one (by positivity)]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hκ0 : 0 ≤ κ := by positivity
  have hin : ∀ᵐ x ∂τ, ∫ y, sliceG d 0 (x - y) ∂τ = sliceG d 0 x + κ := by
    filter_upwards [hae] with x hx
    have hx0 : x ≠ 0 := EnergyAux.ne_zero_of_tdist_pos (by rw [hx]; exact hη)
    rw [sliceG0_conv_sphere hd hη hη2 x hx0, EnergyAux.fTrunc0_eq_zero hd hη hx.ge]; ring
  have hbd : ∀ᵐ x ∂τ, |∫ y, sliceG d 0 (x - y) ∂τ| ≤ B + 1 := by
    filter_upwards [hin, hae] with x hx hx2
    rw [hx]
    have := hB x hx2.ge
    calc |sliceG d 0 x + κ| ≤ |sliceG d 0 x| + |κ| := abs_add_le _ _
      _ ≤ B + 1 := by rw [abs_of_nonneg hκ0]; linarith
  have hmeas : AEStronglyMeasurable (fun x : Torus d => ∫ y, sliceG d 0 (x - y) ∂τ) τ := by
    have : StronglyMeasurable (fun p : Torus d × Torus d => sliceG d 0 (p.1 - p.2)) :=
      ((EnergyAux.measurable_sliceG 0).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
    exact (this.integral_prod_right' (ν := τ)).aestronglyMeasurable
  have hint : Integrable (fun x : Torus d => ∫ y, sliceG d 0 (x - y) ∂τ) τ :=
    Integrable.mono' (integrable_const (B + 1)) hmeas (hbd.mono fun x hx => by rwa [Real.norm_eq_abs])
  have hV : ∀ᵐ x ∂τ, ∫ y, sliceG d 0 (x - y) ∂τ ≤ (cC d)⁻¹ * selfScale d ((d : ℝ) - 2) η + C₂ + 1 := by
    filter_upwards [hin, hae] with x hx hx2
    rw [hx]
    have hx0 : x ≠ 0 := EnergyAux.ne_zero_of_tdist_pos (by rw [hx2]; exact hη)
    have := hup x (by rw [hx2]; exact hη8) hx0
    rw [hx2] at this
    linarith
  unfold S0
  calc ∫ x, ∫ y, sliceG d 0 (x - y) ∂τ ∂τ ≤ ∫ x, ((cC d)⁻¹ * selfScale d ((d : ℝ) - 2) η + C₂ + 1) ∂τ :=
        integral_mono_ae hint (integrable_const _) hV
    _ = (cC d)⁻¹ * selfScale d ((d : ℝ) - 2) η + (C₂ + 1) := by
        rw [integral_const]; simp; ring

theorem sgv0_bound (hd : 2 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Torus d, z ≠ 0 →
    ‖SliceAux.sgv 0 z‖ ≤ K * (((KernelGrad.tdist z 0) ^ (d - 1))⁻¹ + 1) := by
  have hc : 0 < cC d := cC_pos hd
  have hgrad := fun x hx => coulomb_grad_c hd x hx
  set c := cC d with hcdef
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  obtain ⟨C, hC⟩ := KernelGrad.periodicRieszGrad_bound_tdist hd hs0 hsd
  refine ⟨c⁻¹ * |C|, by positivity, fun z hz => ?_⟩
  have h1 := hC z hz
  have h2 := hgrad z hz
  have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
  have e : KernelGrad.tdist z 0 ^ (-((d : ℝ) - 2) - 1) = ((KernelGrad.tdist z 0) ^ (d - 1))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]; ring
  rw [e] at h1
  have h3 : ‖SliceAux.sgv 0 z‖ = c⁻¹ * ‖periodicRieszGrad d ((d : ℝ) - 2) z‖ := by
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos hc]; field_simp
  rw [h3]
  have h4 : 0 ≤ ((KernelGrad.tdist z 0) ^ (d - 1))⁻¹ + 1 := by positivity
  calc c⁻¹ * ‖periodicRieszGrad d ((d : ℝ) - 2) z‖ ≤ c⁻¹ * (C * (((KernelGrad.tdist z 0) ^ (d - 1))⁻¹ + 1)) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hc).le
    _ ≤ c⁻¹ * (|C| * (((KernelGrad.tdist z 0) ^ (d - 1))⁻¹ + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) h4) (inv_pos.mpr hc).le
    _ = c⁻¹ * |C| * (((KernelGrad.tdist z 0) ^ (d - 1))⁻¹ + 1) := by ring

theorem radial_int_bound (hd : 2 ≤ d) {K : ℝ} (hK : 0 ≤ K) (a : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    {g : Torus d → ℝ} (hg0 : ∀ z, 0 ≤ g z) (hgm : Measurable g)
    (hg : ∀ z : Torus d, z ≠ 0 → g z ≤ if KernelGrad.tdist z 0 ≤ ρ then
      KernelGrad.tdist z 0 ^ a * (K * (((KernelGrad.tdist z 0) ^ (d - 1))⁻¹ + 1)) else 0) :
    ∫ z, g z ≤ ((volume : Measure (Euc d)).toSphere univ).toReal * (2 * K * ρ ^ (a + 1)) := by
  have hd1 : 1 ≤ d := by omega
  set S : ℝ≥0∞ := (volume : Measure (Euc d)).toSphere univ with hS
  have hSt : S ≠ ⊤ := measure_ne_top _ _
  set F : ℝ → ℝ≥0∞ := fun r => if r ≤ ρ then ENNReal.ofReal (r ^ a * (K * ((r ^ (d - 1))⁻¹ + 1))) else 0 with hF
  have hFm : Measurable F := by
    refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ measurable_const
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_id.pow_const _).mul (measurable_const.mul (((measurable_id.pow_const _).inv).add measurable_const))
  have hF0 : ∀ r, 1 / 3 ≤ r → F r = 0 := fun r hr => by
    simp only [hF]; rw [if_neg (by linarith)]
  have h1 : ∫⁻ z : Torus d, ENNReal.ofReal (g z) ≤ ∫⁻ z : Torus d, F (KernelGrad.tdist z 0) := by
    refine lintegral_mono_ae ?_
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with z hz
    have := hg z hz
    simp only [hF]
    by_cases hzρ : KernelGrad.tdist z 0 ≤ ρ
    · rw [if_pos hzρ]; rw [if_pos hzρ] at this
      exact ENNReal.ofReal_le_ofReal this
    · rw [if_neg hzρ]; rw [if_neg hzρ] at this
      have := le_antisymm this (hg0 z)
      rw [this]; simp
  rw [lintegral_torus_radial hd1 (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2) F hFm hF0] at h1
  have h2 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) * F t ≤ ENNReal.ofReal (2 * K * ρ ^ a) * ENNReal.ofReal ρ := by
    calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) * F t
        ≤ ∫⁻ t in Ioi (0 : ℝ), (Ioc 0 ρ).indicator (fun _ => ENNReal.ofReal (2 * K * ρ ^ a)) t := by
          refine setLIntegral_mono (measurable_const.indicator measurableSet_Ioc) fun t ht => ?_
          have ht0 : 0 < t := ht
          by_cases htρ : t ≤ ρ
          · rw [indicator_of_mem (show t ∈ Ioc 0 ρ from ⟨ht0, htρ⟩)]
            simp only [hF, if_pos htρ]
            rw [← ENNReal.ofReal_mul (pow_nonneg ht0.le _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hp : t ^ (d - 1) * (t ^ (d - 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_pos ht0 _).ne'
            have hp1 : t ^ (d - 1) ≤ 1 := pow_le_one₀ ht0.le (by linarith)
            have hta : t ^ a ≤ ρ ^ a := pow_le_pow_left₀ ht0.le htρ a
            have hpos : 0 ≤ t ^ (d - 1) := pow_nonneg ht0.le _
            calc t ^ (d - 1) * (t ^ a * (K * ((t ^ (d - 1))⁻¹ + 1)))
                = t ^ a * K * (t ^ (d - 1) * (t ^ (d - 1))⁻¹ + t ^ (d - 1)) := by ring
              _ = t ^ a * K * (1 + t ^ (d - 1)) := by rw [hp]
              _ ≤ ρ ^ a * K * 2 := by
                  have : 1 + t ^ (d - 1) ≤ 2 := by linarith
                  have h5 : 0 ≤ t ^ a * K := mul_nonneg (pow_nonneg ht0.le _) hK
                  calc t ^ a * K * (1 + t ^ (d - 1)) ≤ t ^ a * K * 2 := mul_le_mul_of_nonneg_left this h5
                    _ ≤ ρ ^ a * K * 2 := by nlinarith [mul_le_mul_of_nonneg_right hta hK]
              _ = 2 * K * ρ ^ a := by ring
          · rw [indicator_of_notMem (show t ∉ Ioc 0 ρ from fun h => htρ h.2)]
            simp only [hF, if_neg htρ]; simp
      _ = ENNReal.ofReal (2 * K * ρ ^ a) * ENNReal.ofReal ρ := by
          rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc, lintegral_const]
          have : Ioc 0 ρ ∩ Ioi 0 = Ioc 0 ρ := by
            ext t; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; tauto
          rw [this, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
          simp
  have h3 : ∫⁻ z : Torus d, ENNReal.ofReal (g z) ≤ S * (ENNReal.ofReal (2 * K * ρ ^ a) * ENNReal.ofReal ρ) :=
    h1.trans (mul_le_mul_right h2 S)
  have hfin : S * (ENNReal.ofReal (2 * K * ρ ^ a) * ENNReal.ofReal ρ) ≠ ⊤ :=
    ENNReal.mul_ne_top hSt (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgm.aestronglyMeasurable]
  have := ENNReal.toReal_mono hfin h3
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hρ.le]
  ring

theorem Wb0_bound (hd : 2 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 4 → Wb d 0 ρ ≤ K * ρ := by
  obtain ⟨K0, hK0, hK⟩ := sgv0_bound hd
  refine ⟨((volume : Measure (Euc d)).toSphere univ).toReal * (2 * K0), by positivity, fun ρ hρ hρ4 => ?_⟩
  have := radial_int_bound hd hK0 0 hρ hρ4 (g := fun z : Torus d =>
      if KernelGrad.tdist z 0 ≤ ρ then ‖SliceAux.sgv 0 z‖ else 0)
    (fun z => by split_ifs <;> positivity)
    (Measurable.ite (measurableSet_le EnergyAux.measurable_tdist_zero measurable_const)
      (measurable_sgv_l 0).norm measurable_const)
    (fun z hz => by
      by_cases h : KernelGrad.tdist z 0 ≤ ρ
      · simp only [if_pos h, pow_zero, one_mul]; exact hK z hz
      · simp only [if_neg h]; exact le_rfl)
  unfold Wb
  refine this.trans (le_of_eq ?_)
  ring

theorem Wt0_bound (hd : 2 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 4 → Wt d 0 ρ ≤ K * ρ ^ 2 := by
  obtain ⟨K0, hK0, hK⟩ := sgv0_bound hd
  refine ⟨((volume : Measure (Euc d)).toSphere univ).toReal * (2 * K0), by positivity, fun ρ hρ hρ4 => ?_⟩
  have := radial_int_bound hd hK0 1 hρ hρ4 (g := fun z : Torus d =>
      if KernelGrad.tdist z 0 ≤ ρ then KernelGrad.tdist z 0 * ‖SliceAux.sgv 0 z‖ else 0)
    (fun z => by
      split_ifs
      · exact mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)
      · exact le_rfl)
    (Measurable.ite (measurableSet_le EnergyAux.measurable_tdist_zero measurable_const)
      (EnergyAux.measurable_tdist_zero.mul (measurable_sgv_l 0).norm) measurable_const)
    (fun z hz => by
      by_cases h : KernelGrad.tdist z 0 ≤ ρ
      · simp only [if_pos h, pow_one]
        exact mul_le_mul_of_nonneg_left (hK z hz) (KernelGrad.tdist_nonneg z 0)
      · simp only [if_neg h]; exact le_rfl)
  unfold Wt
  refine this.trans (le_of_eq ?_)
  ring

theorem annulus_w2_bound (hd : 2 ≤ d) : ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
    ∫ z : Torus d, (if r / 2 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < r then ‖SliceAux.sgv 0 z‖ ^ 2 else 0) ≤
      Cw * (r * (r ^ (d - 1))⁻¹) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨K, hK0, hK⟩ := sgv0_bound hd
  refine ⟨((volume : Measure (Euc d)).toSphere univ).toReal * (2 ^ d * K ^ 2), by positivity, fun r hr hr4 => ?_⟩
  set S : ℝ≥0∞ := (volume : Measure (Euc d)).toSphere univ with hS
  have hSt : S ≠ ⊤ := measure_ne_top _ _
  set g : Torus d → ℝ := fun z => if r / 2 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < r then ‖SliceAux.sgv 0 z‖ ^ 2 else 0 with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => by simp only [hg]; split_ifs <;> positivity
  have hgm : Measurable g := by
    refine Measurable.ite ((measurableSet_lt measurable_const EnergyAux.measurable_tdist_zero).inter
      (measurableSet_lt EnergyAux.measurable_tdist_zero measurable_const)) ?_ measurable_const
    exact (measurable_sgv_l 0).norm.pow_const 2
  set F : ℝ → ℝ≥0∞ := fun t => if r / 2 < t ∧ t < r then ENNReal.ofReal ((K * ((t ^ (d - 1))⁻¹ + 1)) ^ 2) else 0 with hF
  have hFm : Measurable F := by
    refine Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)) ?_ measurable_const
    refine ENNReal.measurable_ofReal.comp ?_
    exact (measurable_const.mul (((measurable_id.pow_const _).inv).add measurable_const)).pow_const 2
  have hF0 : ∀ t, 1 / 3 ≤ t → F t = 0 := fun t ht => by
    simp only [hF]; rw [if_neg]; intro h; linarith [h.2]
  have h1 : ∫⁻ z : Torus d, ENNReal.ofReal (g z) ≤ ∫⁻ z : Torus d, F (KernelGrad.tdist z 0) := by
    refine lintegral_mono_ae ?_
    filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with z hz
    simp only [hg, hF]
    by_cases hc : r / 2 < KernelGrad.tdist z 0 ∧ KernelGrad.tdist z 0 < r
    · rw [if_pos hc, if_pos hc]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hK z hz
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    · simp [hc]
  rw [lintegral_torus_radial hd1 (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2) F hFm hF0] at h1
  have hr20 : 0 < r / 2 := by linarith
  have h2 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) * F t ≤
      ENNReal.ofReal (4 * K ^ 2 * ((r / 2) ^ (d - 1))⁻¹) * ENNReal.ofReal (r / 2) := by
    calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) * F t
        ≤ ∫⁻ t in Ioi (0 : ℝ), (Ioo (r / 2) r).indicator
            (fun _ => ENNReal.ofReal (4 * K ^ 2 * ((r / 2) ^ (d - 1))⁻¹)) t := by
          refine setLIntegral_mono (measurable_const.indicator measurableSet_Ioo) fun t ht => ?_
          have ht0 : 0 < t := ht
          by_cases htr : r / 2 < t ∧ t < r
          · rw [indicator_of_mem (show t ∈ Ioo (r / 2) r from htr)]
            simp only [hF, if_pos htr]
            rw [← ENNReal.ofReal_mul (pow_nonneg ht0.le _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hp : t ^ (d - 1) * (t ^ (d - 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_pos ht0 _).ne'
            have hp1 : t ^ (d - 1) ≤ 1 := pow_le_one₀ ht0.le (by linarith [htr.2])
            have hpos : 0 < t ^ (d - 1) := pow_pos ht0 _
            have hinv : (t ^ (d - 1))⁻¹ ≤ ((r / 2) ^ (d - 1))⁻¹ :=
              inv_anti₀ (pow_pos hr20 _) (pow_le_pow_left₀ hr20.le htr.1.le _)
            calc t ^ (d - 1) * (K * ((t ^ (d - 1))⁻¹ + 1)) ^ 2
                = K ^ 2 * (t ^ (d - 1))⁻¹ * (1 + t ^ (d - 1)) ^ 2 := by
                  field_simp
              _ ≤ K ^ 2 * ((r / 2) ^ (d - 1))⁻¹ * 4 := by
                  have h4 : (1 + t ^ (d - 1)) ^ 2 ≤ 4 := by nlinarith
                  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
                  calc K ^ 2 * (t ^ (d - 1))⁻¹ * (1 + t ^ (d - 1)) ^ 2
                      ≤ K ^ 2 * ((r / 2) ^ (d - 1))⁻¹ * (1 + t ^ (d - 1)) ^ 2 :=
                        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hK2) (sq_nonneg _)
                    _ ≤ K ^ 2 * ((r / 2) ^ (d - 1))⁻¹ * 4 :=
                        mul_le_mul_of_nonneg_left h4 (by positivity)
              _ = 4 * K ^ 2 * ((r / 2) ^ (d - 1))⁻¹ := by ring
          · rw [indicator_of_notMem (show t ∉ Ioo (r / 2) r from fun h => htr h)]
            simp only [hF, if_neg htr]; simp
      _ = ENNReal.ofReal (4 * K ^ 2 * ((r / 2) ^ (d - 1))⁻¹) * ENNReal.ofReal (r / 2) := by
          rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo, lintegral_const]
          have : Ioo (r / 2) r ∩ Ioi 0 = Ioo (r / 2) r := by
            ext t; simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
            constructor
            · intro h; exact h.1
            · intro h; exact ⟨h, by linarith [h.1]⟩
          rw [this, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
          congr 2; ring
  have h3 : ∫⁻ z : Torus d, ENNReal.ofReal (g z) ≤
      S * (ENNReal.ofReal (4 * K ^ 2 * ((r / 2) ^ (d - 1))⁻¹) * ENNReal.ofReal (r / 2)) :=
    h1.trans (mul_le_mul_right h2 S)
  have hfin : S * (ENNReal.ofReal (4 * K ^ 2 * ((r / 2) ^ (d - 1))⁻¹) * ENNReal.ofReal (r / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top hSt (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgm.aestronglyMeasurable]
  have := ENNReal.toReal_mono hfin h3
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hr20.le]
  have hp2 : ((r / 2) ^ (d - 1))⁻¹ = 2 ^ (d - 1) * (r ^ (d - 1))⁻¹ := by
    rw [div_pow, inv_div, div_eq_mul_inv, mul_comm]
  rw [hp2]
  have : (2 : ℝ) ^ d = 2 * 2 ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [this]
  ring

end HRS.Commutator.Renorm
