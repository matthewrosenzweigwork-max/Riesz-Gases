import HRS.Energy.Commutator.EnergyAux

/-!
# Energy identity for the Coulomb slice (packet CM-S3, helpers)

Lower bound and evenness of `𝒢_0`, the surface charge `sphereT`, integrability of `𝒢_0(w - ·)`
against it (Newton's identity at larger radii plus Fatou), and the bookkeeping of
`energy_identity_coulomb`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux
open scoped Pointwise

namespace HRS.Commutator.EnergyAux

variable {d : ℕ}

/-! ### Elementary properties of the slice kernel -/

theorem cosMode_neg' (k : Lattice d) (x : Torus d) : Torus.cosMode k (-x) = Torus.cosMode k x :=
  HRS.cosMode_neg k x

theorem psiFn_neg' (x : Torus d) (u : ℝ) : psiFn (-x) u = psiFn x u := by
  unfold psiFn
  simp only [cosMode_neg']

theorem sliceG_neg (l : ℝ) (x : Torus d) : sliceG d l (-x) = sliceG d l x := by
  unfold sliceG
  simp only [psiFn_neg']

/-- Uniform lower bound of `Ψ`. -/
theorem psiFn_ge_neg_exp (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : Torus d) (u : ℝ), 0 < u → -K * Real.exp (-u) ≤ psiFn x u := by
  set G := ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) with hG
  have hG0 : 0 ≤ G := tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨Real.exp 1 * G + Real.exp 1, by positivity, fun x u hu => ?_⟩
  rcases le_total 1 u with h1 | h1
  · have hb : ∀ k : Lattice d, ‖if k = 0 then 0 else Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x‖
        ≤ Real.exp (-u) * Real.exp 1 * Real.exp (-1 * Lattice.enorm k ^ 2) := by
      intro k
      by_cases hk : k = 0
      · simp only [hk, ite_true, norm_zero]; positivity
      · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hm := one_le_enorm k hk
        calc Real.exp (-u * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
            ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
          _ = Real.exp (-u * Lattice.enorm k ^ 2) := mul_one _
          _ ≤ Real.exp (-u + 1 + -1 * Lattice.enorm k ^ 2) := by
              apply Real.exp_le_exp.mpr
              nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (show (1:ℝ) ≤ Lattice.enorm k ^ 2 by nlinarith))]
          _ = _ := by rw [Real.exp_add, Real.exp_add]
    have hsum := ((summable_gauss_lattice d 1 one_pos).mul_left
      (Real.exp (-u) * Real.exp 1)).hasSum
    have h2 := tsum_of_norm_bounded hsum hb
    rw [tsum_mul_left, ← hG] at h2
    have h3 : |psiFn x u| ≤ Real.exp (-u) * Real.exp 1 * G := by
      rw [← Real.norm_eq_abs]; exact h2
    have h4 := (abs_le.mp h3).1
    have : 0 ≤ Real.exp 1 * Real.exp (-u) := by positivity
    nlinarith [Real.exp_pos (-u), Real.exp_pos 1]
  · have h2 := one_add_psiFn_nonneg' x hu
    have h5 : 1 ≤ Real.exp 1 * Real.exp (-u) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; linarith
    have : 0 ≤ Real.exp 1 * G * Real.exp (-u) := by positivity
    nlinarith

/-- `𝒢_0` is bounded below. -/
theorem sliceG_zero_lower (d : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Torus d, -M ≤ sliceG d 0 x := by
  obtain ⟨K, hK0, hK⟩ := psiFn_ge_neg_exp d
  have hb : 0 < 4 * Real.pi ^ 2 := by positivity
  refine ⟨K / (4 * Real.pi ^ 2), by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    have h1 : 0 ≤ sliceG d 0 (0 : Torus d) := by
      unfold sliceG
      exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (Real.exp_pos _).le (CoercAux.psi_zero_nonneg (by have : (0 : ℝ) < t := ht; positivity))
    have : 0 ≤ K / (4 * Real.pi ^ 2) := by positivity
    linarith
  · have hI := SliceAux.integrableOn_slice_psi (le_refl (0 : ℝ)) hx
    have hE : IntegrableOn (fun t : ℝ => K * Real.exp (-(4 * Real.pi ^ 2 * t))) (Ioi 0) := by
      have := integrableOn_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) (0 : ℝ)
      have h2 : IntegrableOn (fun t : ℝ => K * Real.exp (-(4 * Real.pi ^ 2) * t)) (Ioi 0) :=
        this.const_mul K
      refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp [neg_mul]
    have hint : ∫ t in Ioi (0 : ℝ), K * Real.exp (-(4 * Real.pi ^ 2 * t)) = K / (4 * Real.pi ^ 2) := by
      rw [integral_const_mul]
      have := integral_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) (0 : ℝ)
      simp only [neg_mul, mul_zero, Real.exp_zero] at this ⊢
      rw [this]; field_simp
    have hle : ∫ t in Ioi (0 : ℝ), -(K * Real.exp (-(4 * Real.pi ^ 2 * t))) ≤ sliceG d 0 x := by
      unfold sliceG
      refine setIntegral_mono_on hE.neg ?_ measurableSet_Ioi fun t ht => ?_
      · simpa using hI
      · have ht' : (0 : ℝ) < t := ht
        have := hK x (4 * Real.pi ^ 2 * t) (by positivity)
        simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
        linarith [this]
    rw [integral_neg, hint] at hle
    exact hle

theorem mk_ne_zero_of_box {w : Euc d} (hw : ∀ i, |w i| ≤ 1 / 2) (hw0 : w ≠ 0) : Torus.mk w ≠ 0 := by
  intro h
  apply hw0
  obtain ⟨m, hm⟩ := SliceAux.exists_lattice_of_mk_eq (x := w) (y := 0) (by
    rw [h]; funext i; simp [Torus.mk])
  ext i
  have h2 : w i = (m i : ℝ) := by rw [hm]; simp [Lattice.toEuc]
  have h3 : |(m i : ℝ)| ≤ 1 / 2 := by rw [← h2]; exact hw i
  have h4 : m i = 0 := by
    have h5 : |m i| < 1 := by
      have : |(m i : ℝ)| < 1 := by linarith
      exact_mod_cast this
    have := abs_lt.mp h5
    omega
  simp [h2, h4]

theorem sliceG_bdd_away {l : ℝ} (hl : 0 ≤ l) {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, ∀ z : Torus d, δ ≤ KernelGrad.tdist z 0 → |sliceG d l z| ≤ B := by
  set K : Set (Euc d) := {w | (∀ i, |w i| ≤ 1 / 2) ∧ δ ≤ ‖w‖} with hK
  have hKc : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Euc d) d) ?_ ?_
    · have h1 : IsClosed {w : Euc d | ∀ i, |w i| ≤ 1 / 2} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i =>
          isClosed_le ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).abs continuous_const
      exact h1.inter (isClosed_le continuous_const continuous_norm)
    · intro w hw
      have : ‖w‖ ≤ d := by
        rw [EuclideanSpace.norm_eq]
        have h2 : ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have := hw.1 i
          nlinarith [abs_nonneg (w i), sq_abs (w i)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h2
        refine (Real.sqrt_le_sqrt h2).trans ?_
        rw [Real.sqrt_le_left (by positivity)]
        have : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h0
            nlinarith
        exact this
      simpa using this
  have hc : ContinuousOn (fun y : Euc d => sliceG d l (Torus.mk y)) K := by
    intro w hw
    refine (sliceG_continuousAt_lift hl ?_).continuousWithinAt
    refine mk_ne_zero_of_box hw.1 ?_
    intro h0
    have := hw.2
    rw [h0] at this
    simp at this
    linarith
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc
  refine ⟨C, fun z hz => ?_⟩
  have hw : KernelGrad.centeredRep z ∈ K := by
    refine ⟨fun i => KernelGrad.abs_centeredRep_le z i, ?_⟩
    rw [norm_centeredRep_eq]; exact hz
  have := hC _ hw
  rw [KernelGrad.mk_centeredRep] at this
  simpa using this

/-! ### The surface charge -/

theorem lintegral_sphereT (η : ℝ) {F : Torus d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(sphereT d η) =
      ((volume : Measure (Euc d)).toSphere Set.univ)⁻¹ *
        ∫⁻ ω : Metric.sphere (0 : Euc d) 1, F (Torus.mk (η • (ω : Euc d)))
          ∂((volume : Measure (Euc d)).toSphere) := by
  unfold sphereT
  rw [lintegral_map hF HRS.Torus.continuous_mk.measurable, lintegral_smul_measure]
  have := lintegral_map (μ := (volume : Measure (Euc d)).toSphere)
    (hF.comp HRS.Torus.continuous_mk.measurable) (measurable_sphere_smul η)
  simp only [smul_eq_mul]
  rw [show (∫⁻ a : Euc d, F (Torus.mk a) ∂Measure.map (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))
    (volume : Measure (Euc d)).toSphere) = _ from this]
  rfl

theorem toSphere_univ_pos (hd : 1 ≤ d) : (volume : Measure (Euc d)).toSphere Set.univ ≠ 0 := by
  rw [Measure.toSphere_apply_univ]
  have h1 : (Module.finrank ℝ (Euc d) : ℝ≥0∞) ≠ 0 := by
    rw [finrank_euclideanSpace_fin]; exact_mod_cast (by omega : d ≠ 0)
  exact mul_ne_zero h1 (Metric.measure_ball_pos _ _ one_pos).ne'

theorem sphereT_univ (hd : 1 ≤ d) (η : ℝ) : sphereT d η Set.univ = 1 := by
  unfold sphereT
  rw [Measure.map_apply HRS.Torus.continuous_mk.measurable MeasurableSet.univ, Set.preimage_univ,
    Measure.smul_apply, Measure.map_apply (measurable_sphere_smul η) MeasurableSet.univ, Set.preimage_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (toSphere_univ_pos hd) (measure_ne_top _ _)

theorem isProbabilityMeasure_sphereT (hd : 1 ≤ d) (η : ℝ) : IsProbabilityMeasure (sphereT d η) :=
  ⟨sphereT_univ hd η⟩

theorem ae_tdist_sphereT (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∀ᵐ x ∂(sphereT d η), KernelGrad.tdist x 0 = η := by
  have hms : MeasurableSet {x : Torus d | KernelGrad.tdist x 0 = η} :=
    measurableSet_eq_fun measurable_tdist_zero measurable_const
  have hms' : MeasurableSet {a : Torus d | ¬KernelGrad.tdist a 0 = η} := hms.compl
  rw [ae_iff]
  unfold sphereT
  rw [Measure.map_apply HRS.Torus.continuous_mk.measurable hms',
    Measure.smul_apply, Measure.map_apply (measurable_sphere_smul η)
      (HRS.Torus.continuous_mk.measurable hms')]
  have : (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) ⁻¹'
      (Torus.mk ⁻¹' {x : Torus d | ¬KernelGrad.tdist x 0 = η}) = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    have hn : ‖η • (ω : Euc d)‖ = η := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      have : ‖(ω : Euc d)‖ = 1 := by simpa using ω.2
      rw [this, mul_one]
    rw [KernelGrad.tdist_mk, hn]
    intro i
    have := abs_apply_le_norm (η • (ω : Euc d)) i
    rw [hn] at this
    linarith
  rw [this]; simp

theorem newton_anti (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : newton d b ≤ newton d a := by
  unfold newton
  split_ifs with h2
  · have : Real.log a ≤ Real.log b := Real.log_le_log ha hab
    have hc : 0 ≤ 1 / (2 * Real.pi) := by positivity
    nlinarith
  · have hd3 : (3 : ℝ) ≤ d := by
      have : d ≠ 2 := h2
      have : 3 ≤ d := by omega
      exact_mod_cast this
    have hG : 0 < Real.Gamma ((d : ℝ) / 2 - 1) := Real.Gamma_pos_of_pos (by linarith)
    have hc : 0 < Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.pi ^ ((d : ℝ) / 2)) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    exact Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

theorem fTrunc0_eq_zero (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) {z : Torus d}
    (hz : η ≤ KernelGrad.tdist z 0) : fTrunc0 d η z = 0 := by
  unfold fTrunc0
  rw [norm_centeredRep_eq]
  have := newton_anti hd hη hz
  exact max_eq_right (by linarith)

theorem fTrunc0_nonneg (z : Torus d) {η : ℝ} : 0 ≤ fTrunc0 d η z := le_max_right _ _


theorem toSphere_singleton_null (hd : 2 ≤ d) (ω : Metric.sphere (0 : Euc d) 1) :
    (volume : Measure (Euc d)).toSphere {ω} = 0 := by
  rw [Measure.toSphere_apply' _ (measurableSet_singleton ω)]
  have hsub : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ({ω} : Set (Metric.sphere (0 : Euc d) 1))) ⊆
      (Submodule.span ℝ {(ω : Euc d)} : Submodule ℝ (Euc d)) := by
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    have hxω : x = ω := hx
    subst hxω
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hne : (Submodule.span ℝ {(ω : Euc d)} : Submodule ℝ (Euc d)) ≠ ⊤ := by
    intro h
    have hω0 : (ω : Euc d) ≠ 0 := by
      intro h0
      have : ‖(ω : Euc d)‖ = 1 := by simpa using ω.2
      rw [h0] at this; simp at this
    have h1 := finrank_span_singleton (K := ℝ) hω0
    rw [h, finrank_top, finrank_euclideanSpace_fin] at h1
    omega
  have h0 := Measure.addHaar_submodule (volume : Measure (Euc d)) _ hne
  rw [measure_mono_null hsub h0]; simp


theorem sphereT_singleton_null (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (w : Torus d) :
    sphereT d η {w} = 0 := by
  have hms : MeasurableSet ({w} : Set (Torus d)) := measurableSet_singleton _
  set Z : Set (Metric.sphere (0 : Euc d) 1) := {ω | Torus.mk (η • (ω : Euc d)) = w} with hZ
  have hZm : MeasurableSet Z :=
    (measurableSet_singleton w).preimage
      (HRS.Torus.continuous_mk.measurable.comp (measurable_sphere_smul η))
  have hsub : Z.Subsingleton := by
    intro ω₁ h₁ ω₂ h₂
    have h12 : Torus.mk (η • (ω₁ : Euc d) - η • (ω₂ : Euc d)) = 0 := by
      rw [KernelGrad.mk_sub]
      have : Torus.mk (η • (ω₁ : Euc d)) = Torus.mk (η • (ω₂ : Euc d)) := h₁.trans h₂.symm
      rw [this, sub_self]
    have hn : ‖η • (ω₁ : Euc d) - η • (ω₂ : Euc d)‖ < 1 := by
      have e1 : ‖η • (ω₁ : Euc d)‖ = η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
        have : ‖(ω₁ : Euc d)‖ = 1 := by simpa using ω₁.2
        rw [this, mul_one]
      have e2 : ‖η • (ω₂ : Euc d)‖ = η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
        have : ‖(ω₂ : Euc d)‖ = 1 := by simpa using ω₂.2
        rw [this, mul_one]
      calc _ ≤ ‖η • (ω₁ : Euc d)‖ + ‖η • (ω₂ : Euc d)‖ := norm_sub_le _ _
        _ < 1 := by rw [e1, e2]; linarith
    have h0 := mk_eq_zero_of_norm_lt_one h12 hn
    have : η • (ω₁ : Euc d) = η • (ω₂ : Euc d) := sub_eq_zero.mp h0
    exact Subtype.ext (smul_right_injective (Euc d) hη.ne' this)
  have hPZ : (volume : Measure (Euc d)).toSphere Z = 0 := by
    by_cases hne : Z.Nonempty
    · obtain ⟨ω₁, h₁⟩ := hne
      have : Z ⊆ {ω₁} := fun ω hω => hsub hω h₁
      exact measure_mono_null this (toSphere_singleton_null hd ω₁)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  have hF : Measurable (({w} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hms
  have h0 : ∫⁻ x, ({w} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) x ∂(sphereT d η) =
      sphereT d η {w} := by
    rw [lintegral_indicator hms]; simp
  rw [← h0, lintegral_sphereT η hF]
  have : ∫⁻ ω : Metric.sphere (0 : Euc d) 1,
      ({w} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk (η • (ω : Euc d)))
        ∂((volume : Measure (Euc d)).toSphere) = 0 := by
    have : (fun ω : Metric.sphere (0 : Euc d) 1 =>
        ({w} : Set (Torus d)).indicator (fun _ => (1 : ℝ≥0∞)) (Torus.mk (η • (ω : Euc d)))) =
        Z.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      simp only [hZ, Set.indicator, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [this, lintegral_indicator hZm]
    simp [hPZ]
  rw [this]; simp


theorem abs_tdist_sub_le (a b : Torus d) :
    |KernelGrad.tdist a 0 - KernelGrad.tdist b 0| ≤ KernelGrad.tdist (a - b) 0 := by
  have h1 := tdist_add_le (a - b) b
  rw [sub_add_cancel] at h1
  have h2 := tdist_add_le a (-(a - b))
  rw [KernelGrad.tdist_neg, show a + -(a - b) = b by abel] at h2
  rw [abs_le]; constructor <;> linarith

theorem lintegral_G0_lt_top_off (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) {M : ℝ}
    {w : Torus d} (hw : KernelGrad.tdist w 0 ≠ η) :
    ∫⁻ y, ENNReal.ofReal (sliceG d 0 (w - y) + M) ∂(sphereT d η) < ⊤ := by
  have h1 : 1 ≤ d := by omega
  haveI := isProbabilityMeasure_sphereT h1 η
  have hδ : 0 < |KernelGrad.tdist w 0 - η| := abs_pos.mpr (sub_ne_zero.mpr hw)
  obtain ⟨B, hB⟩ := sliceG_bdd_away (d := d) (le_refl (0 : ℝ)) hδ
  have hae := ae_tdist_sphereT h1 hη hη2
  calc ∫⁻ y, ENNReal.ofReal (sliceG d 0 (w - y) + M) ∂(sphereT d η)
      ≤ ∫⁻ _y, ENNReal.ofReal (B + M) ∂(sphereT d η) := by
        refine lintegral_mono_ae (hae.mono fun y hy => ?_)
        refine ENNReal.ofReal_le_ofReal ?_
        have := hB (w - y) (by
          have := abs_tdist_sub_le w y
          rw [hy] at this; exact this)
        have := (abs_le.mp this).2
        linarith
    _ < ⊤ := by simp


theorem integrable_of_lintegral_lt_top {μ : Measure (Torus d)} {f : Torus d → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤) : Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) h
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_of_nonneg (hf0 x)]

theorem lintegral_G0_newton_off (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) {M : ℝ}
    (hM : ∀ x, 0 ≤ sliceG d 0 x + M) {w : Torus d} (hw : KernelGrad.tdist w 0 ≠ η)
    (hwη : η ≤ KernelGrad.tdist w 0) :
    ∫⁻ y, ENNReal.ofReal (sliceG d 0 (w - y) + M) ∂(sphereT d η) =
      ENNReal.ofReal (sliceG d 0 w + η ^ 2 / (2 * d) + M) := by
  have h1 : 1 ≤ d := by omega
  haveI := isProbabilityMeasure_sphereT h1 η
  have hw0 : w ≠ 0 := ne_zero_of_tdist_pos (lt_of_lt_of_le hη hwη)
  have hfin := lintegral_G0_lt_top_off hd hη hη2 (M := M) hw
  have hmeas : Measurable fun y : Torus d => sliceG d 0 (w - y) + M :=
    ((measurable_sliceG 0).comp (measurable_const.sub measurable_id)).add measurable_const
  have hint : Integrable (fun y : Torus d => sliceG d 0 (w - y) + M) (sphereT d η) :=
    integrable_of_lintegral_lt_top hmeas (fun y => hM _) hfin
  have hint0 : Integrable (fun y : Torus d => sliceG d 0 (w - y)) (sphereT d η) := by
    have := hint.sub (integrable_const M)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => hM _)]
  rw [integral_add hint0 (integrable_const M), sliceG0_conv_sphere hd hη hη2 w hw0,
    fTrunc0_eq_zero hd hη hwη]
  simp


theorem lintegral_G0_lt_top_on (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) {M : ℝ}
    (hM : ∀ x, 0 ≤ sliceG d 0 x + M) {w : Torus d} (hw : KernelGrad.tdist w 0 = η) :
    ∫⁻ y, ENNReal.ofReal (sliceG d 0 (w - y) + M) ∂(sphereT d η) < ⊤ := by
  have h1 : 1 ≤ d := by omega
  have := isProbabilityMeasure_sphereT h1 η
  set wt : Euc d := KernelGrad.centeredRep w with hwt
  have hwtn : ‖wt‖ = η := (norm_centeredRep_eq w).trans hw
  have hmk : Torus.mk wt = w := KernelGrad.mk_centeredRep w
  set ε0 : ℝ := (1 / 2 - η) / (2 * η) with hε0
  have hε0pos : 0 < ε0 := div_pos (by linarith) (by linarith)
  set s : ℕ → ℝ := fun n => 1 + ε0 * (1 / ((n : ℝ) + 1)) with hs
  have hs1 : ∀ n, 1 < s n := fun n => by
    have : 0 < ε0 * (1 / ((n : ℝ) + 1)) := by positivity
    simp only [hs]; linarith
  have hs2 : ∀ n, η * s n < 1 / 2 := fun n => by
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h4 : s n ≤ 1 + ε0 := by
      simp only [hs]
      have := mul_le_mul_of_nonneg_left h3 hε0pos.le
      linarith
    have h5 : η * (1 + ε0) = (η + 1 / 2) / 2 := by
      simp only [hε0]; field_simp; ring
    calc η * s n ≤ η * (1 + ε0) := mul_le_mul_of_nonneg_left h4 hη.le
      _ = (η + 1 / 2) / 2 := h5
      _ < 1 / 2 := by linarith
  have hs_tend : Tendsto s atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε0
    simpa [hs] using (tendsto_const_nhds (x := (1 : ℝ))).add this
  set wn : ℕ → Torus d := fun n => Torus.mk (s n • wt) with hwn
  have hwn_norm : ∀ n, ‖s n • wt‖ = s n * η := fun n => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hs1 n]), hwtn]
  have hwn_td : ∀ n, KernelGrad.tdist (wn n) 0 = η * s n := fun n => by
    simp only [hwn]
    rw [KernelGrad.tdist_mk, hwn_norm, mul_comm]
    intro i
    have := abs_apply_le_norm (s n • wt) i
    rw [hwn_norm] at this
    have := hs2 n
    nlinarith
  obtain ⟨B, hB⟩ := sliceG_bdd_away (d := d) (le_refl (0 : ℝ)) hη
  set F : ℕ → Torus d → ℝ≥0∞ := fun n y => ENNReal.ofReal (sliceG d 0 (wn n - y) + M) with hF
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp (((measurable_sliceG 0).comp (measurable_const.sub measurable_id)).add
      measurable_const)
  have hFb : ∀ n, ∫⁻ y, F n y ∂(sphereT d η) ≤ ENNReal.ofReal (B + η ^ 2 / (2 * d) + M) := by
    intro n
    have hne : KernelGrad.tdist (wn n) 0 ≠ η := by
      rw [hwn_td]
      have := hs1 n
      nlinarith
    have hge : η ≤ KernelGrad.tdist (wn n) 0 := by
      rw [hwn_td]
      have := hs1 n
      nlinarith
    simp only [hF]
    rw [lintegral_G0_newton_off hd hη hη2 hM hne hge]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_le.mp (hB (wn n) hge)).2
    linarith
  have hfat := lintegral_liminf_le (μ := sphereT d η) (u := atTop) hFm
  have hbound : liminf (fun n => ∫⁻ y, F n y ∂(sphereT d η)) atTop ≤
      ENNReal.ofReal (B + η ^ 2 / (2 * d) + M) :=
    Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall hFb).frequently
  have hnull := sphereT_singleton_null hd hη hη2 w
  have hae : ∀ᵐ y ∂(sphereT d η), y ≠ w := by
    rw [ae_iff]; simpa using hnull
  have hlim : ∀ᵐ y ∂(sphereT d η), liminf (fun n => F n y) atTop =
      ENNReal.ofReal (sliceG d 0 (w - y) + M) := by
    filter_upwards [hae] with y hy
    apply Filter.Tendsto.liminf_eq
    set yt : Euc d := KernelGrad.centeredRep y with hyt
    have hymk : Torus.mk yt = y := KernelGrad.mk_centeredRep y
    have hlim0 : w - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    have hlimpt : Torus.mk (wt - yt) ≠ 0 := by
      rw [KernelGrad.mk_sub, hmk, hymk]; exact hlim0
    have hcont := sliceG_continuousAt_lift (d := d) (le_refl (0 : ℝ)) hlimpt
    have hu : Tendsto (fun n => s n • wt - yt) atTop (𝓝 (wt - yt)) := by
      have := (hs_tend.smul_const wt).sub_const yt
      simpa using this
    have hg := hcont.tendsto.comp hu
    have hg2 : Tendsto (fun n => sliceG d 0 (wn n - y) + M) atTop (𝓝 (sliceG d 0 (w - y) + M)) := by
      have e1 : ∀ n, wn n - y = Torus.mk (s n • wt - yt) := fun n => by
        rw [KernelGrad.mk_sub, hymk]
      have e2 : w - y = Torus.mk (wt - yt) := by rw [KernelGrad.mk_sub, hmk, hymk]
      simp only [e1, e2]
      exact (hg.add_const M)
    exact (ENNReal.continuous_ofReal.tendsto _).comp hg2
  calc ∫⁻ y, ENNReal.ofReal (sliceG d 0 (w - y) + M) ∂(sphereT d η)
      = ∫⁻ y, liminf (fun n => F n y) atTop ∂(sphereT d η) := (lintegral_congr_ae (hlim.mono fun y hy => hy.symm))
    _ ≤ _ := hfat
    _ ≤ _ := hbound
    _ < ⊤ := ENNReal.ofReal_lt_top


theorem lintegral_G0_lt_top (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) {M : ℝ}
    (hM : ∀ x, 0 ≤ sliceG d 0 x + M) (w : Torus d) :
    ∫⁻ y, ENNReal.ofReal (sliceG d 0 (w - y) + M) ∂(sphereT d η) < ⊤ := by
  by_cases hw : KernelGrad.tdist w 0 = η
  · exact lintegral_G0_lt_top_on hd hη hη2 hM hw
  · exact lintegral_G0_lt_top_off hd hη hη2 hw

theorem fTrunc0_neg (η : ℝ) (z : Torus d) : fTrunc0 d η (-z) = fTrunc0 d η z := by
  unfold fTrunc0
  rw [norm_centeredRep_eq, norm_centeredRep_eq, KernelGrad.tdist_neg]

theorem lintegral_G0_newton (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) {M : ℝ}
    (hM : ∀ x, 0 ≤ sliceG d 0 x + M) {w : Torus d} (hw0 : w ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (sliceG d 0 (w - y) + M) ∂(sphereT d η) =
      ENNReal.ofReal (sliceG d 0 w - fTrunc0 d η w + η ^ 2 / (2 * d) + M) := by
  have h1 : 1 ≤ d := by omega
  have := isProbabilityMeasure_sphereT h1 η
  have hfin := lintegral_G0_lt_top hd hη hη2 hM w
  have hmeas : Measurable fun y : Torus d => sliceG d 0 (w - y) + M :=
    ((measurable_sliceG 0).comp (measurable_const.sub measurable_id)).add measurable_const
  have hint : Integrable (fun y : Torus d => sliceG d 0 (w - y) + M) (sphereT d η) :=
    integrable_of_lintegral_lt_top hmeas (fun y => hM _) hfin
  have hint0 : Integrable (fun y : Torus d => sliceG d 0 (w - y)) (sphereT d η) := by
    have := hint.sub (integrable_const M)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => hM _)]
  rw [integral_add hint0 (integrable_const M), sliceG0_conv_sphere hd hη hη2 w hw0]
  simp

theorem lintegral_G0_newton' (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) {M : ℝ}
    (hM : ∀ x, 0 ≤ sliceG d 0 x + M) {z : Torus d} (hz0 : z ≠ 0) :
    ∫⁻ y, ENNReal.ofReal (sliceG d 0 (z + y) + M) ∂(sphereT d η) =
      ENNReal.ofReal (sliceG d 0 z - fTrunc0 d η z + η ^ 2 / (2 * d) + M) := by
  have h := lintegral_G0_newton hd hη hη2 hM (neg_ne_zero.mpr hz0)
  rw [sliceG_neg, fTrunc0_neg] at h
  rw [← h]
  refine lintegral_congr fun y => ?_
  have : sliceG d 0 (z + y) = sliceG d 0 (-z - y) := by
    rw [← sliceG_neg (d := d) 0 (z + y)]; congr 1; abel
  rw [this]


theorem integral_integral_eq_toReal_shift {ν₁ ν₂ : Measure (Torus d)} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] {K : Torus d → Torus d → ℝ} (hK : Measurable (Function.uncurry K)) {M : ℝ}
    (hK0 : ∀ x y, 0 ≤ K x y + M)
    (hfin : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y + M) ∂ν₂ ∂ν₁ ≠ ⊤) :
    ∫ x, ∫ y, K x y ∂ν₂ ∂ν₁ =
      (∫⁻ x, ∫⁻ y, ENNReal.ofReal (K x y + M) ∂ν₂ ∂ν₁).toReal - M * ν₂.real Set.univ * ν₁.real Set.univ := by
  have hK' : Measurable (Function.uncurry fun x y => K x y + M) := hK.add measurable_const
  have hKx : ∀ x, Measurable fun y => K x y := fun x => hK.comp measurable_prodMk_left
  have hA : Measurable fun x => ∫⁻ y, ENNReal.ofReal (K x y + M) ∂ν₂ := by
    have : Measurable (Function.uncurry fun x y => ENNReal.ofReal (K x y + M)) :=
      ENNReal.measurable_ofReal.comp hK'
    exact this.lintegral_prod_right'
  have hae : ∀ᵐ x ∂ν₁, (∫⁻ y, ENNReal.ofReal (K x y + M) ∂ν₂) ≠ ⊤ :=
    (ae_lt_top hA hfin).mono fun x hx => hx.ne
  have hinner : ∀ᵐ x ∂ν₁, ∫ y, K x y ∂ν₂ =
      (∫⁻ y, ENNReal.ofReal (K x y + M) ∂ν₂).toReal - M * ν₂.real Set.univ := by
    filter_upwards [hae] with x hx
    have hint : Integrable (fun y => K x y + M) ν₂ :=
      integrable_of_lintegral_lt_top ((hKx x).add measurable_const) (fun y => hK0 x y) hx.lt_top
    have hint0 : Integrable (fun y => K x y) ν₂ := by
      have := hint.sub (integrable_const M)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp
    have h1 : ∫ y, (K x y + M) ∂ν₂ = (∫⁻ y, ENNReal.ofReal (K x y + M) ∂ν₂).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hK0 x y)
        ((hKx x).add measurable_const).aestronglyMeasurable
    rw [integral_add hint0 (integrable_const M)] at h1
    simp only [integral_const, smul_eq_mul] at h1
    rw [← h1]
    simp [Measure.real]
    ring
  rw [integral_congr_ae hinner]
  have hAint : Integrable (fun x => (∫⁻ y, ENNReal.ofReal (K x y + M) ∂ν₂).toReal) ν₁ :=
    integrable_toReal_of_lintegral_ne_top hA.aemeasurable hfin
  rw [integral_sub hAint (integrable_const _), integral_toReal hA.aemeasurable
    (ae_lt_top hA hfin)]
  simp [Measure.real]
  ring


section Coulomb

theorem lintegral_pair0 (hd : 2 ≤ d) {M : ℝ} (hM : ∀ x, 0 ≤ sliceG d 0 x + M) {ηa ηb : ℝ}
    (ha : 0 < ηa) (ha2 : ηa < 1 / 2) (hb : 0 < ηb) (hb2 : ηb < 1 / 2) (X Y : Torus d)
    (hsep : ηa + ηb < KernelGrad.tdist X Y) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceG d 0 (x - y) + M) ∂((sphereT d ηb).map (fun y => y + Y))
      ∂((sphereT d ηa).map (fun x => x + X)) =
      ENNReal.ofReal (sliceG d 0 (X - Y) + ηa ^ 2 / (2 * d) + ηb ^ 2 / (2 * d) + M) := by
  have h1 : 1 ≤ d := by omega
  have hz : 0 < KernelGrad.tdist (X - Y) 0 := by rw [← tdist_def]; linarith
  have hzne : X - Y ≠ 0 := ne_zero_of_tdist_pos hz
  have hκb : 0 ≤ ηb ^ 2 / (2 * d) := by positivity
  have hκa : 0 ≤ ηa ^ 2 / (2 * d) := by positivity
  rw [lintegral_map_add]
  have hae := ae_tdist_sphereT h1 ha ha2
  have hcongr : ∀ᵐ x' ∂(sphereT d ηa),
      (∫⁻ y, ENNReal.ofReal (sliceG d 0 (x' + X - y) + M) ∂((sphereT d ηb).map (fun y => y + Y))) =
        ENNReal.ofReal (sliceG d 0 ((X - Y) + x') + (ηb ^ 2 / (2 * d) + M)) := by
    filter_upwards [hae] with x' hx'
    have e := (tdist_def X Y).symm
    have h1' : KernelGrad.tdist ((X - Y) + x') 0 > ηb := by
      have := tdist_add_ge (X - Y) x'
      rw [add_comm x' (X - Y)] at this
      linarith
    have hne : (X - Y) + x' ≠ 0 := ne_zero_of_tdist_pos (by linarith)
    rw [lintegral_map_add]
    have e2 : ∀ y : Torus d, x' + X - (y + Y) = ((X - Y) + x') - y := fun y => by abel
    simp only [e2]
    rw [lintegral_G0_newton hd hb hb2 hM hne, fTrunc0_eq_zero hd hb h1'.le]
    congr 1; ring
  rw [lintegral_congr_ae hcongr]
  have hM' : ∀ x, 0 ≤ sliceG d 0 x + (ηb ^ 2 / (2 * d) + M) := fun x => by linarith [hM x]
  rw [lintegral_G0_newton' hd ha ha2 hM' hzne, fTrunc0_eq_zero hd ha (by rw [← tdist_def]; linarith)]
  congr 1; ring

theorem lintegral_self0_lt_top (hd : 2 ≤ d) {M : ℝ} (hM : ∀ x, 0 ≤ sliceG d 0 x + M) {η : ℝ}
    (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceG d 0 (x - y) + M) ∂(sphereT d η) ∂(sphereT d η) < ⊤ := by
  have h1 : 1 ≤ d := by omega
  have := isProbabilityMeasure_sphereT h1 η
  obtain ⟨B, hB⟩ := sliceG_bdd_away (d := d) (le_refl (0 : ℝ)) hη
  have hae := ae_tdist_sphereT h1 hη hη2
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceG d 0 (x - y) + M) ∂(sphereT d η) ∂(sphereT d η)
      ≤ ∫⁻ _x, ENNReal.ofReal (B + η ^ 2 / (2 * d) + M) ∂(sphereT d η) := by
        refine lintegral_mono_ae (hae.mono fun x hx => ?_)
        have hx0 : x ≠ 0 := ne_zero_of_tdist_pos (by rw [hx]; exact hη)
        rw [lintegral_G0_newton hd hη hη2 hM hx0, fTrunc0_eq_zero hd hη hx.ge]
        refine ENNReal.ofReal_le_ofReal ?_
        have := (abs_le.mp (hB x hx.ge)).2
        linarith
    _ < ⊤ := by simp

theorem lintegral_cross0 (hd : 2 ≤ d) {M : ℝ} (hM : ∀ x, 0 ≤ sliceG d 0 x + M) {η : ℝ}
    (hη : 0 < η) (hη2 : η < 1 / 2) (X : Torus d) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (hμ0 : ∀ x, μ {x} = 0) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceG d 0 (x - y) + M) ∂μ ∂((sphereT d η).map (fun y => y + X)) =
      ∫⁻ y, ENNReal.ofReal (sliceG d 0 (X - y) - fTrunc0 d η (X - y) + η ^ 2 / (2 * d) + M) ∂μ := by
  have h1 : 1 ≤ d := by omega
  have := isProbabilityMeasure_sphereT h1 η
  rw [lintegral_map_add]
  have hmeas : Measurable (Function.uncurry fun (x : Torus d) (y : Torus d) =>
      ENNReal.ofReal (sliceG d 0 (x + X - y) + M)) :=
    ENNReal.measurable_ofReal.comp ((((measurable_sliceG 0).comp
      ((measurable_fst.add measurable_const).sub measurable_snd))).add measurable_const)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hae : ∀ᵐ y ∂μ, y ≠ X := by
    rw [ae_iff]; simpa using hμ0 X
  refine lintegral_congr_ae (hae.mono fun y hy => ?_)
  have hz : X - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have e : ∀ x' : Torus d, x' + X - y = (X - y) + x' := fun x' => by abel
  simp only [e]
  exact lintegral_G0_newton' hd hη hη2 hM hz


theorem newton_nonneg (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) {M : ℝ}
    (hM : ∀ x, 0 ≤ sliceG d 0 x + M) {w : Torus d} (hw0 : w ≠ 0) :
    0 ≤ sliceG d 0 w - fTrunc0 d η w + η ^ 2 / (2 * d) + M := by
  have h1 : 1 ≤ d := by omega
  have := isProbabilityMeasure_sphereT h1 η
  have hfin := lintegral_G0_lt_top hd hη hη2 hM w
  have hmeas : Measurable fun y : Torus d => sliceG d 0 (w - y) + M :=
    ((measurable_sliceG 0).comp (measurable_const.sub measurable_id)).add measurable_const
  have hint : Integrable (fun y : Torus d => sliceG d 0 (w - y) + M) (sphereT d η) :=
    integrable_of_lintegral_lt_top hmeas (fun y => hM _) hfin
  have hint0 : Integrable (fun y : Torus d => sliceG d 0 (w - y)) (sphereT d η) := by
    have := hint.sub (integrable_const M)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  have h0 : 0 ≤ ∫ y, (sliceG d 0 (w - y) + M) ∂(sphereT d η) :=
    integral_nonneg fun y => hM _
  rw [integral_add hint0 (integrable_const M), sliceG0_conv_sphere hd hη hη2 w hw0] at h0
  simpa using h0

end Coulomb


theorem measurable_newton (d : ℕ) : Measurable (newton d) := by
  show Measurable (fun r : ℝ => newton d r)
  by_cases h : d = 2
  · simp only [newton, h, if_true]
    exact Real.measurable_log.const_mul _
  · simp only [newton, h, if_false]
    exact (measurable_id.pow_const _).const_mul _

theorem measurable_fTrunc0 (η : ℝ) : Measurable (fTrunc0 d η) := by
  unfold fTrunc0
  have : (fun z : Torus d => max (newton d ‖KernelGrad.centeredRep z‖ - newton d η) 0) =
      fun z => max (newton d (KernelGrad.tdist z 0) - newton d η) 0 := by
    funext z; simp [KernelGrad.tdist]
  rw [this]
  exact (((measurable_newton d).comp measurable_tdist_zero).sub measurable_const).max measurable_const

theorem lintegral_self_shift' (σ : Measure (Torus d)) (a : Torus d) (M : ℝ) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceG d 0 (x - y) + M) ∂(σ.map (fun y => y + a))
      ∂(σ.map (fun y => y + a)) =
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sliceG d 0 (x - y) + M) ∂σ ∂σ := by
  rw [lintegral_map_add]
  simp_rw [lintegral_map_add]
  simp only [add_sub_add_right_eq_sub]

theorem energy_identity_coulomb_aux {N : ℕ} (hd : 2 ≤ d) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] (hμ0 : ∀ x, μ {x} = 0)
    (hμ1 : ∀ x, Integrable (fun y => sliceG d 0 (x - y)) μ)
    (X : Fin N → Torus d) (η : Fin N → ℝ) (hη : ∀ i, 0 < η i ∧ η i < 1 / 2)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    (ν : Measure (Torus d))
    (hν : ν = (N : ℝ≥0∞)⁻¹ • ∑ i, (sphereT d (η i)).map (fun y => y + X i)) :
    ∫ x, ∫ y, sliceG d 0 (x - y) ∂ν ∂ν - 2 * ∫ x, ∫ y, sliceG d 0 (x - y) ∂μ ∂ν
        + ∫ x, ∫ y, sliceG d 0 (x - y) ∂μ ∂μ =
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (sliceG d 0 (X i - X j) + η i ^ 2 / (2 * d) + η j ^ 2 / (2 * d))
      + (1 / (N : ℝ) ^ 2) * ∑ i, ∫ x, ∫ y, sliceG d 0 (x - y) ∂(sphereT d (η i)) ∂(sphereT d (η i))
      - (2 / (N : ℝ)) * ∑ i, ∫ y, (sliceG d 0 (X i - y) - fTrunc0 d (η i) (X i - y)
          + η i ^ 2 / (2 * d)) ∂μ
      + ∫ x, ∫ y, sliceG d 0 (x - y) ∂μ ∂μ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · subst hν
    simp
  have hd1 : 1 ≤ d := by omega
  obtain ⟨M, hM0, hM0'⟩ := sliceG_zero_lower d
  have hM : ∀ x, 0 ≤ sliceG d 0 x + M := fun x => by linarith [hM0' x]
  set c : ℝ≥0∞ := (N : ℝ≥0∞)⁻¹ with hcdef
  have hc : c ≠ ⊤ := by
    rw [hcdef]; exact ENNReal.inv_ne_top.mpr (by simpa using hN.ne')
  have hcr : c.toReal = 1 / (N : ℝ) := by
    rw [hcdef, ENNReal.toReal_inv]; simp
  set σ : Fin N → Measure (Torus d) := fun i => sphereT d (η i) with hσ
  have hσp : ∀ i, IsProbabilityMeasure (σ i) := fun i => isProbabilityMeasure_sphereT hd1 (η i)
  set ν' : Fin N → Measure (Torus d) := fun i => (σ i).map (fun y => y + X i) with hν'
  have hν'p : ∀ i, IsProbabilityMeasure (ν' i) := fun i => by
    rw [hν']; infer_instance
  have hν2 : ν = c • ∑ i, ν' i := hν
  have hνuniv : ν Set.univ = 1 := by
    rw [hν2]
    simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
    have : ∀ i, ν' i Set.univ = 1 := fun i => measure_univ
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hcdef]
    exact ENNReal.inv_mul_cancel (by simpa using hN.ne') (ENNReal.natCast_ne_top N)
  have hνfin : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact ENNReal.one_lt_top⟩
  have hνreal : ν.real Set.univ = 1 := by simp [Measure.real, hνuniv]
  set g : Torus d → ℝ := sliceG d 0 with hg
  have hgm : Measurable g := measurable_sliceG 0
  have hK : Measurable (Function.uncurry fun x y : Torus d => g (x - y)) :=
    hgm.comp (measurable_fst.sub measurable_snd)
  have hKA : Measurable (Function.uncurry fun x y : Torus d => ENNReal.ofReal (g (x - y) + M)) :=
    ENNReal.measurable_ofReal.comp (hK.add measurable_const)
  set κ : Fin N → ℝ := fun i => η i ^ 2 / (2 * d) with hκ
  have hκ0 : ∀ i, 0 ≤ κ i := fun i => by simp only [hκ]; positivity
  -- self energies
  set S : Fin N → ℝ≥0∞ := fun i =>
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y) + M) ∂(σ i) ∂(σ i) with hS
  have hSfin : ∀ i, S i ≠ ⊤ := fun i => (lintegral_self0_lt_top hd hM (hη i).1 (hη i).2).ne
  have hE : ∀ i j, ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y) + M) ∂(ν' j) ∂(ν' i) =
      if i = j then S i else ENNReal.ofReal (g (X i - X j) + κ i + κ j + M) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have := lintegral_self_shift' (σ i) (X i) M
      exact this
    · rw [if_neg hij]
      exact lintegral_pair0 hd hM (hη i).1 (hη i).2 (hη j).1 (hη j).2 (X i) (X j) (hdisj i j hij)

  have hAm : ∀ j, Measurable fun x => ∫⁻ y, ENNReal.ofReal (g (x - y) + M) ∂(ν' j) := fun j =>
    hKA.lintegral_prod_right'
  have hEtot : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y) + M) ∂ν ∂ν =
      c * ∑ i, (c * ∑ j, if i = j then S i else ENNReal.ofReal (g (X i - X j) + κ i + κ j + M)) := by
    rw [hν2]
    simp only [lintegral_smul_measure, lintegral_finset_sum_measure, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_const_mul' _ _ hc, lintegral_finset_sum _ fun j _ => hAm j]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hE i j
  -- cross energies
  set Cc : Fin N → ℝ≥0∞ := fun i =>
    ∫⁻ y, ENNReal.ofReal (g (X i - y) - fTrunc0 d (η i) (X i - y) + κ i + M) ∂μ with hCc
  have hCfin : ∀ i, Cc i ≠ ⊤ := by
    intro i
    have h1 : Cc i ≤ ∫⁻ y, ENNReal.ofReal (g (X i - y) + (κ i + M)) ∂μ := by
      refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
      have := fTrunc0_nonneg (d := d) (X i - y) (η := η i)
      linarith
    have hint : Integrable (fun y => g (X i - y) + (κ i + M)) μ := (hμ1 (X i)).add (integrable_const _)
    have h2 : ∫⁻ y, ENNReal.ofReal (g (X i - y) + (κ i + M)) ∂μ < ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun y => by
          have := hM (X i - y); have := hκ0 i; simp only [Pi.zero_apply]; linarith)]
      exact ENNReal.ofReal_lt_top
    exact (h1.trans_lt h2).ne
  have hEcross : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y) + M) ∂μ ∂ν = c * ∑ i, Cc i := by
    rw [hν2]
    simp only [lintegral_smul_measure, lintegral_finset_sum_measure, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact lintegral_cross0 hd hM (hη i).1 (hη i).2 (X i) μ hμ0
  have hEtotfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y) + M) ∂ν ∂ν) ≠ ⊤ := by
    rw [hEtot]
    refine ENNReal.mul_ne_top hc (ENNReal.sum_ne_top.mpr fun i _ => ENNReal.mul_ne_top hc
      (ENNReal.sum_ne_top.mpr fun j _ => ?_))
    split_ifs
    · exact hSfin i
    · exact ENNReal.ofReal_ne_top
  have hEcrossfin : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (g (x - y) + M) ∂μ ∂ν) ≠ ⊤ := by
    rw [hEcross]
    exact ENNReal.mul_ne_top hc (ENNReal.sum_ne_top.mpr fun i _ => hCfin i)
  have hT1 := integral_integral_eq_toReal_shift (ν₁ := ν) (ν₂ := ν) hK (M := M)
    (fun x y => hM _) hEtotfin
  have hT2 := integral_integral_eq_toReal_shift (ν₁ := ν) (ν₂ := μ) hK (M := M)
    (fun x y => hM _) hEcrossfin
  have hTS : ∀ i, ∫ x, ∫ y, g (x - y) ∂(sphereT d (η i)) ∂(sphereT d (η i)) = (S i).toReal - M := by
    intro i
    have := integral_integral_eq_toReal_shift (ν₁ := σ i) (ν₂ := σ i) hK (M := M)
      (fun x y => hM _) (hSfin i)
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at this
    exact this
  have hTC : ∀ i, ∫ y, (g (X i - y) - fTrunc0 d (η i) (X i - y) + η i ^ 2 / (2 * d)) ∂μ =
      (Cc i).toReal - M * μ.real Set.univ := by
    intro i
    have hae : ∀ᵐ y ∂μ, y ≠ X i := by
      rw [ae_iff]; simpa using hμ0 (X i)
    have hmeasU : Measurable fun y => g (X i - y) - fTrunc0 d (η i) (X i - y) + κ i + M := by
      have h0 : Measurable (fTrunc0 d (η i)) := measurable_fTrunc0 (η i)
      exact (((hgm.comp (measurable_const.sub measurable_id)).sub
        (h0.comp (measurable_const.sub measurable_id))).add measurable_const).add measurable_const
    have hnn : ∀ᵐ y ∂μ, 0 ≤ g (X i - y) - fTrunc0 d (η i) (X i - y) + κ i + M :=
      hae.mono fun y hy => newton_nonneg hd (hη i).1 (hη i).2 hM (sub_ne_zero.mpr (Ne.symm hy))
    have h1 : ∫ y, (g (X i - y) - fTrunc0 d (η i) (X i - y) + κ i + M) ∂μ = (Cc i).toReal :=
      integral_eq_lintegral_of_nonneg_ae hnn hmeasU.aestronglyMeasurable
    have hint : Integrable (fun y => g (X i - y) - fTrunc0 d (η i) (X i - y) + κ i + M) μ := by
      refine ⟨hmeasU.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      refine lt_of_le_of_lt (le_of_eq ?_) (hCfin i).lt_top
      rw [hCc]
      refine lintegral_congr_ae (hnn.mono fun y hy => ?_)
      dsimp only
      rw [Real.enorm_of_nonneg hy]
    have hint0 : Integrable (fun y => g (X i - y) - fTrunc0 d (η i) (X i - y) + κ i) μ := by
      have := hint.sub (integrable_const M)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp
    rw [integral_add hint0 (integrable_const M)] at h1
    simp only [integral_const, smul_eq_mul, Measure.real] at h1 ⊢
    rw [← h1]
    ring
  rw [hT1, hT2, hEtot, hEcross]
  simp only [hTC, hTS, hνreal, mul_one]
  have hsplit : ∀ i, (∑ j, if i = j then S i else ENNReal.ofReal (g (X i - X j) + κ i + κ j + M)) =
      S i + ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (g (X i - X j) + κ i + κ j + M) := by
    intro i
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin N))
      (fun j : Fin N => if i = j then S i else ENNReal.ofReal (g (X i - X j) + κ i + κ j + M))
      (Finset.mem_univ i)]
    simp only [if_true]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]
  have hpos : ∀ i j, 0 ≤ g (X i - X j) + κ i + κ j + M := fun i j => by
    have := hM (X i - X j); have := hκ0 i; have := hκ0 j; linarith
  have hE1 : (c * ∑ i, c * ∑ j, if i = j then S i else
      ENNReal.ofReal (g (X i - X j) + κ i + κ j + M)).toReal =
      (1 / (N : ℝ)) ^ 2 * ∑ i, ((S i).toReal +
        ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + κ i + κ j + M)) := by
    simp only [hsplit]
    have hfin : ∀ i, (S i + ∑ j ∈ Finset.univ.erase i,
        ENNReal.ofReal (g (X i - X j) + κ i + κ j + M)) ≠ ⊤ := fun i =>
      ENNReal.add_ne_top.mpr ⟨hSfin i, ENNReal.sum_ne_top.mpr fun j _ => ENNReal.ofReal_ne_top⟩
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top hc (hfin i)), hcr]
    have hterm : ∀ i, (c * (S i + ∑ j ∈ Finset.univ.erase i,
        ENNReal.ofReal (g (X i - X j) + κ i + κ j + M))).toReal =
        1 / (N : ℝ) * ((S i).toReal + ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + κ i + κ j + M)) := by
      intro i
      have hsf : (∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (g (X i - X j) + κ i + κ j + M)) ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr fun j _ => ENNReal.ofReal_ne_top
      rw [ENNReal.toReal_mul, hcr, ENNReal.toReal_add (hSfin i) hsf,
        ENNReal.toReal_sum (s := Finset.univ.erase i) (fun j _ => ENNReal.ofReal_ne_top)]
      congr 2
      exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (hpos i j)
    simp only [hterm]
    rw [← Finset.mul_sum, sq, mul_assoc]
  have hE2 : (c * ∑ i, Cc i).toReal = (1 / (N : ℝ)) * ∑ i, (Cc i).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun i _ => hCfin i), hcr]
  rw [hE1, hE2]
  have hNn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcard : ∀ i : Fin N, ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := fun i => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega)]; simp
  have hsum : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + κ i + κ j + M) =
      ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + κ i + κ j) + ((N : ℝ) - 1) * M := fun i => by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
  simp only [hsum]
  have key1 : ∀ (T s : Fin N → ℝ) (a : ℝ), ∑ i, (s i + (T i + a)) = ∑ i, s i + ∑ i, T i + (N : ℝ) * a := by
    intro T s a
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const]; simp; ring
  have key2 : ∀ (s : Fin N → ℝ) (a : ℝ), ∑ i, (s i - a) = ∑ i, s i - (N : ℝ) * a := by
    intro s a
    rw [Finset.sum_sub_distrib, Finset.sum_const]; simp
  have e1 := key1 (fun i => ∑ j ∈ Finset.univ.erase i, (g (X i - X j) + κ i + κ j))
    (fun i => (S i).toReal) (((N : ℝ) - 1) * M)
  have e2 := key2 (fun i => (S i).toReal) M
  have e3 := key2 (fun i => (Cc i).toReal) (M * μ.real Set.univ)
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3]
  simp only [hκ]
  generalize ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
    (g (X i - X j) + η i ^ 2 / (2 * d) + η j ^ 2 / (2 * d)) = T
  generalize ∑ i : Fin N, (S i).toReal = SS
  generalize ∑ i : Fin N, (Cc i).toReal = CC
  field_simp
  ring


end HRS.Commutator.EnergyAux
