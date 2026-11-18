import HRS.Main.EqMargU3

/-!
# EQ-MARG-U, part 4: uniform smallness and the uniform `L²` bound
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace EqMarg

open HRS.External HRS.PoleCavityAux HRS.MarginalAux

variable {d : ℕ} {s : ℝ}

open InformationTheory in
theorem eqmarg_klDiv_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C C' : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N →
      klDiv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))
          (Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
        ENNReal.ofReal (C * ((N : ℝ) * aN d s N) + C') := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, Cc, hB0, hCc0, hKU⟩ := eqmarg_kerData hd hs0 hsd Λ0
  obtain ⟨C₀, hC₀, hcoer⟩ := coercivity_lower hd1 hs0 hsd
  set Λ' : ℝ := max Λ0 1 with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_right _ _
  obtain ⟨C₀', hC₀', hoN⟩ := oNΛ_le_aN hd1 hs0 hsd C₀ hC₀ Λ' hΛ'1
  refine ⟨βp * C₀', βp * (B / 2), by positivity, by positivity,
    fun β hβ1 hβ2 ρ hρ hΛρ N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hK := hKU ρ hρ hΛρ
  have hΛ'b : ∀ x, ρ x ≤ Λ' := fun x => (hΛρ x).trans (le_max_left _ _)
  set μ := withDensityReal ρ with hμdef
  set g := periodicRiesz d s with hgdef
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hgm : Measurable g := measurable_periodicRiesz hd hs0 hsd
  have heven : ∀ x, g (-x) = g x := fun x => periodicRiesz_neg x
  -- energy and exponent
  set F : Config d N → ℝ := fun X => modulatedEnergyKernel g X μ with hF
  set w : Config d N → ℝ := fun X => -β * N * F X with hw
  have hFi : Integrable F P := integrable_energy hd hs0 hsd hρ N (by omega)
  have hlam : 0 ≤ β / N := by positivity
  set wc : Config d N → ℝ := fun Y => -(β / N) * pairSum g Y + β * ∑ i, convMeasure g μ (Y i) with hwc
  have hwcm : Measurable wc := measurable_cavityW hgm μ N (β / N) β
  have hE : ∀ X : Config d N, w X = wc X - β * N * Calib.Kq g μ := by
    intro X
    show -β * N * modulatedEnergyKernel g X μ = _
    rw [Calib.modEnergy_q_eq (by omega : 0 < N) β X]
    unfold Calib.E0
    simp only [hwc]
    rw [RefSmall.pairSum_eq_half heven X, ← Finset.mul_sum]
    ring
  obtain ⟨W, hW⟩ := cavity_weight_le hd hs0 hsd β hρ N (β / N) hlam
  have hwb : ∀ X, w X ≤ W - β * N * Calib.Kq g μ := fun X => by rw [hE X]; linarith [hW X]
  have hwm : Measurable w := by
    have : w = fun X => wc X - β * N * Calib.Kq g μ := funext hE
    rw [this]; exact hwcm.sub measurable_const
  have hexp : Integrable (fun X => Real.exp (w X)) P :=
    Integrable.of_bound (C := Real.exp (W - β * N * Calib.Kq g μ)) (Real.measurable_exp.comp hwm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hwb X))
  have hQ : modulatedGibbs g N β μ = P.tilted w := Calib.modulatedGibbs_eq_tilted hexp
  set Q := modulatedGibbs g N β μ with hQdef
  set Z := ∫ X, Real.exp (w X) ∂P with hZ
  have hZpos : 0 < Z := integral_exp_pos hexp
  have hQprob : IsProbabilityMeasure Q := by
    rw [hQ]; exact isProbabilityMeasure_tilted hexp
  have hac : Q ≪ P := by rw [hQ]; exact tilted_absolutelyContinuous P w
  have hllr : llr Q P =ᵐ[Q] fun X => w X - Real.log Z := by
    have := log_rnDeriv_tilted_left_self hexp
    rw [← hQ] at this
    exact hac.ae_le this
  have hwQ : Integrable w Q := by
    rw [hQ, integrable_tilted_iff hexp]
    refine Integrable.of_bound (C := max (|W - β * N * Calib.Kq g μ| * Real.exp (W - β * N * Calib.Kq g μ)) 1)
      ((Real.measurable_exp.comp hwm).mul hwm).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
    simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm]
    exact abs_mul_exp_le_of_le (hwb X)
  have hllrI : Integrable (llr Q P) Q := (hwQ.sub (integrable_const _)).congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hllrI]
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have h1 : P.real Set.univ = 1 := by simp [Measure.real]
  have h2 : Q.real Set.univ = 1 := by simp [Measure.real]
  rw [h1, h2, add_sub_cancel_right, integral_congr_ae hllr, integral_sub hwQ (integrable_const _), integral_const]
  simp only [h2, smul_eq_mul, one_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  -- upper bound of `∫ w dQ`
  have hnc : ∀ᵐ X ∂Q, X ∉ collisionSet d N := by
    exact hac.ae_le (RefSmall.ae_not_collision hd1 hρ.density N)
  have hFlow : ∀ᵐ X ∂Q, -oNΛ d s C₀ Λ' N ≤ F X := by
    filter_upwards [hnc] with X hX
    have := hcoer Λ' hΛ'1 N hN ρ hρ.density hΛ'b X hX
    show -oNΛ d s C₀ Λ' N ≤ rieszEnergy d s X μ
    linarith
  have hwQup : ∫ X, w X ∂Q ≤ β * N * oNΛ d s C₀ Λ' N := by
    have : ∫ X, w X ∂Q ≤ ∫ _X, β * N * oNΛ d s C₀ Λ' N ∂Q := by
      refine integral_mono_ae hwQ (integrable_const _) ?_
      filter_upwards [hFlow] with X hX
      simp only [hw]
      have hb : 0 ≤ β * N := by positivity
      nlinarith
    simpa [h2] using this
  -- Jensen lower bound of `log Z`
  have hwi : Integrable w P := by
    have : w = fun X => (-β * N) * F X := rfl
    rw [this]; exact hFi.const_mul _
  have hJ : ∫ X, w X ∂P ≤ Real.log Z := by
    have := EF.ef_cgf_ge (P := P) (X := w) (b := W - β * N * Calib.Kq g μ) hwm hwb hwi
    simpa [cgf, mgf, hZ] using this
  have hEF : ∫ X, F X ∂P = -(1 / (2 * N)) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) :=
    expectation_modulatedEnergy_iid g μ (by omega) hK.int2 hK.int
  have hI : -B ≤ ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) := by
    have := integral_mono (integrable_const (-B)) hK.int2 (fun p => hK.lower _)
    simpa using this
  have hwP : ∫ X, w X ∂P = (β / 2) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) := by
    have : ∫ X, w X ∂P = (-β * N) * ∫ X, F X ∂P := integral_const_mul _ _
    rw [this, hEF]; field_simp
  have hoN' := hoN N hN
  have hb : 0 ≤ β * N := by positivity
  have hNa : 0 ≤ (N : ℝ) * aN d s N := mul_nonneg hN0.le (eqmarg_aN_nonneg d s N)
  have hm1 : β * N * (C₀' * aN d s N) ≤ βp * C₀' * (N * aN d s N) := by
    have := mul_le_mul_of_nonneg_right hβ2 (mul_nonneg hC₀' hNa)
    nlinarith [this]
  have hm2 : β * (B / 2) ≤ βp * (B / 2) := mul_le_mul_of_nonneg_right hβ2 (by positivity)
  have : β * N * oNΛ d s C₀ Λ' N ≤ β * N * (C₀' * aN d s N) := mul_le_mul_of_nonneg_left hoN' hb
  have hI2 : (β / 2) * (-B) ≤ (β / 2) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) :=
    mul_le_mul_of_nonneg_left hI (by positivity)
  nlinarith [hm1, hm2]

open HRS.External.Entropy in
theorem eqmarg_tv_pi_mu (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ n : ℕ, n₁ ≤ n → ∀ A : Set (Torus d), MeasurableSet A →
    |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) (β / ((n + 1 : ℕ) : ℝ)) β) A).toReal -
      (withDensityReal ρ A).toReal| ≤ ε := by
  intro ε hε
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, C', hC, hC', hkl⟩ := eqmarg_klDiv_le hd hs0 hsd βm βp hβm hββ Λ0
  have ha := RefSmall.tendsto_aN hd1 hs0 hsd
  have ha1 : Tendsto (fun N : ℕ => aN d s (N + 1)) atTop (𝓝 0) :=
    ha.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun N : ℕ => C' / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := C')).div_atTop (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa using this
  have hup : Tendsto (fun N : ℕ => Real.sqrt ((C * aN d s (N + 1) + C' / ((N : ℝ) + 1)) / 2)) atTop (𝓝 0) := by
    have h1 := ((ha1.const_mul C).add hinv).div_const 2
    simp only [mul_zero, add_zero, zero_div] at h1
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa [Function.comp_def] using h2
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((tendsto_order.1 hup).2 ε hε)
  refine ⟨max n₁ 1, fun β hβ1 hβ2 ρ hρ hΛ n hn0 A hA => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hn : n₁ ≤ n := le_trans (le_max_left _ _) hn0
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn0
  have hμ := isProbabilityMeasure_mu hρ
  have hG := modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n)
  haveI : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) := by
    rw [hG]; exact cavity_isProb hd hs0 hsd β hρ (n + 1) _ (by positivity)
  haveI : IsProbabilityMeasure ((modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)).map
      fun X : Config d (n + 1) => X 0) :=
    (Measure.isProbabilityMeasure_map_iff (Measurable.aemeasurable (measurable_pi_apply 0))).2 inferInstance
  have hex : Entropy.IsExchangeable (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) := by
    rw [hG]
    exact cavityLaw_exchangeable hd hs0 hsd β hρ (n + 1) _
  have haN := eqmarg_aN_nonneg d s (n + 1)
  have hK : 0 ≤ C * (((n + 1 : ℕ) : ℝ) * aN d s (n + 1)) + C' := by positivity
  have htv := eqmarg_tv_of_kl (withDensityReal ρ)
    (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) hex hK
    (hkl β hβ1 hβ2 ρ hρ hΛ (n + 1) (by omega))
  have e0 : (C * (((n + 1 : ℕ) : ℝ) * aN d s (n + 1)) + C') / ((n : ℝ) + 1) / 2 =
      (C * aN d s (n + 1) + C' / ((n : ℝ) + 1)) / 2 := by
    push_cast
    field_simp
  rw [e0] at htv
  have h1 := Entropy.abs_le_tvDist ((modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)).map
      fun X : Config d (n + 1) => X 0) (withDensityReal ρ) hA
  have h2 := hn₁ n hn
  have e : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) (β / ((n + 1 : ℕ) : ℝ)) β) =
      (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)).map
        fun X : Config d (n + 1) => X 0 := by
    rw [← hG]
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  rw [e]
  simp only [Measure.real] at h1
  exact h1.trans (htv.trans h2.le)

theorem eqmarg_Kt_sup_small (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) (hM : 0 ≤ M) (Λ0 : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
    ∀ h : Torus d → ℝ, Measurable h → (∀ y, |h y| ≤ M) → ∫ y, |h y| ∂(withDensityReal ρ) ≤ δ →
      ∀ x, |ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h x| ≤ ε := by
  set Λ : ℝ := max Λ0 1 with hΛdef
  have hΛ0 : 0 < Λ := lt_max_of_lt_right one_pos
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := MarginalAux.sup_conv_small hd hs0 hsd (M * Λ) (by positivity) ε hε
  refine ⟨δ, hδ, fun ρ hρ hΛρ h hm hb hl x => ?_⟩
  have hμ := isProbabilityMeasure_mu hρ
  have hΛ : ∀ x, ρ x ≤ Λ := fun x => (hΛρ x).trans (le_max_left _ _)
  have hρm : Measurable ρ := hρ.density.measurable
  set f : Torus d → ℝ := fun y => ρ y * h y with hf
  have hfm : Measurable f := hρm.mul hm
  have hfb : ∀ y, |f y| ≤ M * Λ := by
    intro y
    have h2 : |ρ y| ≤ Λ := by rw [abs_of_pos (hρ.pos y)]; exact hΛ y
    rw [abs_mul, mul_comm]
    exact mul_le_mul (hb y) h2 (abs_nonneg _) hM
  have hhi : Integrable h (withDensityReal ρ) :=
    Integrable.of_bound (C := M) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have hl1f : ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal δ := by
    have e1 : ∀ y, ‖f y‖ₑ = ENNReal.ofReal (ρ y) * ‖h y‖ₑ := by
      intro y
      simp only [hf, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y)]
    simp_rw [e1]
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    have e2 : ∫⁻ y, ENNReal.ofReal (ρ y) * ‖h y‖ₑ = ∫⁻ y, ‖h y‖ₑ ∂(withDensityReal ρ) := by
      show _ = ∫⁻ y, ‖h y‖ₑ ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))
      rw [lintegral_withDensity_eq_lintegral_mul _ hmρ hm.enorm]
      rfl
    rw [e2]
    have e3 : ∫⁻ y, ‖h y‖ₑ ∂(withDensityReal ρ) = ENNReal.ofReal (∫ y, |h y| ∂(withDensityReal ρ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hhi.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs]
    rw [e3]
    exact ENNReal.ofReal_le_ofReal hl
  have h1 := hs f hfm hfb hl1f x
  have hKt : ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h x =
      ∫ y, periodicRiesz d s (x - y) * f y := by
    rw [ResponseAux.Kt_eq_cv hρ.density]; rfl
  rw [hKt]
  have h2 : ‖∫ y, periodicRiesz d s (x - y) * f y‖ₑ ≤ ENNReal.ofReal ε := by
    refine (enorm_integral_le_lintegral_enorm _).trans ((le_of_eq ?_).trans h1)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul]
  rw [Real.enorm_eq_ofReal_abs] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 h2

theorem eqmarg_sup_dev_small (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
    ∀ n : ℕ, n₀ ≤ n → 0 < n → ∀ lam : ℝ,
    lam = β / ((n + 1 : ℕ) : ℝ) → ∀ x : Torus d,
      |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1| ≤ ε := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  intro ε hε
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Mp, hMp1, hMpU⟩ := eqmarg_pDens_bounds hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Mq, hMq0, hMqU⟩ := eqmarg_qDens_bound hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Ctv, hCtv0, hCtvU⟩ := eqmarg_cavity_tv hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Cd, hCdU⟩ := eqmarg_insDefect_le hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Kg, hKg0, hKgU⟩ := eqmarg_convAbs hd hs0 hsd Λ0
  set η : ℝ := Real.log (1 + ε) / 2 with hη
  have hη0 : 0 < η := by
    have : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    positivity
  set ε₁ : ℝ := η / (3 * βp) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δ₁, hδ₁, hKtU⟩ := eqmarg_Kt_sup_small hd hs0 hsd (1 + Mq) (by positivity) Λ0 ε₁ hε₁0
  obtain ⟨n₁, hn₁U⟩ := eqmarg_tv_pi_mu hd hs0 hsd βm βp hβm hββ Λ0 (δ₁ / 8) (by positivity)
  -- smallness of `δ_{n+1}`
  have hδt : Tendsto (fun n : ℕ => deltaN d s (n + 1)) atTop (𝓝 0) :=
    (tendsto_deltaN hs0 hsd hd1).comp (tendsto_add_atTop_nat 1)
  set K : ℝ := |Cd| + βp * Kg * Mq + 1 with hK
  have hK0 : 0 < K := by positivity
  set κ : ℝ := min (η / (3 * K)) ((δ₁ / (8 * (Ctv + 1))) ^ 2) with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 ((tendsto_order.1 hδt).2 κ hκ0)
  refine ⟨max (max n₁ n₂) 1, fun β hβ1 hβ2 ρ hρ hΛ n hnn hn lam hlamdef x => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hMp := hMpU β hβ1 hβ2 ρ hρ hΛ
  have hMq := hMqU β hβ1 hβ2 ρ hρ hΛ
  have hCtv := hCtvU β hβ1 hβ2 ρ hρ hΛ
  have hCd := hCdU β hβ1 hβ2 ρ hρ hΛ
  have hKg := hKgU ρ hρ hΛ
  have hKt := hKtU ρ hρ hΛ
  have hn₁ := hn₁U β hβ1 hβ2 ρ hρ hΛ
  have hn₁' : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnn
  have hn₂' : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnn
  have hδκ := hn₂ n hn₂'
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hacq := (hMq (n + 1) hN)
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪ withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hlamδ : lam ≤ β * deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    rw [hlam', div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left this hβ.le
  have hTV1 : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (withDensityReal ρ A).toReal| ≤ δ₁ / 8 := by
    intro A hA
    subst hlam'
    exact hn₁ n hn₁' A hA
  have hTV2 : ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) A).toReal| ≤
        Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro A hA
    subst hlam'
    exact hCtv (n + 1) hN A hA
  have hsqrt : Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ δ₁ / 8 := by
    have h1 : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) := by
      refine div_le_self hδ0 ?_
      exact_mod_cast (by omega : 1 ≤ n + 1)
    have h2 : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ δ₁ / (8 * (Ctv + 1)) := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      exact h1.trans (hδκ.le.trans (min_le_right _ _))
    calc Ctv * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ (Ctv + 1) * (δ₁ / (8 * (Ctv + 1))) := by
          gcongr
          linarith
      _ = δ₁ / 8 := by field_simp
  have hl1 := l1_one_q hd hs0 hsd hβ hρ hn hlamdef hac hpb hTV1 (fun A hA => (hTV2 A hA).trans hsqrt)
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hq0 : ∀ y, 0 ≤ qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y := fun y => ENNReal.toReal_nonneg
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
  have hqbm : Measurable qb := hqm.min measurable_const
  have hqbq : q =ᵐ[withDensityReal ρ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
  have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
  have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
  have hhb : ∀ y, |1 - qb y| ≤ 1 + Mq := by
    intro y
    rw [abs_le]; constructor <;> linarith [hqb0 y, hqbM y]
  have hsm : ∫ y, |1 - qb y| ∂(withDensityReal ρ) ≤ δ₁ := by
    have e4 : ∫ y, |1 - qb y| ∂(withDensityReal ρ) = ∫ y, |1 - q y| ∂(withDensityReal ρ) := by
      refine integral_congr_ae (hqbq.mono fun y hy => ?_)
      simp only [← hy]
    rw [e4]
    refine hl1.trans ?_
    have : 2 * (δ₁ / 8) + 2 * (δ₁ / 8) ≤ δ₁ := by linarith
    linarith
  have hae : (fun y => 1 - q y) =ᵐ[withDensityReal ρ] fun y => 1 - qb y :=
    hqbq.mono fun y hy => by simp only [← hy]
  have hκK : K * deltaN d s (n + 1) ≤ η / 3 := by
    have := hδκ.le.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hut : ∀ y, |uIns (periodicRiesz d s) (withDensityReal ρ) n lam β y| ≤ η := by
    intro y
    have hKty := hKt (fun y => 1 - qb y) (measurable_const.sub hqbm) hhb hsm y
    rw [← ResponseAux.Kt_congr _ hae] at hKty
    have hu := uIns_le_aux hd hs0 hsd hβ hρ hn hlamdef hac hMq0.le hqb hKg y
    have hDb := hCd (n + 1) hN y
    rw [Nat.add_sub_cancel] at hDb
    have hDb' : |insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β y| ≤ |Cd| * deltaN d s (n + 1) := by
      subst hlam'
      rw [abs_of_nonneg hDb.1]
      exact hDb.2.1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
    have h1 : β * |ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) (fun y => 1 - q y) y| ≤ η / 3 := by
      calc _ ≤ β * ε₁ := mul_le_mul_of_nonneg_left hKty hβ.le
        _ ≤ βp * ε₁ := mul_le_mul_of_nonneg_right hβ2 hε₁0.le
        _ = η / 3 := by rw [hε₁]; field_simp
    have h2 : lam * (Kg * Mq) ≤ η / 3 := by
      calc lam * (Kg * Mq) ≤ (β * deltaN d s (n + 1)) * (Kg * Mq) :=
            mul_le_mul_of_nonneg_right hlamδ (by positivity)
        _ = (β * Kg * Mq) * deltaN d s (n + 1) := by ring
        _ ≤ K * deltaN d s (n + 1) := by
            refine mul_le_mul_of_nonneg_right ?_ hδ0
            have hβKM : β * Kg * Mq ≤ βp * Kg * Mq := by
              have := mul_nonneg hKg0 hMq0.le
              nlinarith
            rw [hK]; linarith [abs_nonneg Cd, hβKM]
        _ ≤ η / 3 := hκK
    have h3 : |Cd| * deltaN d s (n + 1) ≤ η / 3 := by
      refine le_trans ?_ hκK
      refine mul_le_mul_of_nonneg_right ?_ hδ0
      rw [hK]
      have : 0 ≤ βp * Kg * Mq := by positivity
      linarith
    linarith
  have hdev := pDens_dev hd hs0 hsd hρ hlam hln hη0.le hut x
  have : Real.exp (2 * η) = 1 + ε := by
    rw [hη, show 2 * (Real.log (1 + ε) / 2) = Real.log (1 + ε) by ring, Real.exp_log (by linarith)]
  linarith

theorem eqmarg_L2_all (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
    ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
    ∫ x, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) ^ 2 ∂(withDensityReal ρ) ≤
      (C * deltaN d s (n + 1)) ^ 2 := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨n₀, hn₀U⟩ := eqmarg_sup_dev_small hd hs0 hsd βm βp hβm hββ Λ0 1 one_pos
  obtain ⟨Cw, hCw0, hCwU⟩ := eqmarg_w_L2 hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Mp, hMp1, hMpU⟩ := eqmarg_pDens_bounds hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Mq, hMq0, hMqU⟩ := eqmarg_qDens_bound hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Kg, hKg0, hKgU⟩ := eqmarg_convAbs hd hs0 hsd Λ0
  refine ⟨max (2 * Cw) (Mp * (n₀ + 1)), le_max_of_le_left (by positivity),
    fun β hβ1 hβ2 ρ hρ hΛ n hn lam hlamdef => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hn₀ := hn₀U β hβ1 hβ2 ρ hρ hΛ
  have hCw := hCwU β hβ1 hβ2 ρ hρ hΛ
  have hMp := hMpU β hβ1 hβ2 ρ hρ hΛ
  have hMq := hMqU β hβ1 hβ2 ρ hρ hΛ
  have hKg := hKgU ρ hρ hΛ
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hp0 := pDens_pos hd hs0 hsd hρ hlam hln
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  by_cases hlarge : n₀ ≤ n
  · have hacq := (hMq (n + 1) hN)
    have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪ withDensityReal ρ := by
      subst hlam'; exact hacq.1
    have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
      subst hlam'; exact hacq.2
    have hpl : ∀ y, Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y := by
      subst hlam'; exact fun y => (hMp (n + 1) hN y).1
    obtain ⟨hWi, hWB⟩ := hCw n hn lam hlamdef
    have := absorb hd hs0 hsd hβ hρ hn hlamdef hac hMp1 hpb hpl hqb hKg
      (fun y => hn₀ n hlarge hn lam hlamdef y) hWi hWB
    refine this.trans ?_
    have h2 : 2 * Cw ≤ max (2 * Cw) (Mp * (n₀ + 1)) := le_max_left _ _
    have h3 : 2 * Cw * deltaN d s (n + 1) ≤ max (2 * Cw) (Mp * (n₀ + 1)) * deltaN d s (n + 1) :=
      mul_le_mul_of_nonneg_right h2 hδ0
    have h4 : 0 ≤ 2 * Cw * deltaN d s (n + 1) := by positivity
    nlinarith [mul_self_le_mul_self h4 h3]
  · push Not at hlarge
    have hz : ∀ y, |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1| ≤ Mp := by
      intro y
      have := hp0 y; have := hpb y
      rw [abs_le]; constructor <;> linarith
    have hzm : Measurable fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1 :=
      hpm.sub measurable_const
    have hint : Integrable (fun y => (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y - 1) ^ 2)
        (withDensityReal ρ) :=
      Integrable.of_bound (C := Mp ^ 2) (hzm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hz y) 2)
    have h1 : ∫ x, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) ^ 2 ∂(withDensityReal ρ) ≤
        Mp ^ 2 := by
      have := integral_mono hint (integrable_const (Mp ^ 2)) (fun y => by
        simp only
        have := pow_le_pow_left₀ (abs_nonneg _) (hz y) 2
        rwa [sq_abs] at this)
      simpa using this
    refine h1.trans ?_
    have hδ : 1 ≤ (n₀ + 1 : ℝ) * deltaN d s (n + 1) := by
      have hinv := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
      have hnn : ((n + 1 : ℕ) : ℝ) ≤ (n₀ : ℝ) + 1 := by
        have : n + 1 ≤ n₀ := hlarge
        have : ((n + 1 : ℕ) : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast this
        linarith
      have h5 : 1 ≤ ((n₀ : ℝ) + 1) * ((n + 1 : ℕ) : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hN0]; linarith
      exact h5.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
    have h6 : Mp ≤ max (2 * Cw) (Mp * (n₀ + 1)) * deltaN d s (n + 1) := by
      calc Mp = Mp * 1 := (mul_one _).symm
        _ ≤ Mp * ((n₀ + 1 : ℝ) * deltaN d s (n + 1)) := mul_le_mul_of_nonneg_left hδ (by linarith)
        _ = (Mp * (n₀ + 1)) * deltaN d s (n + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0
    nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ Mp) h6]

end EqMarg

end HRS
