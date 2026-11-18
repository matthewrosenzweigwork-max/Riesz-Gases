import HRS.MD.EQStatRefMarg
import HRS.Main.EqMargU1

/-!
# EQ-STATIC-U, part 4: `core_L2` uniform in `β ∈ [β₋,β₊]`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.MD.EQStat

open HRS HRS.External HRS.External.RefMarg HRS.External.Calib

variable {d M : ℕ}

set_option maxHeartbeats 1600000 in
theorem eqstat_core_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp)
    {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {c : ℝ} (hc0 : 0 ≤ c)
    (hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q gL Ψ (Λ * c))
    (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqe : ∀ z, q (-z) = q z) (hqi : Integrable q)
    (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c)
    {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s))))
    (hkm : Measurable (fun w => gL w + q w)) (hki : Integrable (fun w => gL w + q w))
    (ĝ : Lattice d → ℝ) (hĝ : ∀ n, 0 ≤ ĝ n)
    (hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) = (ĝ n : ℂ))
    (hκ : KappaSmall βp (Λ * c)) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₁ ≤ N →
      ∀ (ht : ∀ x, |inner ℝ (tN q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ 1),
      firstMarginal (RN q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (RN q (withDensityReal ρ) Ψ β N)).rnDeriv
          (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  set γ : ℝ := Λ * c with hγ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hγ0 : 0 ≤ γ := mul_nonneg hΛ0 hc0
  set Cν : ℝ := Real.exp ((βp * γ + 1) + 0 + βp * γ) with hCν
  have hCν1 : 1 ≤ Cν := Real.one_le_exp (by positivity)
  obtain ⟨CD, ND, hCD0, hD⟩ := eqstat_cavD_torus hd hs0 hsd hΛ1 hqm hq0 hqe hc0 hqc hK0 hw hβm hββ hCν1
  obtain ⟨T₀, c₁, hT₀, hc₁, hconv⟩ := cv_L2_rate hd hs0 hsd hqm hq0 hK0 hw
  set κ₀ : ℝ := 4 * Cν * (βp * γ) with hκ₀
  set E : ℝ := Λ * (2 * (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) + (2 * κ₀) ^ 2 * c₁)) with hE
  have hE0 : 0 ≤ E := by positivity
  set Ccv : ℝ := Real.sqrt E with hCcv
  set Cphi : ℝ := CD + βp * Ccv + βp * (Cν * (Λ * c)) with hCphi
  have hCphi0 : 0 ≤ Cphi := by positivity
  refine ⟨Cν * Cphi, max ND 2, ?_⟩
  intro β hβ1 hβ2 ρ hρ hΛρ N hN ht
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hκβ : KappaSmall β γ := eqstat_kappaSmall_mono hβ.le hβ2 hγ0 hκ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have h := hRef ρ hρ hΛρ
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := theta V lam n with hθdef
  have hθ0 : ∀ x, 0 < θ x := theta_pos V hlam0 n
  have hθm : Measurable θ := measurable_theta V hlam0 n
  have hθ1 : ∫ x, θ x ∂μ = 1 := integral_theta V hlam0 n
  have hθi : Integrable θ μ := integrable_theta V hlam0 n
  have hVq : ∀ x y, V.q x y = q (x - y) := fun _ _ => rfl
  have hβγ : β * γ ≤ βp * γ := mul_le_mul_of_nonneg_right hβ2 hγ0
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cν := by
    show Real.exp ((β * γ + 1) + 0 + β * γ) ≤ Cν
    exact Real.exp_le_exp.2 (by linarith)
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le h hβ.le ht hκβ
  have hκle : weakKappa V β ≤ κ₀ := by
    show 4 * Real.exp ((β * γ + 1) + 0 + β * γ) * (β * γ) ≤ 4 * Cν * (βp * γ)
    have h1 : Real.exp ((β * γ + 1) + 0 + β * γ) ≤ Cν := Real.exp_le_exp.2 (by linarith)
    have h0 : 0 ≤ β * γ := mul_nonneg hβ.le hγ0
    gcongr
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  set ν := cavMarg V lam n with hν
  haveI hνp : IsProbabilityMeasure ν := by
    haveI := isProb_pinnedLaw V hlam0 n (fun e : Empty => e.elim)
    have : IsProbabilityMeasure (cavMarg V lam n) := by unfold cavMarg; infer_instance
    exact this
  have hmono : ∀ a : ℝ, a ≤ Cν → ENNReal.ofReal a • μ ≤ ENNReal.ofReal Cν • μ := fun a ha =>
    Measure.le_iff'.2 fun A => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal ha) le_rfl
  have hπle : firstMarginal (RN q μ Ψ β (n + 1)) ≤ ENNReal.ofReal Cν • μ :=
    (firstMarginal_RN_leK h hβ hN0 ht).trans (hmono _ (Real.exp_le_exp.2 (by linarith)))
  have hπeq := firstMarginal_RN_eq h hβ ht (n := n)
  rw [← hV] at hπeq
  have hνle : ν ≤ ENNReal.ofReal Cν • μ := by
    have := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simp) (fun e : Empty => e.elim) 0
    exact this.trans (hmono _ hVC)
  haveI : IsFiniteMeasure (firstMarginal (RN q μ Ψ β (n + 1))) :=
    ⟨lt_of_le_of_lt (hπle Set.univ) (by simp [Measure.smul_apply])⟩
  have hπ_ac := PoleCavityAux.rnDeriv_le_of_le_withDensity μ (firstMarginal (RN q μ Ψ β (n + 1)))
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hπle)
  have hrn : (firstMarginal (RN q μ Ψ β (n + 1))).rnDeriv μ =ᵐ[μ] fun y => ENNReal.ofReal (θ y) := by
    rw [hπeq]; exact Measure.rnDeriv_withDensity μ (ENNReal.measurable_ofReal.comp hθm)
  have hθC : ∀ᵐ y ∂μ, θ y ≤ Cν := by
    filter_upwards [hrn, hπ_ac.2] with y h1 h2
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h2
  refine ⟨hπ_ac.1, ?_⟩
  have hfin : (fun y => ((firstMarginal (RN q μ Ψ β (n + 1))).rnDeriv μ y).toReal - 1) =ᵐ[μ]
      fun y => θ y - 1 := by
    filter_upwards [hrn] with y h1
    rw [h1, ENNReal.toReal_ofReal (hθ0 y).le]
  rw [eLpNorm_congr_ae hfin]
  have hCz : ∀ᵐ y ∂μ, |θ y - 1| ≤ Cν := hθC.mono fun y hy => by
    rw [abs_le]; constructor <;> linarith [hθ0 y]
  obtain ⟨c', hc'⟩ := cavity_equation h hβ ht (n := n) (Cz := Cν) hCz
  -- clipped densities
  have hCν0 : 0 ≤ Cν := by linarith
  set θc : Torus d → ℝ := fun y => min (θ y) Cν with hθc
  have hθcm : Measurable θc := hθm.min measurable_const
  have hθc0 : ∀ y, 0 ≤ θc y := fun y => le_min (hθ0 y).le hCν0
  have hθcb : ∀ y, θc y ≤ Cν := fun y => min_le_right _ _
  have hθc_ae : ∀ᵐ y ∂μ, θc y = θ y := hθC.mono fun y hy => min_eq_left hy
  have hνac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hνle
  haveI : IsFiniteMeasure ν := inferInstance
  have hν_rn := PoleCavityAux.rnDeriv_le_of_le_withDensity μ ν (fun _ => ENNReal.ofReal Cν)
    (by rw [withDensity_const]; exact hνle)
  set θ' : Torus d → ℝ := fun y => (ν.rnDeriv μ y).toReal with hθ'
  set θ'c : Torus d → ℝ := fun y => min (θ' y) Cν with hθ'c
  have hθ'm : Measurable θ' := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hθ'cm : Measurable θ'c := hθ'm.min measurable_const
  have hθ'c0 : ∀ y, 0 ≤ θ'c y := fun y => le_min ENNReal.toReal_nonneg hCν0
  have hθ'cb : ∀ y, θ'c y ≤ Cν := fun y => min_le_right _ _
  have hνeq : ν = μ.withDensity (fun y => ENNReal.ofReal (θ'c y)) := by
    calc ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ hνac).symm
      _ = _ := by
        refine withDensity_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top ν μ, hν_rn.2] with y h1 h2
        have h3 : (ν.rnDeriv μ y).toReal ≤ Cν := ENNReal.toReal_le_of_le_ofReal hCν0 h2
        simp only [hθ'c, hθ', min_eq_left h3, ENNReal.ofReal_toReal h1.ne]
  have hπeq' : firstMarginal (RN q μ Ψ β (n + 1)) = μ.withDensity (fun y => ENNReal.ofReal (θc y)) := by
    rw [hπeq]
    refine withDensity_congr_ae ?_
    filter_upwards [hθc_ae] with y hy
    rw [hy]
  have hθci : Integrable θc μ := Integrable.of_bound hθcm.aestronglyMeasurable Cν
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθc0 y)]; exact hθcb y)
  have hθ'ci : Integrable θ'c μ := Integrable.of_bound hθ'cm.aestronglyMeasurable Cν
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hθ'c0 y)]; exact hθ'cb y)
  have hTV0 : ∫ y, |θc y - θ'c y| ∂μ ≤ 2 * (weakKappa V β / ((n + 1 : ℕ) : ℝ)) := by
    refine integral_abs_sub_le hθcm hθ'cm hθc0 hθ'c0 hθci hθ'ci (fun A hA => ?_)
    rw [← hπeq', ← hνeq]
    exact event_pi_nu h hβ ht hκV hA
  -- the convolution term
  set w : Torus d → ℝ := fun y => ρ y * (θc y - θ'c y) with hw
  have hcvid : ∀ x, (∫ y, q (x - y) * θ y ∂μ) - ∫ y, q (x - y) ∂ν = ResponseAux.cv q w x := by
    intro x
    have e1 : ∫ y, q (x - y) * θ y ∂μ = ∫ y, q (x - y) * θc y ∂μ :=
      integral_congr_ae (hθc_ae.mono fun y hy => by show q (x - y) * θ y = q (x - y) * θc y; rw [hy])
    rw [e1]
    have := cv_identity hρ hΛρ hqm hq0 hqi hθcm hθ'cm hθc0 hθ'c0 hθcb hθ'cb x
    rw [← hνeq] at this
    exact this
  set Dfun : Torus d → ℝ := fun x => Real.log (cavU V lam n (fun e : Empty => e.elim) x) +
    lam * n * ∫ y, V.q y x ∂ν with hDfun
  set Qν : Torus d → ℝ := fun x => ∫ y, q (x - y) ∂ν with hQν
  set Φ : Torus d → ℝ := fun x => Dfun x + β * ResponseAux.cv q w x + lam * Qν x with hΦ
  have heq : ∀ x, Real.log (θ x) + β * ResponseAux.Kt (fun w => gL w + q w) μ (fun y => θ y - 1) x =
      Φ x + c' := by
    intro x
    rw [hc' x]
    simp only [hΦ, hDfun, hQν]
    rw [← hcvid x]
  -- the rate `δ = N⁻¹ g(N)`
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ n + 1 := by omega
    show (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)
    exact_mod_cast this
  have hNpos : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hδ : deltaN d s (n + 1) = N⁻¹ * gFun d s N := deltaN_eq_gFun hd hs0 hsd (by omega)
  have hg1 : 1 ≤ gFun d s N := one_le_gFun hd hs0 hsd hN1
  set δ : ℝ := deltaN d s (n + 1) with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδ1 : N⁻¹ ≤ δ := by
    rw [hδ]
    calc N⁻¹ = N⁻¹ * 1 := (mul_one _).symm
      _ ≤ N⁻¹ * gFun d s N := by gcongr
  have hlam_le : lam ≤ βp * δ := by
    have : lam = β * N⁻¹ := by rw [hlam]; ring
    rw [this]; gcongr
  -- the cavity correction `D`
  have hDb : ∀ x, 0 ≤ Dfun x ∧ Dfun x ≤ CD * δ := fun x =>
    hD hβ1 hβ2 ρ hρ hΛρ V hVq hVC hκV (n + 1) n (by omega) (Nat.le_succ n) x
  have hDm : Measurable Dfun := by
    refine ((Real.measurable_log.comp (measurable_cavU V hlam0 n _)).add (measurable_const.mul ?_))
    exact measurable_integral_kernel (F := fun p : Torus d × Torus d => V.q p.2 p.1)
      (V.measurable_q.comp (measurable_snd.prodMk measurable_fst))
  have hDL2 : eLpNorm Dfun 2 μ ≤ ENNReal.ofReal (CD * δ) :=
    eLpNorm_two_le_const hDm.aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (hDb x).1]; exact (hDb x).2
  -- the convolution term
  have hwm : Measurable w := hρ.measurable.mul (hθcm.sub hθ'cm)
  have hcvm : Measurable (ResponseAux.cv q w) := by
    unfold ResponseAux.cv
    exact measurable_integral_kernel (F := fun p : Torus d × Torus d => q (p.1 - p.2) * w p.2)
      ((hqm.comp (measurable_fst.sub measurable_snd)).mul (hwm.comp measurable_snd))
  have hκ0 : 0 ≤ weakKappa V β := weakKappa_nonneg V hβ.le
  set η : ℝ := 2 * (κ₀ / N) with hη
  have hη0 : 0 ≤ η := by positivity
  have hTV : ∫ y, |θc y - θ'c y| ∂μ ≤ η := by
    refine hTV0.trans ?_
    rw [hη]; gcongr
  have hb : ∀ y, |θc y - θ'c y| ≤ Cν := fun y => by
    rw [abs_le]; constructor <;> linarith [hθc0 y, hθ'c0 y, hθcb y, hθ'cb y]
  have h1 := hconv ρ hρ hΛρ hΛ0 hθcm hθ'cm hCν0 hb hη0 hTV (N := n + 1) (by omega)
  have hE' : Λ * (2 * ((T₀ * (N⁻¹ * gFun d s N)) ^ 2 * (Λ * Cν * η) + η ^ 2 * (c₁ * gFun d s N))) ≤
      E * δ ^ 2 := by
    have ha0 : 0 < N⁻¹ := inv_pos.2 hNpos
    have ha1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    set a : ℝ := N⁻¹ with ha
    set g : ℝ := gFun d s N with hg
    have hηa : η = 2 * κ₀ * a := by rw [hη, div_eq_mul_inv]; ring
    have hX : δ ^ 2 = (a * g) ^ 2 := by rw [hδ]
    have hX0 : 0 ≤ (a * g) ^ 2 := sq_nonneg _
    have t1 : (T₀ * (a * g)) ^ 2 * (Λ * Cν * η) ≤ T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 := by
      rw [hηa]
      have : (T₀ * (a * g)) ^ 2 * (Λ * Cν * (2 * κ₀ * a)) =
          (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * a := by ring
      rw [this]
      have hnn : 0 ≤ T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 := by positivity
      calc (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * a ≤ (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left ha1 hnn
        _ = _ := mul_one _
    have t2 : η ^ 2 * (c₁ * g) ≤ (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2 := by
      rw [hηa]
      have : (2 * κ₀ * a) ^ 2 * (c₁ * g) = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) := by ring
      rw [this]
      have : (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2 = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) * g := by ring
      rw [this]
      have hnn : 0 ≤ (2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g) := by positivity
      calc (2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g) = ((2 * κ₀) ^ 2 * c₁ * (a ^ 2 * g)) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hg1 hnn
    rw [hX]
    calc Λ * (2 * ((T₀ * (a * g)) ^ 2 * (Λ * Cν * η) + η ^ 2 * (c₁ * g)))
        ≤ Λ * (2 * (T₀ ^ 2 * (Λ * Cν * (2 * κ₀)) * (a * g) ^ 2 + (2 * κ₀) ^ 2 * c₁ * (a * g) ^ 2)) := by
          gcongr
      _ = E * (a * g) ^ 2 := by rw [hE]; ring
  have hAE : AEStronglyMeasurable (ResponseAux.cv q w) μ := hcvm.aestronglyMeasurable
  have hsq : (eLpNorm (ResponseAux.cv q w) 2 μ) ^ 2 ≤ ENNReal.ofReal (Ccv * δ) ^ 2 := by
    rw [ResponseAux.eLpNorm_two_sq hAE, ← ENNReal.ofReal_pow (by positivity), mul_pow, hCcv,
      Real.sq_sqrt hE0]
    exact h1.trans (ENNReal.ofReal_le_ofReal hE')
  have hcvL2 : eLpNorm (ResponseAux.cv q w) 2 μ ≤ ENNReal.ofReal (Ccv * δ) :=
    (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hsq
  -- the `λ q*ν` term
  have hQνm : Measurable Qν := measurable_integral_kernel (F := fun p : Torus d × Torus d => q (p.1 - p.2))
    (hqm.comp (measurable_fst.sub measurable_snd))
  have hQb : ∀ x, 0 ≤ Qν x ∧ Qν x ≤ Cν * (Λ * c) := fun x =>
    ⟨integral_nonneg fun y => hq0 _, integral_kernel_le hΛρ hΛ0 hνle hCν0 hqm hq0 hc0 hqc x⟩
  have hQL2 : eLpNorm (fun x => lam * Qν x) 2 μ ≤ ENNReal.ofReal (βp * (Cν * (Λ * c)) * δ) :=
    eLpNorm_two_le_const (hQνm.const_mul lam).aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (mul_nonneg hlam0 (hQb x).1)]
      calc lam * Qν x ≤ (βp * δ) * (Cν * (Λ * c)) :=
            mul_le_mul hlam_le (hQb x).2 (hQb x).1 (by positivity)
        _ = _ := by ring
  -- Minkowski
  have hΦe : Φ = (Dfun + fun x => β * ResponseAux.cv q w x) + fun x => lam * Qν x := by
    funext x; simp [hΦ]
  have hΦnorm : eLpNorm Φ 2 μ ≤ ENNReal.ofReal (Cphi * δ) := by
    have m1 : AEStronglyMeasurable Dfun μ := hDm.aestronglyMeasurable
    have m2 : AEStronglyMeasurable (fun x => β * ResponseAux.cv q w x) μ :=
      (hcvm.const_mul β).aestronglyMeasurable
    have m3 : AEStronglyMeasurable (fun x => lam * Qν x) μ := (hQνm.const_mul lam).aestronglyMeasurable
    have e2 : eLpNorm (fun x => β * ResponseAux.cv q w x) 2 μ =
        ENNReal.ofReal β * eLpNorm (ResponseAux.cv q w) 2 μ := by
      have := eLpNorm_const_smul (p := 2) (μ := μ) β (ResponseAux.cv q w)
      rw [show (fun x => β * ResponseAux.cv q w x) = β • ResponseAux.cv q w from rfl, this,
        Real.enorm_of_nonneg hβ.le]
    rw [hΦe]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine (add_le_add_left (eLpNorm_add_le (by norm_num)) _).trans ?_
    rw [e2]
    calc eLpNorm Dfun 2 μ + ENNReal.ofReal β * eLpNorm (ResponseAux.cv q w) 2 μ +
          eLpNorm (fun x => lam * Qν x) 2 μ
        ≤ ENNReal.ofReal (CD * δ) + ENNReal.ofReal βp * ENNReal.ofReal (Ccv * δ) +
          ENNReal.ofReal (βp * (Cν * (Λ * c)) * δ) := by
          gcongr
      _ = ENNReal.ofReal (Cphi * δ) := by
          rw [← ENNReal.ofReal_mul hβp.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [hCphi]; ring
  have hΦm : Measurable Φ := (hDm.add (hcvm.const_mul β)).add (hQνm.const_mul lam)
  have hΦmem : MemLp Φ 2 μ := lt_of_le_of_lt hΦnorm ENNReal.ofReal_lt_top
  -- absorption
  have habs := absorption hρ hΛρ hkm hki ĝ hĝ hcoef hβ.le hθm hθ0 hCν1 hθC hθ1 hΦmem heq
  refine habs.trans ?_
  calc ENNReal.ofReal Cν * eLpNorm Φ 2 μ ≤ ENNReal.ofReal Cν * ENNReal.ofReal (Cphi * δ) := by gcongr
    _ = ENNReal.ofReal (Cν * Cphi * δ) := by
        rw [← ENNReal.ofReal_mul hCν0]; congr 1; ring


variable {d : ℕ}

theorem eqstat_reference_marginal_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hκ : KappaSmall βp (Λ * (weakSplit d s τ L).c))
    {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₀ ≤ N →
      firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)).rnDeriv
            (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8, h9, h10, -, -, h13, -, h15, -, -⟩ :=
    weakSplit_spec hd hs0 hsd hτ hτ1 L
  set c : ℝ := (weakSplit d s τ L).c with hc
  set q : Torus d → ℝ := (weakSplit d s τ L).q with hq
  set gL : Torus d → ℝ := (weakSplit d s τ L).gL with hgL
  obtain ⟨B, hB0, hB⟩ := h15
  obtain ⟨K0, hK0, hw⟩ := weakLp_of_envelope hd hs0 hsd hB0 hB
  have hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c := by
    have := ofReal_integral_eq_lintegral_ofReal h7 (Filter.Eventually.of_forall h6)
    rw [h8] at this
    exact le_of_eq this.symm
  have hgLi : Integrable gL := h13.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace gL)
  have hkm : Measurable (fun w => gL w + q w) := h13.measurable.add h5
  have hki : Integrable (fun w => gL w + q w) := hgLi.add h7
  set ĝ : Lattice d → ℝ := fun n => rieszCoeff d s n + (if n = 0 then c else 0) with hĝdef
  have hĝ : ∀ n, 0 ≤ ĝ n := by
    intro n
    by_cases hn : n = 0
    · simp [hĝdef, hn, rieszCoeff, h10]
    · have := rieszCoeff_pos hd hs0 hsd n hn
      simp [hĝdef, hn]; exact this.le
  have hcoef : ∀ n, ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) = (ĝ n : ℂ) := by
    intro n
    have e1 : ∫ x, Torus.mode (-n) x * (((gL x + q x : ℝ)) : ℂ) =
        ∫ x, (Torus.mode (-n) x * ((periodicRiesz d s x : ℝ) : ℂ) + Torus.mode (-n) x * (c : ℂ)) := by
      refine integral_congr_ae ?_
      filter_upwards [h4] with x hx
      rw [← mul_add]
      congr 1
      rw [hx]; push_cast; ring
    rw [e1]
    have hgi : Integrable (fun x => Torus.mode (-n) x * ((periodicRiesz d s x : ℝ) : ℂ)) := by
      have := (KernelAux.integrable_periodicRiesz hd hs0 hsd).ofReal (𝕜 := ℂ)
      exact this.bdd_mul (c := 1) (Torus.continuous_mode (-n)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-n) x).le)
    have hci : Integrable (fun x => Torus.mode (-n) x * (c : ℂ)) := by
      have : Integrable (fun x => Torus.mode (-n) x) :=
        (integrable_const (1 : ℂ)).bdd_mul (c := 1) (Torus.continuous_mode (-n)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-n) x).le) |>.congr
          (Filter.Eventually.of_forall fun x => by simp)
      exact this.mul_const _
    rw [integral_add hgi hci, KernelAux.integral_periodicRiesz_mode hd hs0 hsd n, integral_mul_const,
      Torus.integral_mode (-n)]
    by_cases hn : n = 0
    · simp [hĝdef, hn, rieszCoeff]
    · have : -n ≠ 0 := neg_ne_zero.2 hn
      simp [hĝdef, hn, this]
  have hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q gL Ψ (Λ * c) := fun ρ hρ hΛρ =>
    refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  obtain ⟨C, N₁, hcore⟩ := eqstat_core_L2 hd hs0 hsd hΛ1 hβm hββ h10 hRef h5 h6 (hQ_even hd hs0 hsd τ L) h7 hqc hK0 hw
    hkm hki ĝ hĝ hcoef hκ
  obtain ⟨N₂, hsmall⟩ := HRS.EqMarg.eqmarg_small_calib hd hs0 hsd hτ hτ1 L hΛ1 Ψ hΨ βp (lt_of_lt_of_le hβm hββ)
  refine ⟨C, max N₁ N₂, fun {β} hβ1 hβ2 ρ hρ hΛρ N hN => ?_⟩
  exact hcore hβ1 hβ2 ρ hρ hΛρ N (le_trans (le_max_left _ _) hN)
    (fun x => hsmall β (lt_of_lt_of_le hβm hβ1) hβ2 ρ hρ hΛρ N (le_trans (le_max_right _ _) hN) x)

end HRS.MD.EQStat

end
