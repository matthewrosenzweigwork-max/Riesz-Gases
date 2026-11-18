import HRS.MS.S111X2Aux47

/-!
# S11.1 terminal wave, part 1: cubic source interface, forcing history (T05) and norm assembly (T10)

Statements copied from Pro's `S11.1-Tensor` skeleton (`CubicSources`, `PhysicalCubicSources`, T05, T10) and checked against
the live frozen types (`IsR2CrossDensities`, `commutatorKernel`, `projTensor`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111T

open HRS.Whole
open HRS (Euc)

/-- Exact remaining source-lift interface (Pro `CubicSources`): initial tensor, drift and covariance cumulative sources. -/
structure CubicSources (d : ℕ) (T u : ℝ) (kappa : projTensor (R2X d T) 3) where
  initial : projTensor (R2X d T) 3
  drift : ℝ → projTensor (R2X d T) 3
  covariance : ℝ → projTensor (R2X d T) 3
  drift_zero : drift 0 = 0
  covariance_zero : covariance 0 = 0
  drift_continuous : ContinuousOn drift (Set.Icc 0 (u + T))
  covariance_continuous : ContinuousOn covariance (Set.Icc 0 (u + T))
  drift_bv : eVariationOn drift (Set.Icc 0 (u + T)) < ⊤
  covariance_bv : eVariationOn covariance (Set.Icc 0 (u + T)) < ⊤
  represents : kappa = initial + drift (u + T) + covariance (u + T)

/-- Physical part of the source-lift interface (Pro `PhysicalCubicSources`). -/
structure PhysicalCubicSources (d : ℕ) (s a beta gamma : ℝ)
    (rho : Euc d → ℝ) (T u : ℝ) (kappa : projTensor (R2X d T) 3)
    extends CubicSources d T u kappa where
  initial_eval : ∀ tau : Fin 3 → Set.Icc (0 : ℝ) T,
    ∀ phi : Fin 3 → Euc d → ℝ, (∀ i, IsOscTest (wholeSpaceIndex d) (phi i)) →
    ∀ M : (R2X d T) [×3]→L[ℝ] ℝ,
      (∀ w : Fin 3 → R2X d T, M w = ∏ i, OscDual.eval (OscPath.at' (w i) (tau i)) (phi i)) →
      let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
      let mu := HRS.Whole.withDensityReal rho
      let h := fun i => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) mu gamma
        (propagatorW C 0 (u + tau i) (phi i))
      (initial : TensorDual (R2X d T) 3) M = ∫ x, h 0 x * h 1 x * h 2 x ∂mu
  drift_eval : ∀ tau : Fin 3 → Set.Icc (0 : ℝ) T,
    ∀ phi : Fin 3 → Euc d → ℝ, (∀ i, IsOscTest (wholeSpaceIndex d) (phi i)) →
    ∀ chi : Fin 3 → ℝ → Euc d → ℝ,
      IsR2CrossDensities d s a beta gamma rho T u tau phi chi →
      ∀ M : (R2X d T) [×3]→L[ℝ] ℝ,
      (∀ w : Fin 3 → R2X d T, M w = ∏ i, OscDual.eval (OscPath.at' (w i) (tau i)) (phi i)) →
      let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
      ∀ v ∈ Set.Icc 0 (u + T),
        (drift v : TensorDual (R2X d T) 3) M =
          -∑ i : Fin 3, ∫ r in Set.Icc 0 (min v (u + tau i)),
            ∫ x, ∫ y, commutatorKernel d s
              (gradient (propagatorW C r (u + tau i) (phi i))) x y *
                chi (i + 1) r x * chi (i + 2) r y
  covariance_eval : ∀ tau : Fin 3 → Set.Icc (0 : ℝ) T,
    ∀ phi : Fin 3 → Euc d → ℝ, (∀ i, IsOscTest (wholeSpaceIndex d) (phi i)) →
    ∀ chi : Fin 3 → ℝ → Euc d → ℝ,
      IsR2CrossDensities d s a beta gamma rho T u tau phi chi →
      ∀ M : (R2X d T) [×3]→L[ℝ] ℝ,
      (∀ w : Fin 3 → R2X d T, M w = ∏ i, OscDual.eval (OscPath.at' (w i) (tau i)) (phi i)) →
      let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
      ∀ v ∈ Set.Icc 0 (u + T),
        (covariance v : TensorDual (R2X d T) 3) M =
          (2 / beta) * ∑ i : Fin 3,
            ∫ r in Set.Icc 0 (min v (min (u + tau i) (u + tau (i + 1)))),
              ∫ x, inner ℝ
                (gradient (propagatorW C r (u + tau i) (phi i)) x)
                (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x) *
                  chi (i + 2) r x

/-- **T05.** Integration of the forcing history, including coincident rates (any strict subrate works). -/
theorem s111t_forcing_history (T c0 kappa c : ℝ)
    (hT : 0 ≤ T) (hc0 : 0 < c0) (hkappa : 0 < kappa)
    (hc : 0 < c) (hc1 : c < c0) (hc2 : c < kappa) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 ≤ u →
      (∫ v in Set.Icc 0 (u + T),
        Real.exp (-c0 * max (u - v) 0) * Real.exp (-kappa * v)) ≤
          B * Real.exp (-c * u) := by
  set c1 : ℝ := (c + min c0 kappa) / 2 with hc1def
  have hmin : c < min c0 kappa := lt_min hc1 hc2
  have hcc1 : c < c1 := by rw [hc1def]; linarith
  have hc1m : c1 ≤ min c0 kappa := by rw [hc1def]; linarith
  have hc1a : c1 ≤ c0 := hc1m.trans (min_le_left _ _)
  have hc1b : c1 ≤ kappa := hc1m.trans (min_le_right _ _)
  set δ : ℝ := c1 - c with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  refine ⟨1 / δ + T, by positivity, fun u hu => ?_⟩
  have hpt : ∀ v ∈ Set.Icc 0 (u + T),
      Real.exp (-c0 * max (u - v) 0) * Real.exp (-kappa * v) ≤ Real.exp (-c1 * u) := by
    intro v hv
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hv0 : 0 ≤ v := hv.1
    have hm0 : 0 ≤ max (u - v) 0 := le_max_right _ _
    have hm1 : u - v ≤ max (u - v) 0 := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hc1a hm0, mul_le_mul_of_nonneg_right hc1b hv0]
  have hmeas : MeasureTheory.IntegrableOn
      (fun v => Real.exp (-c0 * max (u - v) 0) * Real.exp (-kappa * v)) (Set.Icc 0 (u + T)) := by
    have hcont : Continuous (fun v : ℝ => Real.exp (-c0 * max (u - v) 0) * Real.exp (-kappa * v)) := by
      fun_prop
    exact hcont.continuousOn.integrableOn_Icc
  have h1 : (∫ v in Set.Icc 0 (u + T),
        Real.exp (-c0 * max (u - v) 0) * Real.exp (-kappa * v)) ≤
      ∫ v in Set.Icc 0 (u + T), Real.exp (-c1 * u) := by
    apply MeasureTheory.setIntegral_mono_on hmeas (by simp) measurableSet_Icc hpt
  have h2 : (∫ v in Set.Icc 0 (u + T), Real.exp (-c1 * u)) = (u + T) * Real.exp (-c1 * u) := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
    simp [smul_eq_mul]
  have h3 : (u + T) * Real.exp (-c1 * u) ≤ (1 / δ + T) * Real.exp (-c * u) := by
    have hexp : Real.exp (-c1 * u) = Real.exp (-c * u) * Real.exp (-δ * u) := by
      rw [← Real.exp_add]; congr 1; rw [hδ]; ring
    have hu1 : u * Real.exp (-δ * u) ≤ 1 / δ := by
      have : δ * u ≤ Real.exp (δ * u) := by
        have := Real.add_one_le_exp (δ * u); linarith
      have hpos : 0 < Real.exp (δ * u) := Real.exp_pos _
      rw [le_div_iff₀ hδpos]
      have e1 : Real.exp (-δ * u) * Real.exp (δ * u) = 1 := by
        rw [← Real.exp_add]; simp
      calc u * Real.exp (-δ * u) * δ = (δ * u) * Real.exp (-δ * u) := by ring
        _ ≤ Real.exp (δ * u) * Real.exp (-δ * u) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        _ = 1 := by rw [mul_comm]; exact e1
    have hu2 : Real.exp (-δ * u) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; nlinarith
    rw [hexp]
    have hE : 0 < Real.exp (-c * u) := Real.exp_pos _
    calc (u + T) * (Real.exp (-c * u) * Real.exp (-δ * u))
        = (u * Real.exp (-δ * u) + T * Real.exp (-δ * u)) * Real.exp (-c * u) := by ring
      _ ≤ (1 / δ + T * 1) * Real.exp (-c * u) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        exact add_le_add hu1 (mul_le_mul_of_nonneg_left hu2 hT)
      _ = (1 / δ + T) * Real.exp (-c * u) := by ring
  exact h1.trans (h2.le.trans h3)

/-- A function of bounded variation vanishing at `0` is controlled pointwise by its variation. -/
theorem s111t_norm_le_var {E : Type*} [NormedAddCommGroup E] (g : ℝ → E) (H x : ℝ) (hx : x ∈ Set.Icc 0 H)
    (hg0 : g 0 = 0) (R : ℝ) (hR0 : 0 ≤ R) (hR : eVariationOn g (Set.Icc 0 H) ≤ ENNReal.ofReal R) :
    ‖g x‖ ≤ R := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 H := ⟨le_rfl, hx.1.trans hx.2⟩
  have h := (eVariationOn.edist_le g hx h0).trans hR
  rw [hg0, edist_zero_right, ← ofReal_norm_eq_enorm] at h
  exact (ENNReal.ofReal_le_ofReal_iff hR0).mp h

/-- **T10.** Norm assembly after the actual source lift: the common `C` precedes `u`, the two tensors and their
source representations. -/
theorem s111t_source_norm_to_relaxation (d : ℕ) (T c0 kappa c C0 : ℝ)
    (hT : 0 < T) (hc0 : 0 < c0) (hkappa : 0 < kappa)
    (hc : 0 < c) (hc1 : c < c0) (hc2 : c < kappa) (hC0 : 0 ≤ C0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u →
      ∀ Ku Kb : projTensor (R2X d T) 3,
      ∀ Su : CubicSources d T u Ku, ∀ Sb : CubicSources d T u Kb,
      ‖Su.initial - Sb.initial‖ ≤ C0 * Real.exp (-3 * c0 * u) →
      eVariationOn (fun v => Su.drift v - Sb.drift v) (Set.Icc 0 (u + T)) ≤
        ENNReal.ofReal (C0 * ∫ v in Set.Icc 0 (u + T),
          Real.exp (-c0 * max (u - v) 0) * Real.exp (-kappa * v)) →
      eVariationOn (fun v => Su.covariance v - Sb.covariance v) (Set.Icc 0 (u + T)) ≤
        ENNReal.ofReal (C0 * ∫ v in Set.Icc 0 (u + T),
          Real.exp (-2 * c0 * max (u - v) 0) * Real.exp (-kappa * v)) →
      ‖Ku - Kb‖ ≤ C * Real.exp (-c * u) := by
  obtain ⟨B1, hB1, h1⟩ := s111t_forcing_history T c0 kappa c hT.le hc0 hkappa hc hc1 hc2
  obtain ⟨B2, hB2, h2⟩ := s111t_forcing_history T (2 * c0) kappa c hT.le (by linarith) hkappa hc
    (by linarith) hc2
  refine ⟨C0 + C0 * B1 + C0 * B2, by positivity, fun u hu Ku Kb Su Sb hI hD hJ => ?_⟩
  have hmem : u + T ∈ Set.Icc 0 (u + T) := ⟨by linarith, le_rfl⟩
  have hint1 : 0 ≤ ∫ v in Set.Icc 0 (u + T),
      Real.exp (-c0 * max (u - v) 0) * Real.exp (-kappa * v) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun v _ => by positivity)
  have hint2 : 0 ≤ ∫ v in Set.Icc 0 (u + T),
      Real.exp (-2 * c0 * max (u - v) 0) * Real.exp (-kappa * v) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun v _ => by positivity)
  have hd := s111t_norm_le_var (fun v => Su.drift v - Sb.drift v) (u + T) (u + T) hmem
    (by simp [Su.drift_zero, Sb.drift_zero]) _ (by positivity) hD
  have hc' := s111t_norm_le_var (fun v => Su.covariance v - Sb.covariance v) (u + T) (u + T) hmem
    (by simp [Su.covariance_zero, Sb.covariance_zero]) _ (by positivity) hJ
  have e2 : (∫ v in Set.Icc 0 (u + T),
      Real.exp (-2 * c0 * max (u - v) 0) * Real.exp (-kappa * v)) =
      ∫ v in Set.Icc 0 (u + T), Real.exp (-(2 * c0) * max (u - v) 0) * Real.exp (-kappa * v) := by
    congr 1; ext v; congr 2; ring
  have hdec : Ku - Kb = (Su.initial - Sb.initial) + (Su.drift (u + T) - Sb.drift (u + T)) +
      (Su.covariance (u + T) - Sb.covariance (u + T)) := by
    have e1 := Su.represents
    have e2 := Sb.represents
    calc Ku - Kb = (Su.initial + Su.drift (u + T) + Su.covariance (u + T)) -
        (Sb.initial + Sb.drift (u + T) + Sb.covariance (u + T)) := by rw [← e1, ← e2]
      _ = _ := by abel
  have hexp3 : Real.exp (-3 * c0 * u) ≤ Real.exp (-c * u) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have hI' : ‖Su.initial - Sb.initial‖ ≤ C0 * Real.exp (-c * u) :=
    hI.trans (mul_le_mul_of_nonneg_left hexp3 hC0)
  have hD' : ‖Su.drift (u + T) - Sb.drift (u + T)‖ ≤ C0 * B1 * Real.exp (-c * u) := by
    calc _ ≤ C0 * ∫ v in Set.Icc 0 (u + T),
          Real.exp (-c0 * max (u - v) 0) * Real.exp (-kappa * v) := hd
      _ ≤ C0 * (B1 * Real.exp (-c * u)) := mul_le_mul_of_nonneg_left (h1 u hu) hC0
      _ = _ := by ring
  have hJ' : ‖Su.covariance (u + T) - Sb.covariance (u + T)‖ ≤ C0 * B2 * Real.exp (-c * u) := by
    calc _ ≤ C0 * ∫ v in Set.Icc 0 (u + T),
          Real.exp (-2 * c0 * max (u - v) 0) * Real.exp (-kappa * v) := hc'
      _ = C0 * ∫ v in Set.Icc 0 (u + T),
          Real.exp (-(2 * c0) * max (u - v) 0) * Real.exp (-kappa * v) := by rw [e2]
      _ ≤ C0 * (B2 * Real.exp (-c * u)) := mul_le_mul_of_nonneg_left (h2 u hu) hC0
      _ = _ := by ring
  rw [hdec]
  calc _ ≤ ‖Su.initial - Sb.initial‖ + ‖Su.drift (u + T) - Sb.drift (u + T)‖ +
        ‖Su.covariance (u + T) - Sb.covariance (u + T)‖ := norm_add₃_le
    _ ≤ C0 * Real.exp (-c * u) + C0 * B1 * Real.exp (-c * u) + C0 * B2 * Real.exp (-c * u) :=
      add_le_add (add_le_add hI' hD') hJ'
    _ = _ := by ring

end HRS.MS.S111T
