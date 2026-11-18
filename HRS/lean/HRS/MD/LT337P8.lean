import HRS.MD.LT337Vocab

/-!
# Packet LT8 (chunk D): Grönwall and Fatou for the localised Coulomb energy identity

`lt8_gronwall_fatou_proof` is the statement `HRS.MD.LT337.lt8_gronwall_fatou` (M L3149-3152), written with the
sorry-free vocabulary copy `HRS.MD.LT337Vocab` (the tie file converts the structure `StoppingFamily`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.MD.LT337Vocab

namespace HRS.MD.LT337P8

variable {d N : ℕ}

/-- Integral Grönwall inequality with an additive forcing term. -/
theorem lt8_gronwall_aff {φ : ℝ → ℝ} {T κ a b : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hφ : ContinuousOn φ (Set.Icc 0 T))
    (h : ∀ t ∈ Set.Icc 0 T, φ t ≤ a + ∫ r in (0 : ℝ)..t, (κ * φ r + b)) :
    ∀ t ∈ Set.Icc 0 T, φ t ≤ Real.exp (κ * T) * (a + b * T) := by
  set cl : ℝ → ℝ := fun r => max 0 (min r T) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ r, cl r ∈ Set.Icc (0 : ℝ) T := fun r => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcle : ∀ r ∈ Set.Icc (0 : ℝ) T, cl r = r := fun r hr => by
    simp only [hcl]; rw [min_eq_left hr.2]; exact max_eq_right hr.1
  set φt : ℝ → ℝ := fun r => φ (cl r) with hφt
  have hφtc : Continuous φt := hφ.comp_continuous hclc hclm
  set G : ℝ → ℝ := fun t => a + ∫ r in (0 : ℝ)..t, (κ * φt r + b) with hG
  have hGd : ∀ x, HasDerivAt G (κ * φt x + b) x := fun x => by
    have hc : Continuous fun r => κ * φt r + b := (continuous_const.mul hφtc).add continuous_const
    have := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
    exact this.const_add a
  have hGφ : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ G t := by
    intro t ht
    have := h t ht
    have e : ∫ r in (0 : ℝ)..t, (κ * φt r + b) = ∫ r in (0 : ℝ)..t, (κ * φ r + b) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le ht.1] at hr
      simp only [hφt]
      rw [hcle r ⟨hr.1, hr.2.trans ht.2⟩]
    simp only [hG]
    rw [e]
    exact this
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := G) (f' := fun x => κ * φt x + b)
    (δ := a) (K := κ) (ε := b) (a := 0) (b := T)
    (fun x _ => (hGd x).continuousAt.continuousWithinAt)
    (fun x _ r hr => (hGd x).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [hG]) (fun x hx => by
      have h1 : φt x = φ x := by simp only [hφt]; rw [hcle x ⟨hx.1, hx.2.le⟩]
      have h2 := hGφ x ⟨hx.1, hx.2.le⟩
      rw [h1]
      nlinarith)
  intro t ht
  have h1 := (hGφ t ht).trans (key t ht)
  rw [sub_zero] at h1
  refine h1.trans ?_
  unfold gronwallBound
  have he : 1 ≤ Real.exp (κ * t) := Real.one_le_exp (mul_nonneg hκ ht.1)
  have hmono : Real.exp (κ * t) ≤ Real.exp (κ * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hκ)
  have hbt : b * t ≤ b * T := mul_le_mul_of_nonneg_left ht.2 hb
  split_ifs with hk
  · subst hk
    simp only [zero_mul, Real.exp_zero, one_mul]
    linarith
  · have hkpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hk)
    have hexp : Real.exp (κ * t) - 1 ≤ κ * t * Real.exp (κ * t) := by
      have := Real.add_one_le_exp (-(κ * t))
      rw [Real.exp_neg] at this
      have hp : 0 < Real.exp (κ * t) := Real.exp_pos _
      have : 1 - κ * t ≤ (Real.exp (κ * t))⁻¹ := by linarith
      calc Real.exp (κ * t) - 1 = Real.exp (κ * t) * (1 - (Real.exp (κ * t))⁻¹) := by field_simp
        _ ≤ Real.exp (κ * t) * (κ * t) := mul_le_mul_of_nonneg_left (by linarith) hp.le
        _ = _ := by ring
    have h3 : b / κ * (Real.exp (κ * t) - 1) ≤ b * t * Real.exp (κ * t) := by
      calc b / κ * (Real.exp (κ * t) - 1) ≤ b / κ * (κ * t * Real.exp (κ * t)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = b * t * Real.exp (κ * t) := by field_simp
    have h4 : a * Real.exp (κ * t) + b * t * Real.exp (κ * t) = Real.exp (κ * t) * (a + b * t) := by ring
    have h5 : Real.exp (κ * t) * (a + b * t) ≤ Real.exp (κ * T) * (a + b * T) := by
      have : 0 ≤ a + b * t := by have := mul_nonneg hb ht.1; linarith
      exact mul_le_mul hmono (by linarith) this (Real.exp_pos _).le
    linarith

/-! ### The stopped time -/

theorem lt8_stopTime_nonneg {t : ℝ} {τ : WithTop ℝ} (ht : 0 ≤ t) (h0 : 0 ≤ τ) : 0 ≤ stopTime t τ := by
  induction τ using WithTop.recTopCoe with
  | top => simpa [stopTime] using ht
  | coe a =>
    have : (0 : ℝ) ≤ a := by exact_mod_cast h0
    simpa [stopTime] using ⟨ht, this⟩

theorem lt8_stopTime_le (t : ℝ) (τ : WithTop ℝ) : stopTime t τ ≤ t := min_le_left _ _

theorem lt8_stopTime_of_lt {r : ℝ} {τ : WithTop ℝ} (h : ((r : ℝ) : WithTop ℝ) < τ) : stopTime r τ = r := by
  induction τ using WithTop.recTopCoe with
  | top => simp [stopTime]
  | coe a =>
    have : r < a := by exact_mod_cast h
    simp [stopTime, this.le]

theorem lt8_stopTime_of_le {t T : ℝ} (htT : t ≤ T) {τ : WithTop ℝ} (h : ((T : ℝ) : WithTop ℝ) ≤ τ) :
    stopTime t τ = t := by
  induction τ using WithTop.recTopCoe with
  | top => simp [stopTime]
  | coe a =>
    have : T ≤ a := by exact_mod_cast h
    simp [stopTime, htT.trans this]

/-! ### The Grönwall step for a fixed localisation -/

theorem lt8_per_eps {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DynData d) (N : ℕ) (T Λ C₀ κ κ' : ℝ) (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (ρ : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) (τ : Ω → WithTop ℝ) (hτ0 : ∀ ω, 0 ≤ τ ω)
    (hI1 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ω))) ω)
        (stopTime t (τ ω))) P)
    (hI2 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ p.2
        then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0)
        ((volume.restrict (Set.Icc (0 : ℝ) t)).prod P))
    (hid : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ ω, correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ω))) ω) (stopTime t (τ ω)) ∂P -
        ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P =
      ∫ r in Set.Icc (0 : ℝ) t, ∫ ω, (if ((r : ℝ) : WithTop ℝ) < τ ω
        then ltDrift D ρ r (X (Real.toNNReal r) ω) else 0) ∂P)
    (hpath : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T,
      0 ≤ correctedEnergy D C₀ Λ ρ (X (Real.toNNReal s) ω) s ∧
      ltDrift D ρ s (X (Real.toNNReal s) ω) ≤
        κ * correctedEnergy D C₀ Λ ρ (X (Real.toNNReal s) ω) s + κ' * D.invβ)
    (hβ : 0 ≤ D.invβ) (hE0 : 0 ≤ ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ ω, correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ω))) ω) (stopTime t (τ ω)) ∂P ≤
        Real.exp (κ * T) * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + κ' * D.invβ * T) := by
  set E0 : ℝ := ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P with hE0def
  set φ : ℝ → ℝ := fun t => ∫ ω, correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ω))) ω)
    (stopTime t (τ ω)) ∂P with hφ
  set g : ℝ → ℝ := fun r => ∫ ω, (if ((r : ℝ) : WithTop ℝ) < τ ω
        then ltDrift D ρ r (X (Real.toNNReal r) ω) else 0) ∂P with hg
  have hgint : IntegrableOn g (Set.Icc (0 : ℝ) T) volume := (hI2 T ⟨hT, le_rfl⟩).integral_prod_left
  have hφid : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t = E0 + ∫ r in (0 : ℝ)..t, g r := by
    intro t ht
    have := hid t ht
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    simp only [hφ, hE0def, hg]
    linarith
  have hφc : ContinuousOn φ (Set.Icc 0 T) := by
    have h1 : ContinuousOn (fun x => ∫ r in (0 : ℝ)..x, g r) (Set.uIcc 0 T) :=
      intervalIntegral.continuousOn_primitive_interval (by rwa [Set.uIcc_of_le hT])
    rw [Set.uIcc_of_le hT] at h1
    exact ((continuousOn_const.add h1)).congr fun t ht => hφid t ht
  have hφnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ φ t := by
    intro t ht
    refine integral_nonneg_of_ae ?_
    filter_upwards [hpath] with ω hω
    exact (hω _ ⟨lt8_stopTime_nonneg ht.1 (hτ0 ω), (lt8_stopTime_le _ _).trans ht.2⟩).1
  have hgle : ∀ r ∈ Set.Icc (0 : ℝ) T, g r ≤ κ * φ r + κ' * D.invβ := by
    intro r hr
    have hv : Integrable (fun ω => κ * correctedEnergy D C₀ Λ ρ
        (X (Real.toNNReal (stopTime r (τ ω))) ω) (stopTime r (τ ω)) + κ' * D.invβ) P :=
      ((hI1 r hr).const_mul κ).add (integrable_const _)
    have hvint : ∫ ω, (κ * correctedEnergy D C₀ Λ ρ
        (X (Real.toNNReal (stopTime r (τ ω))) ω) (stopTime r (τ ω)) + κ' * D.invβ) ∂P =
        κ * φ r + κ' * D.invβ := by
      rw [integral_add ((hI1 r hr).const_mul κ) (integrable_const _), integral_const_mul]
      simp [hφ]
    by_cases hu : Integrable (fun ω => if ((r : ℝ) : WithTop ℝ) < τ ω
        then ltDrift D ρ r (X (Real.toNNReal r) ω) else 0) P
    · rw [← hvint]
      refine integral_mono_ae hu hv ?_
      filter_upwards [hpath] with ω hω
      by_cases hlt : ((r : ℝ) : WithTop ℝ) < τ ω
      · rw [if_pos hlt, lt8_stopTime_of_lt hlt]
        exact (hω r hr).2
      · rw [if_neg hlt]
        have := (hω _ ⟨lt8_stopTime_nonneg hr.1 (hτ0 ω), (lt8_stopTime_le _ _).trans hr.2⟩).1
        have := mul_nonneg hκ this
        have := mul_nonneg hκ' hβ
        linarith
    · have h0 : g r = 0 := integral_undef hu
      rw [h0]
      have := mul_nonneg hκ (hφnn r hr)
      have := mul_nonneg hκ' hβ
      linarith
  have hineq : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ E0 + ∫ r in (0 : ℝ)..t, (κ * φ r + κ' * D.invβ) := by
    intro t ht
    rw [hφid t ht]
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right ht.2
    have hgi : IntegrableOn g (Set.Icc 0 t) := hgint.mono_set hsub
    have hφi : IntegrableOn φ (Set.Icc 0 t) := (hφc.mono hsub).integrableOn_Icc
    have hri : IntegrableOn (fun r => κ * φ r + κ' * D.invβ) (Set.Icc 0 t) :=
      (hφi.const_mul κ).add (integrableOn_const (by simp))
    have h1 : ∫ r in Set.Icc 0 t, g r ≤ ∫ r in Set.Icc 0 t, (κ * φ r + κ' * D.invβ) :=
      setIntegral_mono_on hgi hri measurableSet_Icc (fun r hr => hgle r (hsub hr))
    have e1 : ∫ r in (0 : ℝ)..t, g r = ∫ r in Set.Icc 0 t, g r := by
      rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
    have e2 : ∫ r in (0 : ℝ)..t, (κ * φ r + κ' * D.invβ) =
        ∫ r in Set.Icc 0 t, (κ * φ r + κ' * D.invβ) := by
      rw [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
    rw [e1, e2]
    linarith
  exact lt8_gronwall_aff hT hκ (mul_nonneg hκ' hβ) hE0 hφc hineq

/-! ### The statement -/

theorem lt8_gronwall_fatou_proof (T κ κ' : ℝ) (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (D : DynData d) (N : ℕ) (Λ C₀ : ℝ) (ρ : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N)
        (ℱ : Filtration ℝ mΩ) (τ : ℝ → Ω → WithTop ℝ),
        StoppingFamily P ℱ X T τ → StoppedIdentity P D N T Λ C₀ ρ X τ →
        (∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T,
          0 ≤ correctedEnergy D C₀ Λ ρ (X (Real.toNNReal s) ω) s ∧
          ltDrift D ρ s (X (Real.toNNReal s) ω) ≤
            κ * correctedEnergy D C₀ Λ ρ (X (Real.toNNReal s) ω) s + κ' * D.invβ) →
        Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (C * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + D.invβ)) := by
  refine ⟨Real.exp (κ * T) * max 1 (κ' * T), by positivity, ?_⟩
  intro Ω mΩ P _ D N Λ C₀ ρ X ℱ τ hSF hSI hpath hint0 t ht
  have hβ : 0 ≤ D.invβ := D.hβ
  set E0 : ℝ := ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P with hE0def
  have hE0 : 0 ≤ E0 := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hpath] with ω hω
    simpa using (hω 0 ⟨le_rfl, hT⟩).1
  set c : ℝ → Ω → ℝ := fun s ω => correctedEnergy D C₀ Λ ρ (X (Real.toNNReal s) ω) s with hc
  -- the stopped values
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal
    (c (stopTime t (τ (1 / ((n : ℝ) + 1)) ω)) ω) with hf
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hCbound : ∀ n : ℕ, ∫⁻ ω, f n ω ∂P ≤
      ENNReal.ofReal (Real.exp (κ * T) * max 1 (κ' * T) * (E0 + D.invβ)) := by
    intro n
    have hS := hSI _ (hε n)
    have hI1 := fun s hs => (hS s hs).1
    have hI2 := fun s hs => (hS s hs).2.1
    have hid := fun s hs => (hS s hs).2.2
    have hb := lt8_per_eps P D N T Λ C₀ κ κ' hT hκ hκ' ρ X (τ (1 / ((n : ℝ) + 1)))
      (fun ω => hSF.zero_le _ ω) hI1 hI2 hid hpath hβ hE0 t ht
    have hnn : 0 ≤ᵐ[P] fun ω => c (stopTime t (τ (1 / ((n : ℝ) + 1)) ω)) ω := by
      filter_upwards [hpath] with ω hω
      exact (hω _ ⟨lt8_stopTime_nonneg ht.1 (hSF.zero_le _ ω),
        (lt8_stopTime_le _ _).trans ht.2⟩).1
    have e := ofReal_integral_eq_lintegral_ofReal (hI1 t ht) hnn
    have hmax1 : 1 ≤ max 1 (κ' * T) := le_max_left _ _
    have hmax2 : κ' * T ≤ max 1 (κ' * T) := le_max_right _ _
    have hexp : 0 < Real.exp (κ * T) := Real.exp_pos _
    have key : E0 + κ' * D.invβ * T ≤ max 1 (κ' * T) * (E0 + D.invβ) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hmax1) hE0, mul_nonneg (sub_nonneg.2 hmax2) hβ]
    calc ∫⁻ ω, f n ω ∂P = ENNReal.ofReal (∫ ω, c (stopTime t (τ (1 / ((n : ℝ) + 1)) ω)) ω ∂P) := e.symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
        calc _ ≤ Real.exp (κ * T) * (max 1 (κ' * T) * (E0 + D.invβ)) :=
              mul_le_mul_of_nonneg_left key hexp.le
          _ = _ := by ring
  have hmeas : ∀ n, AEMeasurable (f n) P := fun n => by
    exact (hSI _ (hε n) t ht).1.aemeasurable.ennreal_ofReal
  have hev : ∀ᵐ ω ∂P, ENNReal.ofReal (c t ω) ≤ liminf (fun n => f n ω) atTop := by
    filter_upwards [hSF.exhaust] with ω ⟨ε₀, hε₀, hω⟩
    have hlim : Tendsto (fun n => f n ω) atTop (𝓝 (ENNReal.ofReal (c t ω))) := by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε₀
      filter_upwards [eventually_ge_atTop n₀] with n hn
      have h1 : 1 / ((n : ℝ) + 1) ≤ ε₀ := by
        have : 1 / ((n : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        exact this.trans hn₀.le
      simp only [hf, hc]
      rw [lt8_stopTime_of_le ht.2 (hω _ (hε n) h1)]
    rw [hlim.liminf_eq]
  calc ∫⁻ ω, ENNReal.ofReal (c t ω) ∂P ≤ ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P := lintegral_mono_ae hev
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' hmeas
    _ ≤ _ := by
      refine liminf_le_of_frequently_le' (Frequently.of_forall hCbound)

end HRS.MD.LT337P8
