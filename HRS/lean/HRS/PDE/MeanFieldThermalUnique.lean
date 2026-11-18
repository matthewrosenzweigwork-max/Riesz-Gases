import HRS.PDE.MeanFieldAux

/-!
# Uniqueness of the thermal equilibrium (package MF-01, packet MF-TH-U)

Strict convexity of the entropy and nonnegativity of the zero-mass interaction form give a unique
thermal equilibrium (proof of Proposition 5.1 of the periodic main paper).  Two continuous positive
thermal densities `ρ, ρ'` satisfy `log ρ - log ρ' = -β g*(ρ - ρ') + const`; integrating against
`ρ - ρ'` and using `∫ (g*z) z = ∑ ĝ(k) |ẑ(k)|² ≥ 0` forces `(log ρ - log ρ')(ρ - ρ') ≡ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFThermal

variable {d : ℕ}

/-- Continuous functions on the torus are `L²`. -/
theorem memLp_two_of_continuous {F : Torus d → ℂ} (hF : Continuous F) : MemLp F 2 volume :=
  hF.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {F : Torus d → E}
    (hF : Continuous F) : Integrable F :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Parseval for the interaction form: `∫ (g*z) z = ∑_k ĝ(k) |ẑ(k)|²`. -/
theorem hasSum_convFun_mul_self (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    {z : Torus d → ℝ} (hz : Continuous z) :
    HasSum (fun k : Lattice d =>
        rieszCoeff d s k * ‖Torus.funFourierCoeff (fun x => (z x : ℂ)) k‖ ^ 2)
      (∫ x, convFun (periodicRiesz d s) z x * z x) := by
  have hg := MFAux.integrable_periodicRiesz hd s hs0 hsd
  have hu : Continuous (convFun (periodicRiesz d s) z) := MFAux.continuous_convFun hg hz
  set u := convFun (periodicRiesz d s) z with hudef
  have hzc : Continuous fun x => (z x : ℂ) := Complex.continuous_ofReal.comp hz
  have huc : Continuous fun x => (u x : ℂ) := Complex.continuous_ofReal.comp hu
  have hP := hasSum_parseval (fun x => (u x : ℂ)) (fun x => (z x : ℂ))
    (memLp_two_of_continuous huc) (memLp_two_of_continuous hzc)
  have hterm : ∀ k : Lattice d,
      conj (Torus.funFourierCoeff (fun x => (u x : ℂ)) k) *
        Torus.funFourierCoeff (fun x => (z x : ℂ)) k =
      ((rieszCoeff d s k * ‖Torus.funFourierCoeff (fun x => (z x : ℂ)) k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [hudef, MFAux.funFourierCoeff_convFun hg hz k, periodicRiesz_fourierCoeff hd hs0 hsd k]
    push_cast
    rw [map_mul, Complex.conj_ofReal]
    rw [mul_assoc, Complex.conj_mul']
  have hval : (∫ t, conj ((u t : ℂ)) * (z t : ℂ)) = ((∫ x, u x * z x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.conj_ofReal]
  simp_rw [hterm, hval] at hP
  exact Complex.hasSum_ofReal.mp hP

/-- The interaction form `∫ (g*z) z` is nonnegative (`ĝ ≥ 0`, `ĝ(0) = 0`). -/
theorem integral_convFun_mul_self_nonneg (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    {z : Torus d → ℝ} (hz : Continuous z) :
    0 ≤ ∫ x, convFun (periodicRiesz d s) z x * z x := by
  refine (hasSum_convFun_mul_self hd s hs0 hsd hz).nonneg fun k => ?_
  by_cases hk : k = 0
  · simp [rieszCoeff, hk]
  · exact mul_nonneg (rieszCoeff_pos hd hs0 hsd k hk).le (sq_nonneg _)

/-- Linearity of the convolution in the second argument (integrable kernel, continuous data). -/
theorem convFun_sub {g a b : Torus d → ℝ} (hg : Integrable g) (ha : Continuous a)
    (hb : Continuous b) (x : Torus d) :
    convFun g (fun y => a y - b y) x = convFun g a x - convFun g b x := by
  have hgx : Integrable (fun y => g (x - y)) := by
    have := (hg.comp_sub_left x)
    exact this
  have hi : ∀ c : Torus d → ℝ, Continuous c → Integrable (fun y => g (x - y) * c y) := by
    intro c hc
    obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hc.continuousOn
    exact hgx.mul_bdd hc.aestronglyMeasurable (c := B)
      (Filter.Eventually.of_forall fun y => hB y (Set.mem_univ _))
  unfold convFun
  rw [← integral_sub (hi a ha) (hi b hb)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mul_sub]

/-- The integrand of the entropy form is nonnegative. -/
theorem log_sub_mul_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (Real.log a - Real.log b) * (a - b) := by
  rcases le_total a b with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [Real.log_le_log ha h])
      (by linarith)
  · exact mul_nonneg (by linarith [Real.log_le_log hb h]) (by linarith)

/-- A thermal density has `log ρ = -β (V + g*ρ) - log Z` with `Z > 0`. -/
theorem log_thermal {g V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}
    (hρ : IsThermalDensity g V β ρ) (hρp : ∀ x, 0 < ρ x) :
    ∃ c : ℝ, ∀ x, Real.log (ρ x) = -β * (V x + convFun g ρ x) + c := by
  set Z := ∫ y, Real.exp (-β * (V y + convFun g ρ y)) with hZ
  have hZpos : 0 < Z := by
    by_contra hneg
    have hle : Z ≤ 0 := not_lt.mp hneg
    have := hρ.2 (Classical.arbitrary _)
    have hp := hρp (Classical.arbitrary _)
    rw [this] at hp
    exact absurd hp (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hle))
  refine ⟨-Real.log Z, fun x => ?_⟩
  have := hρ.2 x
  rw [this, Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  ring

/-- **Uniqueness of the thermal equilibrium**: two continuous positive thermal densities for the
same `V`, `β > 0` and Riesz kernel coincide (no hypothesis on `V`). -/
theorem thermal_unique (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (ρ ρ' : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρc : Continuous ρ) (hρp : ∀ x, 0 < ρ x)
    (hρ' : IsThermalDensity (periodicRiesz d s) V β ρ') (hρc' : Continuous ρ')
    (hρp' : ∀ x, 0 < ρ' x) :
    ρ' = ρ := by
  have hg := MFAux.integrable_periodicRiesz hd s hs0 hsd
  obtain ⟨c₁, h₁⟩ := log_thermal hρ hρp
  obtain ⟨c₂, h₂⟩ := log_thermal hρ' hρp'
  set z : Torus d → ℝ := fun x => ρ x - ρ' x with hzdef
  have hzc : Continuous z := hρc.sub hρc'
  have hlin : ∀ x, convFun (periodicRiesz d s) ρ x - convFun (periodicRiesz d s) ρ' x =
      convFun (periodicRiesz d s) z x := fun x => (convFun_sub hg hρc hρc' x).symm
  have hdiff : ∀ x, Real.log (ρ x) - Real.log (ρ' x) =
      -β * convFun (periodicRiesz d s) z x + (c₁ - c₂) := by
    intro x
    rw [h₁ x, h₂ x, ← hlin x]
    ring
  have hzint : ∫ x, z x = 0 := by
    rw [hzdef, integral_sub (integrable_of_continuous hρc) (integrable_of_continuous hρc'),
      hρ.1.integral_one, hρ'.1.integral_one]
    ring
  have huc : Continuous (convFun (periodicRiesz d s) z) := MFAux.continuous_convFun hg hzc
  have hlogc : Continuous fun x => (Real.log (ρ x) - Real.log (ρ' x)) * z x := by
    refine Continuous.mul (Continuous.sub ?_ ?_) hzc
    · exact hρc.log fun x => (hρp x).ne'
    · exact hρc'.log fun x => (hρp' x).ne'
  have hE : ∫ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x =
      -β * ∫ x, convFun (periodicRiesz d s) z x * z x := by
    have : ∀ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x =
        -β * (convFun (periodicRiesz d s) z x * z x) + (c₁ - c₂) * z x := by
      intro x; rw [hdiff x]; ring
    simp_rw [this]
    have i1 : Integrable (fun x => convFun (periodicRiesz d s) z x * z x) :=
      integrable_of_continuous (huc.mul hzc)
    have i2 : Integrable z := integrable_of_continuous hzc
    rw [integral_add (i1.const_mul (-β)) (i2.const_mul (c₁ - c₂)), integral_const_mul,
      integral_const_mul, hzint]
    ring
  have hnn := integral_convFun_mul_self_nonneg hd s hs0 hsd hzc
  have hle : ∫ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x ≤ 0 := by
    rw [hE]; nlinarith
  have hge : 0 ≤ ∫ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x :=
    integral_nonneg fun x => log_sub_mul_nonneg (hρp x) (hρp' x)
  have h0 : ∫ x, (Real.log (ρ x) - Real.log (ρ' x)) * z x = 0 := le_antisymm hle hge
  have hae : (fun x => (Real.log (ρ x) - Real.log (ρ' x)) * z x) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => log_sub_mul_nonneg (hρp x) (hρp' x))
      (integrable_of_continuous hlogc)).mp h0
  have hall := (Continuous.ae_eq_iff_eq volume hlogc continuous_const).mp hae
  funext x
  have hx : (Real.log (ρ x) - Real.log (ρ' x)) * (ρ x - ρ' x) = 0 := congrFun hall x
  rcases mul_eq_zero.mp hx with hx | hx
  · have := Real.log_injOn_pos (Set.mem_Ioi.mpr (hρp x)) (Set.mem_Ioi.mpr (hρp' x))
      (sub_eq_zero.mp hx)
    exact this.symm
  · exact (sub_eq_zero.mp hx).symm

end HRS.PDE.MFThermal
