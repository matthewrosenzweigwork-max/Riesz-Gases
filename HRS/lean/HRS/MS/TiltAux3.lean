import HRS.MS.TiltAux2

/-!
# S4.7 packet P3: the canonical form of the tilted preparation and the static bundle

`s47_V0 = -γ⁻¹ log ρ - g * μ` makes `ρ` a solution of the thermal equation for `(g, V₀, γ)` with normaliser `1`
(`s47_isThermalDensity_V0`), hence `Q = modulatedGibbs g N γ μ = canonicalGibbs g V₀ N γ` (`s47_P_eq`).
`S47Static` / `s47_static_all`: the calibrated static estimates of S3.3/S3.5 for `Q`, with one constant for all reference
densities with a Gaussian bound `(C, c)` and `γ ∈ [γm, γp]`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open HRS.Whole HRS.MS.Thm HRS.MS.Can2
open HRS (Euc)

variable {d : ℕ}

/-- `V₀ = -γ⁻¹ log ρ - g * μ`. -/
def s47_V0 (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (γ : ℝ) : Euc d → ℝ := fun x =>
  -γ⁻¹ * Real.log (ρ x) - convMeasure (rieszKernel d s) (withDensityReal ρ) x

/-- The preparation law, in canonical form. -/
abbrev s47_P (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (γ : ℝ) (N : ℕ) : Measure (EucConfig d N) :=
  canonicalGibbs (rieszKernel d s) (s47_V0 d s ρ γ) N γ

/-- Its one-particle marginal. -/
abbrev s47_nu (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (γ : ℝ) (N : ℕ) : Measure (Euc d) :=
  firstMarginal (s47_P d s ρ γ N)

theorem s47_isThermalDensity_V0 {s : ℝ} {ρ : Euc d → ℝ} {γ : ℝ} (hγ : 0 < γ) (hprob : IsProbDensity ρ)
    (hpos : ∀ x, 0 < ρ x) : IsThermalDensity (rieszKernel d s) (s47_V0 d s ρ γ) γ ρ := by
  have key : ∀ y : Euc d, -γ * (s47_V0 d s ρ γ y +
      convMeasure (rieszKernel d s) (withDensityReal ρ) y) = Real.log (ρ y) := by
    intro y
    unfold s47_V0
    field_simp
    ring
  refine ⟨hprob, fun x => ?_⟩
  simp_rw [key]
  have e : ∀ y, Real.exp (Real.log (ρ y)) = ρ y := fun y => Real.exp_log (hpos y)
  simp_rw [e]
  rw [hprob.integral_one, div_one]

theorem s47_P_eq {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {C c : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) (hprob : IsProbDensity ρ) (hρc : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) {γ : ℝ} (hγ : 0 < γ) (N : ℕ) :
    s47_P d s ρ γ N = modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ) :=
  HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof (rieszKernel d s) (s47_V0 d s ρ γ) γ ρ
    (s47_isThermalDensity_V0 hγ hprob hpos) (fun x => can2_rieszKernel_neg s x)
    (s47_hint hd hs0 hsd hprob hρc hc hC h0)

/-- The static facts at particle number `N` for `Q_{N,γ}`. -/
structure S47Static (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (γ C : ℝ) (N : ℕ) : Prop where
  prob : IsProbabilityMeasure (s47_P d s ρ γ N)
  exch : IsExchangeable (s47_P d s ρ γ N)
  linear : ∀ f : Euc d → ℝ, MemLp f 2 (withDensityReal ρ) →
    evariance (linStat f) (s47_P d s ρ γ N) ≤
      ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂(withDensityReal ρ))
  marg : ∃ φ : Euc d → ℝ, Measurable φ ∧
    s47_nu d s ρ γ N = (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (φ x)) ∧
    (∀ x, 0 ≤ φ x ∧ φ x ≤ C) ∧ MemLp (fun x => φ x - 1) 2 (withDensityReal ρ) ∧
    l2Norm (withDensityReal ρ) (fun x => φ x - 1) ≤ C * HRS.deltaN d s N
  comm : ∀ (Λ : ℝ≥0) (v : Euc d → Euc d), LipschitzWith Λ v →
    QuadraticVarianceBound (commutatorKernel d s v) (s47_P d s ρ γ N) (withDensityReal ρ)
      (C * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N) ∧
    QuadraticVarianceBound (commutatorKernel d s v) (s47_P d s ρ γ N) (s47_nu d s ρ γ N)
      (C * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N)


theorem s47_static_all (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {γm γp : ℝ} (hγm : 0 < γm)
    (hγp : γm ≤ γp) {C0 c0 : ℝ} (hC0 : 0 ≤ C0) (hc0 : 0 < c0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ρ : Euc d → ℝ} {q BU BB : ℝ} {Bd : Euc d → Euc d},
      TRef d s ρ q C0 c0 BU BB Bd → ∀ γ ∈ Set.Icc γm γp, ∀ N : ℕ, 2 ≤ N → S47Static d s ρ γ C N := by
  have hd1 : 1 ≤ d := by omega
  have hsd2 : (0 : ℝ) < d / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rcases hs0.eq_or_lt with h0 | h0
  · -- s = 0
    subst h0
    obtain ⟨A, hA⟩ := S46.s46_spherical hd1 hc0 hC0
    obtain ⟨C, hC⟩ := HRS.MS.Wl.r2_log_static_proof hd γm γp A hγm hγp
    obtain ⟨C', hC'⟩ := HRS.MS.Wl.r2_log_static_commutator_proof hd γm γp A hγm hγp
    refine ⟨max (max C C') 0, le_max_right _ _, fun {ρ q BU BB Bd} hT γ hγ N hN => ?_⟩
    have hγ0 : 0 < γ := hγm.trans_le hγ.1
    have hCle : C ≤ max (max C C') 0 := (le_max_left _ _).trans (le_max_left _ _)
    have hC'le : C' ≤ max (max C C') 0 := (le_max_right _ _).trans (le_max_left _ _)
    have hC0 : 0 ≤ max (max C C') 0 := le_max_right _ _
    have hρ := hT.prob
    have hρg : ∀ x, ρ x ≤ C0 * Real.exp (-c0 * ‖x‖ ^ 2) := fun x => (le_abs_self _).trans (hT.h0 x)
    haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    obtain ⟨hGW, hlin, hmarg, -⟩ := hC ρ hρ (hA ρ hρg) γ hγ N hN
    have hcan := s47_P_eq hd1 hs0 hsd hT.hc hT.C0 hT.prob hT.smooth.continuous hT.pos hT.h0 hγ0 N
    have hδ : HRS.deltaN d 0 N = (N : ℝ)⁻¹ := by
      unfold HRS.deltaN; rw [if_pos hsd2]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hprob : IsProbabilityMeasure (modulatedGibbs (rieszKernel d 0) N γ (withDensityReal ρ)) :=
      S45.s45_modGibbs_prob hGW
    have hexch : IsExchangeable (modulatedGibbs (rieszKernel d 0) N γ (withDensityReal ρ)) :=
      modulatedGibbs_isExchangeable _ _ _ (S45.s45_rieszKernel_even 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hcan]; exact hprob
    · rw [hcan]; exact hexch
    · intro f hf
      rw [hcan]
      refine (hlin f hf).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI : 0 ≤ ∫ x, f x ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun x => sq_nonneg _
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCle hN0.le) hI
    · unfold s47_nu
      rw [hcan]
      obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
      refine ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, ?_⟩, hφ2, ?_⟩
      · refine (hφb x).2.trans ?_
        have hp : (1 + ‖x‖ ^ 2) ^ (-(γ / (2 * N))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
            (by have : 0 < γ / (2 * N) := by positivity
                linarith)
        have h1 : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(γ / (2 * N))) := Real.rpow_nonneg (by positivity) _
        calc C * (1 + ‖x‖ ^ 2) ^ (-(γ / (2 * N)))
            ≤ max (max C C') 0 * (1 + ‖x‖ ^ 2) ^ (-(γ / (2 * N))) :=
              mul_le_mul_of_nonneg_right hCle h1
          _ ≤ max (max C C') 0 * 1 := mul_le_mul_of_nonneg_left hp hC0
          _ = _ := mul_one _
      · rw [hδ]
        refine hφn.trans ?_
        have : C / N = C * (N : ℝ)⁻¹ := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hCle (by positivity)
    · intro Λ v hv
      unfold s47_nu
      rw [hcan]
      obtain ⟨h1, h2⟩ := hC' ρ hρ (hA ρ hρg) γ hγ N hN Λ v hv
      have hb : C' * (Λ : ℝ) ^ 2 / N / N ≤ max (max C C') 0 * (Λ : ℝ) ^ 2 * HRS.deltaN d 0 N / N := by
        rw [hδ]
        have : C' * (Λ : ℝ) ^ 2 / N / N = C' * (Λ : ℝ) ^ 2 * (N : ℝ)⁻¹ / N := by
          field_simp
        rw [this]
        gcongr
      exact ⟨HRS.MS.Wr.wr14a_qvb_mono hb h1, HRS.MS.Wr.wr14a_qvb_mono hb h2⟩
  · -- 0 < s < d
    obtain ⟨C, hC⟩ := HRS.MS.Wr.euc_static_proof hd h0 hsd γm γp C0 hγm hγp
    obtain ⟨C', hC'⟩ := HRS.MS.Wr.euc_static_commutator_proof hd h0 hsd γm γp C0 hγm hγp
    refine ⟨max (max C (C' * s ^ 2)) 0, le_max_right _ _, fun {ρ q BU BB Bd} hT γ hγ N hN => ?_⟩
    have hγ0 : 0 < γ := hγm.trans_le hγ.1
    have hCle : C ≤ max (max C (C' * s ^ 2)) 0 := (le_max_left _ _).trans (le_max_left _ _)
    have hC'le : C' * s ^ 2 ≤ max (max C (C' * s ^ 2)) 0 := (le_max_right _ _).trans (le_max_left _ _)
    have hC0 : 0 ≤ max (max C (C' * s ^ 2)) 0 := le_max_right _ _
    have hρ := hT.prob
    have hρg : ∀ x, ρ x ≤ C0 * Real.exp (-c0 * ‖x‖ ^ 2) := fun x => (le_abs_self _).trans (hT.h0 x)
    have hM : ∀ x, ρ x ≤ C0 := fun x => HRS.MS.TcR.tc2_le_M0 hT.prob hT.hc hρg x
    haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    obtain ⟨hGW, hlin, hmarg, -⟩ := hC ρ hρ hM γ hγ N hN
    have hcan := s47_P_eq hd1 hs0 hsd hT.hc hT.C0 hT.prob hT.smooth.continuous hT.pos hT.h0 hγ0 N
    have hδ0 : 0 ≤ HRS.deltaN d s N := HRS.deltaN_nonneg s (by omega)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hprob : IsProbabilityMeasure (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) :=
      S45.s45_modGibbs_prob hGW
    have hexch : IsExchangeable (modulatedGibbs (rieszKernel d s) N γ (withDensityReal ρ)) :=
      modulatedGibbs_isExchangeable _ _ _ (S45.s45_rieszKernel_even s)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hcan]; exact hprob
    · rw [hcan]; exact hexch
    · intro f hf
      rw [hcan]
      refine (hlin f hf).trans (ENNReal.ofReal_le_ofReal ?_)
      have hI : 0 ≤ ∫ x, f x ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun x => sq_nonneg _
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCle hN0.le) hI
    · unfold s47_nu
      rw [hcan]
      obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
      exact ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, (hφb x).2.trans hCle⟩, hφ2,
        hφn.trans (mul_le_mul_of_nonneg_right hCle hδ0)⟩
    · intro Λ v hv
      unfold s47_nu
      rw [hcan]
      obtain ⟨h1, h2⟩ := hC' ρ hρ hM γ hγ N hN Λ v hv
      have hb : C' * (s * (Λ : ℝ)) ^ 2 * HRS.deltaN d s N / N ≤
          max (max C (C' * s ^ 2)) 0 * (Λ : ℝ) ^ 2 * HRS.deltaN d s N / N := by
        have e : C' * (s * (Λ : ℝ)) ^ 2 = (C' * s ^ 2) * (Λ : ℝ) ^ 2 := by ring
        rw [e]
        gcongr
      exact ⟨HRS.MS.Wr.wr14a_qvb_mono hb h1, HRS.MS.Wr.wr14a_qvb_mono hb h2⟩

end S47

end
