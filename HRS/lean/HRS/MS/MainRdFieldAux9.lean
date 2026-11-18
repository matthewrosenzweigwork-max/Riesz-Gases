import HRS.MS.MainRdFieldAux8

/-!
# S.A.6, packet P5c: the covariance cost `E ∫_0^t ‖Σ_r - Σ̄_r‖_{𝔖₁} dr ≤ t K₁ 𝔴_N`

* `sa6_cutoff_expect`: expectation form of the cutoff estimate for a real random variable with a pathwise bound;
* `sa6_inj_swap`: a.e. in time injectivity from a.s. injectivity for a.e. time;
* `sa6_covDiscrepancy_le`: `covDiscrepancy ≤ t · 2q · max(C_p,0) · C_k · 𝔴_N`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem

variable {d : ℕ}

section Expect

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 : ℝ} {r mV : ℕ}
  {C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa6_cutoff_expect (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hΛ : 1 ≤ Λ) {N : ℕ}
    (hN : 2 ≤ N) {σ : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) S.T) {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hm2 : PropagatedSecondMoment S R m₂)
    (hcoll : ∀ᵐ ζ ∂(R N).P, (R N).X (Real.toNNReal σ) ζ ∉ eucCollisionSet d N) {Kc : ℝ}
    (hKc : 0 ≤ Kc) (L : (R N).Ω → ℝ)
    (hL : ∀ᵐ ζ ∂(R N).P, ∀ Rr : ℝ, 1 ≤ Rr → |L ζ| ≤ Kc * (Rr ^ ((d : ℝ) / 2) *
      (smearScale d N Λ + Real.sqrt (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal σ) ζ)
        (HRS.Whole.withDensityReal (S.ρ N σ)) + oNΛ d S.s C₀ Λ N)) +
      (secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal σ) ζ)) +
        secondMomentOf (HRS.Whole.withDensityReal (S.ρ N σ))) / Rr ^ 2)) :
    ∫⁻ ζ, ENNReal.ofReal |L ζ| ∂(R N).P ≤ ENNReal.ofReal (Kc * wN d N (𝔈 N) m₂) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hsol := hS.mean_field.solution N hN1
  have hprob : HRS.Whole.IsProbDensity (S.ρ N σ) := hsol.density σ hσ
  have hmom : Integrable (fun x => ‖x‖ ^ 2 * S.ρ N σ x) := hsol.second_moment σ hσ
  have hρΛ : ∀ x, S.ρ N σ x ≤ Λ := by
    obtain ⟨hmem, -, hle⟩ := (hS.mean_field.regular N hN1).1 σ hσ
    exact Q09A.rho_le_of_cbNorm hmem ENNReal.toReal_nonneg hle
  have hmeasX : Measurable ((R N).X (Real.toNNReal σ)) :=
    Q09A.selectedFlow_measurable (hS.flow N hN1) _
  have hmeas_m : Measurable fun ζ => secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal σ) ζ)) :=
    Q09A.measurable_secondMoment_empirical hN0 hmeasX
  have h𝔈 : 0 < 𝔈 N := hS.energy.pos N hN1
  have hΛ0 : 0 < Λ := by linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN0
  have hbound : ∀ R' : {R : ℝ // 1 ≤ R},
      ∫⁻ ζ, ENNReal.ofReal |L ζ| ∂(R N).P ≤
        ENNReal.ofReal (Kc * (R'.1 ^ ((d : ℝ) / 2) *
          ((N : ℝ) ^ (-(1 : ℝ) / d) + (𝔈 N) ^ ((1 : ℝ) / 2)) + m₂ / R'.1 ^ 2)) := by
    intro R'
    have hR1 : 1 ≤ R'.1 := R'.2
    have hR0 : 0 < R'.1 := by linarith
    refine le_trans (Q09A.lintegral_bound (R N).P L
      (fun ζ => correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal σ) ζ) σ)
      (fun ζ => secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal σ) ζ)) +
        secondMomentOf (HRS.Whole.withDensityReal (S.ρ N σ)))
      (hmeas_m.add_const _) Kc (R'.1 ^ ((d : ℝ) / 2)) (smearScale d N Λ) R'.1 (𝔈 N) m₂
      hKc (Real.rpow_nonneg hR0.le _) ?_ hR0 h𝔈 hm₂ ?_ ?_ ?_ (hm2 N hN1 σ hσ) ?_)
      (ENNReal.ofReal_le_ofReal ?_)
    · unfold smearScale
      exact Real.rpow_nonneg (by positivity) _
    · filter_upwards [hcoll] with ζ hζ
      exact hS.energy.completion.2 Λ hΛ N hN (S.ρ N σ) hprob hρΛ
        (fun _ => Q09A.log_integrable_withDensityReal hprob hmom) _ hζ
    · intro ζ
      exact add_nonneg (Q09A.secondMomentOf_nonneg _) (Q09A.secondMomentOf_nonneg _)
    · exact hS.energy.bound N hN1 σ hσ
    · filter_upwards [hL] with ζ h
      exact h R'.1 hR1
    · have h1 : smearScale d N Λ ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := by
        unfold smearScale
        refine Real.rpow_le_rpow_of_nonpos hNp ?_ ?_
        · nlinarith
        · have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
          rw [neg_div]; linarith
      have h2 : Real.sqrt (𝔈 N) = (𝔈 N) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      rw [h2]
      have h3 : 0 ≤ R'.1 ^ ((d : ℝ) / 2) := Real.rpow_nonneg hR0.le _
      have := mul_le_mul_of_nonneg_left (add_le_add_right h1 ((𝔈 N) ^ ((1 : ℝ) / 2))) h3
      exact mul_le_mul_of_nonneg_left (by linarith) hKc
  unfold wN
  refine Q09A.inf_bound _ ?_ _ _ hKc hbound
  intro R'
  have hR0 : 0 < R'.1 := by have := R'.2; linarith
  have : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have : 0 ≤ (𝔈 N) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg h𝔈.le _
  positivity

/-- A.e. injectivity in time, for a.e. particle path, gives a.s. injectivity for a.e. time. -/
theorem sa6_inj_swap (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ}
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal ρ) ζ)) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)), ∀ᵐ ζ ∂(R N).P,
      (R N).X (Real.toNNReal σ) ζ ∉ eucCollisionSet d N := by
  have hT : 0 ≤ S.T := S.hT.le
  have hm := mrr_prog_meas ℱ (R N).X hF.progressive hT
  set A : Set ((R N).Ω × ℝ) :=
    {p | (R N).X (Real.toNNReal (mrrClamp S.T p.2)) p.1 ∈ eucCollisionSet d N} with hA
  have hAm : MeasurableSet A := (hm.comp measurable_swap) (mrr_measurableSet_coll N)
  have h1 : ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)), ¬ (ζ, ρ) ∈ A := by
    filter_upwards [hinj] with ζ hζ
    filter_upwards [hζ, ae_restrict_mem measurableSet_Icc] with ρ hρ hρm
    intro h
    simp only [hA, Set.mem_setOf_eq, mrrClamp_of_mem hρm] at h
    obtain ⟨i, j, hij, heq⟩ := h
    exact hij (hρ heq)
  have h2 := (Measure.ae_ae_comm (μ := (R N).P) (ν := volume.restrict (Set.Icc (0 : ℝ) S.T))
    (p := fun ζ ρ => ¬ (ζ, ρ) ∈ A) hAm.compl).1 h1
  filter_upwards [h2, ae_restrict_mem measurableSet_Icc] with σ hσ hσm
  filter_upwards [hσ] with ζ hζ
  intro h
  exact hζ (by simp only [hA, Set.mem_setOf_eq, mrrClamp_of_mem hσm]; exact h)

lemma sa6_wN_nonneg {N : ℕ} {E m₂ : ℝ} (hE : 0 ≤ E) (hm : 0 ≤ m₂) : 0 ≤ wN d N E m₂ := by
  unfold wN
  have hne : Nonempty {R : ℝ // 1 ≤ R} := ⟨⟨1, le_refl _⟩⟩
  refine le_ciInf fun R' => ?_
  have hR0 : 0 < R'.1 := by have := R'.2; linarith
  have : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have : 0 ≤ E ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hE _
  positivity

lemma sa6_qN_nonneg (S : WholeMainData d) (N : ℕ) : 0 ≤ S.qN N := by
  unfold WholeMainData.qN qScale
  by_cases h0 : S.invβ N = 0
  · rw [if_pos h0]
  · rw [if_neg h0]
    have := S.hinvβ N
    positivity

section CovDisc

variable {Γ : ℕ}

theorem sa6_covDiscrepancy_le
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈) (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 2 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X) {Kk : ℝ}
    {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)} (hK : Sa6Kern (S.coeff N) S.T Γ Kk Kern)
    (hkb : ∀ σ : ℝ, Sa6KBdd (fun j z => Kern j σ t z) Kk)
    (hprob : ∀ σ : ℝ, HRS.Whole.IsProbDensity (S.ρ N (mrrClamp S.T σ)))
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal ρ) ζ))
    {χ : Euc d → ℝ} {Ck : ℝ} (hCk : 0 ≤ Ck)
    (hcN : ∀ B : HNeg d (Γ : ℝ) →L[ℝ] HNeg d (Γ : ℝ),
      (∀ u v, inner ℝ (B u) v = inner ℝ u (B v)) → ‖B‖ ≤ 1 → ∀ σ ∈ Set.Icc (0 : ℝ) t,
        cNormE χ (fun z => ∑ j, inner ℝ (B (Kern j σ t z)) (Kern j σ t z)) ≤ ENNReal.ofReal Ck)
    {Cp : ℝ}
    (hCp : ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ N' : ℕ, 2 ≤ N' → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ') →
      Integrable (fun x => ‖x‖ ^ 2 * ρ x) → ∀ X : EucConfig d N', Function.Injective X →
      ∀ h : Euc d → ℝ, cNormE χ h < ⊤ → ∀ Rr : ℝ, 1 ≤ Rr →
        |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h| ≤ Cp * (cNormE χ h).toReal *
          (Rr ^ ((d : ℝ) / 2) * (smearScale d N' Λ' + Real.sqrt (rieszModulatedEnergy d S.s X
            (HRS.Whole.withDensityReal ρ) + oNΛ d S.s C₀ Λ' N')) +
            (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / Rr ^ 2))
    {m₂ : ℝ} (hm₂ : 0 ≤ m₂) (hm2 : PropagatedSecondMoment S R m₂)
    (M : ℝ → (R N).Ω → HNeg d (Γ : ℝ))
    (hM : ∀ T', IsHilbertMartingaleWithCovariation (R N).P ℱ T' M
      (fun r ω => hsCovForm (mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X r ω))) :
    covDiscrepancy (R N).P t
        (fun r ω => hsCovForm (mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X r ω))
        (sa6_sb Kern t Kk (S.qN N) hkb (fun σ => S.ρ N (mrrClamp S.T σ)) hprob) ≤
      t * (2 * S.qN N * max Cp 0 * Ck * wN d N (𝔈 N) m₂) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  have hq := sa6_qN_nonneg S N
  have htT : t ≤ S.T := ht.2
  have hρm : Measurable (fun p : ℝ × Euc d => S.ρ N (mrrClamp S.T p.1) p.2) := mrr_rho_meas hS hN1
  have hKm : ∀ j, Measurable (fun p : ℝ × Euc d => Kern j p.1 t p.2) :=
    fun j => sa6_kern_meas_joint hK htT j
  set sb := sa6_sb Kern t Kk (S.qN N) hkb (fun σ => S.ρ N (mrrClamp S.T σ)) hprob with hsbdef
  have hsb : IsDetCovDensity t sb := sa6_sb_det (Kern := Kern) (t := t) (Kk := Kk) (hkb := hkb) (ρ := fun σ => S.ρ N (mrrClamp S.T σ)) (hprob := hprob) hq hρm hKm
  set Zf := mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X with hZf
  set g : ℝ → (R N).Ω → ℝ := fun σ ω => traceNormForm (hsCovForm (Zf σ ω) - sb σ) with hg
  set K₁ : ℝ := 2 * S.qN N * max Cp 0 * Ck with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hwN0 := sa6_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂
  -- the pathwise estimate for σ ∈ [0,t]
  have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) t, ∀ ζ, (R N).X (Real.toNNReal σ) ζ ∉ eucCollisionSet d N →
      ∀ Rr : ℝ, 1 ≤ Rr → g σ ζ ≤ K₁ * (Rr ^ ((d : ℝ) / 2) *
        (smearScale d N Λ + Real.sqrt (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal σ) ζ)
          (HRS.Whole.withDensityReal (S.ρ N σ)) + oNΛ d S.s C₀ Λ N)) +
        (secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal σ) ζ)) +
          secondMomentOf (HRS.Whole.withDensityReal (S.ρ N σ))) / Rr ^ 2) := by
    intro σ hσ ζ hζ Rr hRr
    have hσS : σ ∈ Set.Icc (0 : ℝ) S.T := ⟨hσ.1, hσ.2.trans htT⟩
    have hcl : mrrClamp S.T σ = σ := mrrClamp_of_mem hσS
    have hclm := mrrClamp_mem hT σ
    set X := (R N).X (Real.toNNReal σ) ζ with hXdef
    set ρ' := S.ρ N (mrrClamp S.T σ) with hρ'def
    have hXinj : Function.Injective X := fun i j hij => by
      by_contra hne; exact hζ ⟨i, j, hne, hij⟩
    haveI : IsProbabilityMeasure (HRS.Whole.empirical X) := HRS.Whole.empirical_isProbabilityMeasure hN0 X
    haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ') := Q09A.measure_isProb (hprob σ)
    have hZ : Zf σ ζ = fun ia : Fin N × Fin d =>
        sa6_cN S N • (fun j z => Kern j σ t z) ia.2 (X ia.1) := by
      funext ia
      simp only [hZf, mrmZ]
      rw [if_pos ⟨hσ, hσ.2.trans htT⟩]
    have hcov : hsCovForm (Zf σ ζ) =
        (2 * S.qN N) • sa6Form (fun j z => Kern j σ t z) (hkb σ) (HRS.Whole.empirical X) := by
      rw [hZ]
      exact sa6_cov_eq hN0 (hkb σ) X _ _ (sa6_cN_sq S hN0)
    have hsbσ : sb σ = (2 * S.qN N) • sa6Form (fun j z => Kern j σ t z) (hkb σ)
        (HRS.Whole.withDensityReal ρ') := rfl
    have hdisc : hsCovForm (Zf σ ζ) - sb σ = (2 * S.qN N) •
        (sa6Form (fun j z => Kern j σ t z) (hkb σ) (HRS.Whole.empirical X) -
          sa6Form (fun j z => Kern j σ t z) (hkb σ) (HRS.Whole.withDensityReal ρ')) := by
      rw [hcov, hsbσ]
      ext x y
      simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, mul_sub]
    have hρ'le : ∀ x, ρ' x ≤ Λ := by
      obtain ⟨hmem, -, hle⟩ := (hS.mean_field.regular N hN1).1 _ hclm
      exact Q09A.rho_le_of_cbNorm hmem ENNReal.toReal_nonneg hle
    have hρ'mom : Integrable (fun x => ‖x‖ ^ 2 * ρ' x) :=
      (hS.mean_field.solution N hN1).second_moment _ hclm
    set Rhs : ℝ := Rr ^ ((d : ℝ) / 2) * (smearScale d N Λ + Real.sqrt (rieszModulatedEnergy d S.s X
      (HRS.Whole.withDensityReal ρ') + oNΛ d S.s C₀ Λ N)) +
      (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ')) / Rr ^ 2 with hRhs
    have hRhs0 : 0 ≤ Rhs := by
      have h1 : 0 ≤ smearScale d N Λ := by
        unfold smearScale; exact Real.rpow_nonneg (by positivity) _
      have h2 := Q09A.secondMomentOf_nonneg (HRS.Whole.empirical X)
      have h3 := Q09A.secondMomentOf_nonneg (HRS.Whole.withDensityReal ρ')
      have hR0 : 0 < Rr := by linarith
      rw [hRhs]; positivity
    have h1 : g σ ζ ≤ |2 * S.qN N| * (max Cp 0 * Rhs) * Ck := by
      show traceNormForm (hsCovForm (Zf σ ζ) - sb σ) ≤ _
      rw [hdisc]
      refine sa6_traceNorm_le (hkb σ) (HRS.Whole.empirical X) (HRS.Whole.withDensityReal ρ') (2 * S.qN N) χ
        (mul_nonneg (le_max_right _ _) hRhs0) hCk (fun B hB hn => hcN B hB hn σ hσ) ?_
      intro h hh
      have := hCp Λ hΛ N hN ρ' (hprob σ) hρ'le hρ'mom X hXinj h hh Rr hRr
      have hn : 0 ≤ (cNormE χ h).toReal := ENNReal.toReal_nonneg
      calc _ ≤ Cp * (cNormE χ h).toReal * Rhs := this
        _ ≤ (max Cp 0 * Rhs) * (cNormE χ h).toReal := by
          nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left Cp 0)) (mul_nonneg hn hRhs0)]
    have habs : |2 * S.qN N| = 2 * S.qN N := abs_of_nonneg (by positivity)
    calc g σ ζ ≤ |2 * S.qN N| * (max Cp 0 * Rhs) * Ck := h1
      _ = K₁ * Rhs := by rw [habs, hK₁]; ring
      _ = _ := by rw [hRhs, hρ'def, hcl]
  have hperσ : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      ∫⁻ ζ, ENNReal.ofReal (g σ ζ) ∂(R N).P ≤ ENNReal.ofReal (K₁ * wN d N (𝔈 N) m₂) := by
    have hsw := sa6_inj_swap hS hF hinj
    have hsw' : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) t)), ∀ᵐ ζ ∂(R N).P,
        (R N).X (Real.toNNReal σ) ζ ∉ eucCollisionSet d N :=
      ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc_right htT) hsw
    filter_upwards [hsw', ae_restrict_mem measurableSet_Icc] with σ hσc hσm
    have hmain := sa6_cutoff_expect hS hΛ hN ⟨hσm.1, hσm.2.trans htT⟩ hm₂ hm2 hσc hK₁0 (g σ) (by
      filter_upwards [hσc] with ζ hζ
      intro Rr hRr
      rw [abs_of_nonneg (traceNormForm_nonneg _)]
      exact hpt σ hσm ζ hζ Rr hRr)
    refine le_trans (le_of_eq ?_) hmain
    refine lintegral_congr fun ζ => ?_
    rw [abs_of_nonneg (traceNormForm_nonneg _)]
  -- integrate
  have hint := discrepancy_integrable (R N).P (hM t) hsb
  have hmeasg := measurable_discrepancy_density (R N).P (hM t) hsb
  have hpath := discrepancy_pathint (R N).P (hM t) hsb
  have hF0 : ∀ ω, 0 ≤ ∫ σ in Set.Icc (0 : ℝ) t, g σ ω :=
    fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _
  have e1 : ENNReal.ofReal (∫ ω, (∫ σ in Set.Icc (0 : ℝ) t, g σ ω) ∂(R N).P) =
      ∫⁻ ω, ENNReal.ofReal (∫ σ in Set.Icc (0 : ℝ) t, g σ ω) ∂(R N).P :=
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hF0)
  have e2 : ∀ᵐ ω ∂(R N).P, ENNReal.ofReal (∫ σ in Set.Icc (0 : ℝ) t, g σ ω) =
      ∫⁻ σ in Set.Icc (0 : ℝ) t, ENNReal.ofReal (g σ ω) := by
    filter_upwards [hpath] with ω hω
    exact ofReal_integral_eq_lintegral_ofReal hω.1 (ae_of_all _ fun σ => traceNormForm_nonneg _)
  have e3 : ∫⁻ ω, (∫⁻ σ in Set.Icc (0 : ℝ) t, ENNReal.ofReal (g σ ω)) ∂(R N).P =
      ∫⁻ σ in Set.Icc (0 : ℝ) t, ∫⁻ ω, ENNReal.ofReal (g σ ω) ∂(R N).P :=
    lintegral_lintegral_swap
      ((ENNReal.measurable_ofReal.comp (hmeasg.comp measurable_swap)).aemeasurable)
  have key : ENNReal.ofReal (∫ ω, (∫ σ in Set.Icc (0 : ℝ) t, g σ ω) ∂(R N).P) ≤
      ENNReal.ofReal (t * (K₁ * wN d N (𝔈 N) m₂)) := by
    rw [e1, lintegral_congr_ae e2, e3]
    calc ∫⁻ σ in Set.Icc (0 : ℝ) t, ∫⁻ ω, ENNReal.ofReal (g σ ω) ∂(R N).P
        ≤ ∫⁻ σ in Set.Icc (0 : ℝ) t, ENNReal.ofReal (K₁ * wN d N (𝔈 N) m₂) :=
          lintegral_mono_ae hperσ
      _ = ENNReal.ofReal t * ENNReal.ofReal (K₁ * wN d N (𝔈 N) m₂) := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
      _ = _ := (ENNReal.ofReal_mul ht.1).symm
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ht.1 (mul_nonneg hK₁0 hwN0))).1 key

end CovDisc

end Expect

end HRS.MS.MainRdField
