import HRS.MS.WsStatAux12
import HRS.MS.FldRemCenTie

/-!
# S21 packet F1/F2: the centred remainder estimate for the stationary quadratic model

* `s21_evariance_map`: `evariance (g . Y) P = evariance g (P.map Y)` for measurable `Y`, `g`.
* `s21_var_hyp`: the variance hypothesis of `field_remainder_centered` (`W:r2:centered-input`):
  `N Var[D_mu(h_f)] <= C_A deltaN ||D^2 f||_infty^2` for every `f in C_b^2`, when the configuration has the law
  `P_{N,beta} = HRS.Whole.canonicalGibbs`, from `S45Static.comm` (S3.3 `euc_static_commutator` / S3.5 `r2_log_static_commutator`),
  the Lipschitz constant `sup ||D^2 f||` of `nabla f` (`s53_grad_lip`) and measurability of `D_mu(h_f)` (`s53_Dk_measurable`).
* `s21_centered_remainder`: with `k = d + 9`, `m = 24 d + 240`, `Q = a . 1`, `nu = beta^{-1}` the conclusion of
  `field_remainder_centered_proof` holds for every stationary realization (`GibbsInvariant`-type input
  `law P (X t) = P_{N,beta}`, `t <= T`) with the constant `C_T` independent of `N`:
  `(E sup_{t<=T} ||(-(sqrt N/2) int_0^t (D_mu(h_{U phi_alpha}) - E D_mu(h_{U phi_alpha})) dr)_alpha||_{l^2}^2)^{1/2} <= C_T sqrt(deltaN)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s21_evariance_map {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (P : Measure Ω)
    (Y : Ω → α) (hY : Measurable Y) (g : α → ℝ) (hg : Measurable g) :
    evariance (fun ζ => g (Y ζ)) P = evariance g (P.map Y) := by
  unfold evariance
  have h1 : ∫ ζ, g (Y ζ) ∂P = ∫ x, g x ∂(P.map Y) := (integral_map hY.aemeasurable hg.aestronglyMeasurable).symm
  simp only [h1]
  have hm : Measurable fun x => ‖g x - ∫ y, g y ∂(P.map Y)‖ₑ ^ 2 :=
    ((hg.sub measurable_const).enorm).pow_const 2
  exact (lintegral_map hm hY).symm

theorem s21_var_hyp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ CA : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y : Ω → EucConfig d N), Measurable Y →
      law P Y = HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β →
      ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ∀ f : Euc d → ℝ, MemCb 2 f →
        (N : ℝ≥0∞) * evariance (fun ζ => centeredPairFunctional
            (commutatorKernel d s (fun x => gradient f x)) (Y ζ) (HRS.Whole.withDensityReal ρ)) P ≤
          ENNReal.ofReal (CA * deltaN d s N * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2) := by
  obtain ⟨C, hC0, hCs⟩ := S45.s45_static_all hd hs0 hsd ha hβ
  refine ⟨C, fun N hN Ω _ P _ Y hY hlaw ρ hρ f hf => ?_⟩
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hρp : HRS.Whole.IsProbDensity ρ := hρ.1.1
  have hLip := HRS.MS.S53.s53_grad_lip hf
  set Λ : ℝ≥0 := Real.toNNReal (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) with hΛ
  have hsup0 : 0 ≤ ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖ := HRS.MS.S53.s53_cbSup_nonneg f
  have hΛc : (Λ : ℝ) = ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖ := Real.coe_toNNReal _ hsup0
  obtain ⟨-, -, hev⟩ := ((hCs N hN).comm Λ (fun x => gradient f x) hLip).1
  have hDk : Measurable fun X : EucConfig d N => HRS.MS.S53.s53_Dk s ρ f X := by
    have hG0 : Measurable (gradient f) := (S45.s45_contDiff_gradient hf.1).continuous.measurable
    have h : Measurable (fun p : ℝ × EucConfig d N => HRS.MS.S53.s53_Dk s ρ ((fun _ : ℝ => f) p.1) p.2) :=
      HRS.MS.S53.s53_Dk_measurable hρp (F := fun _ => f) (hG0.comp measurable_snd)
    exact Measurable.of_uncurry_left (f := fun (_ : ℝ) (X : EucConfig d N) => HRS.MS.S53.s53_Dk s ρ f X)
      (x := 0) h
  have hmeas : Measurable fun X : EucConfig d N => centeredPairFunctional
      (commutatorKernel d s (fun x => gradient f x)) X (HRS.Whole.withDensityReal ρ) := hDk
  have hmap : (HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β) = P.map Y := hlaw.symm
  have hth : HRS.Whole.withDensityReal ρ = thermalMeasure d s a β := by rw [hρeq]; rfl
  rw [s21_evariance_map P Y hY _ hmeas]
  have hev' := hev
  rw [hmap] at hev'
  rw [hth]
  refine (mul_le_mul' le_rfl hev').trans ?_
  have hδ : 0 ≤ deltaN d s N := (s21_deltaN_pos hs0 hsd N (by omega)).le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h1 : (N : ℝ≥0∞) = ENNReal.ofReal N := (ENNReal.ofReal_natCast N).symm
  rw [h1, ← ENNReal.ofReal_mul hN0.le, hΛc]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp

theorem s21_centered_remainder (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T) :
    ∃ CT : ℝ, ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsVectorBrownian P W →
        IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X →
        (∀ t : ℝ≥0, (t : ℝ) ≤ T → law P (X t) = HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β) →
        (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
          IntegrableOn (fun r => commForcing
            ((⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff (fun _ => ρ))
            s ((wholeSpaceIndex d : ℕ) : ℝ) (HRS.Whole.withDensityReal ρ) X α t r ζ) (Set.Icc 0 t)) ∧
        (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
            -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
              (commForcing ((⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff
                  (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (HRS.Whole.withDensityReal ρ) X α t r ζ -
                ∫ ζ', commForcing ((⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff
                  (fun _ => ρ)) s ((wholeSpaceIndex d : ℕ) : ℝ) (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P))) ^ 2 ∂P) ^
          (1 / 2 : ℝ) ≤ ENNReal.ofReal (CT * Real.sqrt (deltaN d s N)) := by
  obtain ⟨CA, hCA⟩ := s21_var_hyp hd hs0 hsd ha hβ
  have hk : (d : ℝ) / 2 + 6 < ((d + 9 : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hm : ((2 * (d + 9) + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hρS : ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → IsSchwartzDensity ρ := fun ρ hρ => by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]; exact s21_schwartz_thermal hd hs0 hsd ha hβ
  -- the constant `C_T` of `field_remainder_centered` for the (unique) thermal density
  by_cases hex : ∃ ρ₁ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ₁
  · obtain ⟨ρ₁, h₁⟩ := hex
    obtain ⟨CT, hCT⟩ := HRS.MS.S53.field_remainder_centered_proof hd s hs0 hsd (d + 9) hk
      ((wholeSpaceIndex d : ℕ) : ℝ) hm T β⁻¹ hT hν (a • (1 : Matrix (Fin d) (Fin d) ℝ)) ρ₁ (hρS ρ₁ h₁) CA
    refine ⟨CT, fun ρ hρ N hN Ω _ P _ X₀ W X hW hX hlaw => ?_⟩
    have hρeq : ρ = ρ₁ := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ).trans
      (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ h₁).symm
    subst hρeq
    have hX' : IsWholeStrongSolution P
        (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d) T X₀ W X := by
      rw [← s21_dyn_eq]; exact hX
    refine hCT N hN P X₀ W X hW hX' (fun t ht => ?_) ?_
    · have h1 := hlaw (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
      have h0 := hlaw 0 (by simpa using hT)
      exact h1.trans h0.symm
    · intro f hf
      exact hCA N hN P (X 0) ((hX.adapted 0)) (hlaw 0 (by simpa using hT)) ρ hρ f hf
  · refine ⟨0, fun ρ hρ => absurd ⟨ρ, hρ⟩ hex⟩

end HRS.MS.S21
