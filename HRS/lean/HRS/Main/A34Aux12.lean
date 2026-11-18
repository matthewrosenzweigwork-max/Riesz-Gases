import HRS.Main.A34Aux11

/-!
# Packet A34, helper 12: perturbation of the test function (single system)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_perturb (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (ν₀ MB Λ VB T Cin : ℝ) (m m₀ : ℕ) (hm₀ : m₀ ≤ m) (hmS : mStar d ≤ m) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ) (A q : ℝ),
      AdjointData s m Rg MB Λ VB D ν₀ T ρ → |A| ≤ 2 → 0 ≤ q → q ≤ 2 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Ω → (Torus d → ℝ) → ℝ), XHyp P η m₀ Cin →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ φ' : Torus d → ℝ, Continuous φ → MemSobolev (m : ℝ) φ →
        Continuous φ' → MemSobolev (m : ℝ) φ' →
        ∫ ω, |A * η ω (propagator D ρ 0 t φ) - A * η ω (propagator D ρ 0 t φ')| ∂P +
          |Real.sqrt (a34_cov D ρ q t φ) - Real.sqrt (a34_cov D ρ q t φ')| ≤
        c * sobolevNorm (m : ℝ) (fun x => φ x - φ' x) := by
  have hm1 : 1 ≤ m := by have := ClassicalPart.three_le_mStar d; omega
  obtain ⟨K, K₂, hK0, hK₂0, hu⟩ := a34_unif hd s hs0 hsd m hmS Rg MB Λ VB ν₀ T
  set m₁ : ℕ := max m₀ 1 with hm₁
  have hm₁1 : 1 ≤ m₁ := le_max_right _ _
  have hm₁m : m₁ ≤ m := max_le hm₀ hm1
  refine ⟨2 * |Cin| * (K m₁ + 1) + Real.sqrt (8 * |Λ| * |T|) * K 1,
    add_nonneg (mul_nonneg (by positivity) (add_nonneg (hK0 _) zero_le_one))
      (mul_nonneg (Real.sqrt_nonneg _) (hK0 _)), ?_⟩
  intro D ρ A q hA hA2 hq0 hq2 Ω _ P _ η hη t ht φ φ' hφc hφ hφ'c hφ'
  set Dn := sobolevNorm (m : ℝ) (fun x => φ x - φ' x) with hDn
  have hDn0 : 0 ≤ Dn := Real.sqrt_nonneg _
  have hΛ0 : 0 ≤ Λ := by
    have := (hA.hμ.bound 0 ⟨le_rfl, hA.hT.le⟩)
    exact (Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _).trans this
  have hdφ : MemSobolev (m : ℝ) (fun x => φ x - φ' x) := a34_memSobolev_sub hφ hφ' hφc hφ'c
  have hdc : Continuous (fun x => φ x - φ' x) := hφc.sub hφ'c
  have hm₀m : (m₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm₀
  have hmem₀φ : MemSobolev (m₀ : ℝ) φ := MFAdjoint.memSobolev_mono_idx hφ hm₀m
  have hmem₀φ' : MemSobolev (m₀ : ℝ) φ' := MFAdjoint.memSobolev_mono_idx hφ' hm₀m
  have hm₀m₁ : (m₀ : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast (le_max_left m₀ 1)
  have hm₁le : (m₁ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm₁m
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have hψ := a34_prop_zero hd m hmS Rg s MB Λ VB ν₀ T D ρ hA hφc hφ
    have hψ' := a34_prop_zero hd m hmS Rg s MB Λ VB ν₀ T D ρ hA hφ'c hφ'
    have hv : ∀ (φ : Torus d → ℝ), a34_cov D ρ q 0 φ = 0 := by
      intro φ
      unfold a34_cov
      rw [min_self, Set.Icc_self, setIntegral_measure_zero _ (by simp), mul_zero]
    rw [hψ, hψ', hv, hv]
    simp only [Real.sqrt_zero, sub_self, abs_zero, add_zero]
    have h1 := a34_X_diff hη hmem₀φ hmem₀φ' hφc hφ'c A A
    rw [sub_self, abs_zero, zero_mul, zero_add] at h1
    refine h1.trans ?_
    have h2 : sobolevNorm (m₀ : ℝ) (fun x => φ x - φ' x) ≤ Dn :=
      a34_sobolevNorm_mono hm₀m hdφ
    have h3 : |A| * (|Cin| * sobolevNorm (m₀ : ℝ) (fun x => φ x - φ' x)) ≤ 2 * (|Cin| * Dn) :=
      mul_le_mul hA2 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by norm_num)
    refine h3.trans ?_
    have hK1 := hK0 m₁
    have hs1 : 0 ≤ Real.sqrt (8 * |Λ| * |T|) * K 1 := mul_nonneg (Real.sqrt_nonneg _) (hK0 1)
    have hp : 0 ≤ |Cin| * Dn := mul_nonneg (abs_nonneg _) hDn0
    nlinarith [mul_nonneg hp hK1, mul_nonneg hDn0 hs1, hp]
  · have htI : t ∈ Set.Ioc 0 T := ⟨hpos, ht.2⟩
    have h0t : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, hpos.le⟩
    obtain ⟨⟨f, hcl, hpe⟩, hrφ⟩ := hu D ρ hA htI hφc hφ
    obtain ⟨⟨f', hcl', hpe'⟩, hrφ'⟩ := hu D ρ hA htI hφ'c hφ'
    obtain ⟨⟨f'', hcl'', hpe''⟩, hrw⟩ := hu D ρ hA htI hdc hdφ
    have hcont : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → Continuous ψ := fun ψ h =>
      ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by norm_num) h)
    have hlin := fun r (hr : r ∈ Set.Icc (0 : ℝ) t) =>
      a34_prop_sub hd s hs0 hsd m hmS Rg MB Λ VB D ν₀ T ρ hA htI hφc hφ hφ'c hφ' hr
    -- the random part
    obtain ⟨hm1ψ, hC2ψ, -⟩ := hrφ 0 h0t
    obtain ⟨hm1ψ', hC2ψ', -⟩ := hrφ' 0 h0t
    obtain ⟨hm1w, hC2w, -⟩ := hrw 0 h0t
    have hψc : Continuous (propagator D ρ 0 t φ) := hcont _ hC2ψ
    have hψ'c : Continuous (propagator D ρ 0 t φ') := hcont _ hC2ψ'
    obtain ⟨hs₁, -⟩ := hm1ψ m₁ hm₁1 hm₁m
    obtain ⟨hs₁', -⟩ := hm1ψ' m₁ hm₁1 hm₁m
    obtain ⟨hsw, hnw⟩ := hm1w m₁ hm₁1 hm₁m
    have hmψ : MemSobolev (m₀ : ℝ) (propagator D ρ 0 t φ) :=
      MFAdjoint.memSobolev_mono_idx hs₁ hm₀m₁
    have hmψ' : MemSobolev (m₀ : ℝ) (propagator D ρ 0 t φ') :=
      MFAdjoint.memSobolev_mono_idx hs₁' hm₀m₁
    have hX := a34_X_diff hη hmψ hmψ' hψc hψ'c A A
    rw [sub_self, abs_zero, zero_mul, zero_add] at hX
    have hw0 : (fun x => propagator D ρ 0 t φ x - propagator D ρ 0 t φ' x) =
        propagator D ρ 0 t (fun x => φ x - φ' x) := (hlin 0 h0t).symm
    have hwn : sobolevNorm (m₀ : ℝ) (fun x => propagator D ρ 0 t φ x - propagator D ρ 0 t φ' x) ≤
        K m₁ * Dn := by
      rw [hw0]
      refine (a34_sobolevNorm_mono hm₀m₁ hsw).trans (hnw.trans ?_)
      exact mul_le_mul_of_nonneg_left (a34_sobolevNorm_mono hm₁le hdφ) (hK0 _)
    have hX' : ∫ ω, |A * η ω (propagator D ρ 0 t φ) - A * η ω (propagator D ρ 0 t φ')| ∂P ≤
        2 * |Cin| * (K m₁ * Dn) := by
      refine hX.trans ?_
      calc |A| * (|Cin| * sobolevNorm (m₀ : ℝ) (fun x => propagator D ρ 0 t φ x -
            propagator D ρ 0 t φ' x)) ≤ 2 * (|Cin| * (K m₁ * Dn)) :=
            mul_le_mul hA2 (mul_le_mul_of_nonneg_left hwn (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (by norm_num)
        _ = _ := by ring
    -- the Gaussian part
    have hJd : (d : ℝ) / 2 < (m : ℝ) := by
      have h1 := a33_mStar_gt d
      have h2 : (mStar d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmS
      linarith
    obtain ⟨hρ, hΛ⟩ := a34_rho m hJd Rg s MB Λ VB ν₀ T D ρ hA
    set Kb : ℝ := K₂ * max (sobolevNorm (m : ℝ) φ) (sobolevNorm (m : ℝ) φ') with hKb
    have hmst : (mStar d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmS
    have hKb0 : 0 ≤ Kb := mul_nonneg hK₂0 (le_max_of_le_left (Real.sqrt_nonneg _))
    have hKφ : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ≤ Kb := by
      intro r hr x
      refine (((hrφ r hr).2.2 x).trans ?_)
      exact mul_le_mul_of_nonneg_left ((a34_sobolevNorm_mono hmst hφ).trans (le_max_left _ _)) hK₂0
    have hKφ' : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖Torus.grad (propagator D ρ r t φ') x‖ ≤ Kb := by
      intro r hr x
      refine (((hrφ' r hr).2.2 x).trans ?_)
      exact mul_le_mul_of_nonneg_left ((a34_sobolevNorm_mono hmst hφ').trans (le_max_right _ _)) hK₂0
    have hKN0 := hKb0
    obtain ⟨hum₁, hub₁⟩ := a34_u_meas_bd D ρ t φ f hcl hpe hKb0 hKφ
    obtain ⟨hum₂, hub₂⟩ := a34_u_meas_bd D ρ t φ' f' hcl' hpe' hKb0 hKφ'
    have hY : ∫ p, ‖a34_u D ρ t φ p - a34_u D ρ t φ' p‖ ^ 2 ∂(a33_mu0 d T) ≤
        t * (K 1 * Dn) ^ 2 := by
      refine a34_Y_H1 ht D D ρ ρ hum₁ hum₂ hub₁ hub₂ (fun r hr => (hrφ r hr).2.1)
        (fun r hr => (hrφ' r hr).2.1) (fun r hr => ?_)
      have hl := hlin r hr
      have hl' : (fun x => propagator D ρ r t φ x - propagator D ρ r t φ' x) =
          propagator D ρ r t (fun x => φ x - φ' x) := hl.symm
      rw [hl']
      obtain ⟨hmw, -⟩ := hrw r hr
      obtain ⟨hs1, hn1⟩ := hmw 1 le_rfl hm1
      simp only [Nat.cast_one] at hs1 hn1
      refine hn1.trans ?_
      exact mul_le_mul_of_nonneg_left
        (a34_sobolevNorm_mono (by exact_mod_cast hm1 : (1 : ℝ) ≤ (m : ℝ)) hdφ) (hK0 _)
    have hgd := a34_gauss_diff hpos ht.2 hρ hρ hΛ hΛ D D hq0 hq0 f f' hcl hcl' hpe hpe' hKb0 hKφ hKφ'
      (δρ := 0) (δq := 0) (fun r hr x => by simp) (by simp) hY
    have hσ : |Real.sqrt (a34_cov D ρ q t φ) - Real.sqrt (a34_cov D ρ q t φ')| ≤
        Real.sqrt (8 * |Λ| * |T|) * K 1 * Dn := by
      refine hgd.trans ?_
      have hKD : 0 ≤ K 1 * Dn := mul_nonneg (hK0 1) hDn0
      have hΛa : |Λ| = Λ := abs_of_nonneg hΛ0
      have hTa : 0 ≤ T := hpos.le.trans ht.2
      have hTb : |T| = T := abs_of_nonneg hTa
      calc Real.sqrt (2 * Kb ^ 2 * (Λ * 0 + 2 * q * 0) * (a33_mu0 d T).real Set.univ +
            2 * (2 * q * Λ) * (t * (K 1 * Dn) ^ 2))
          ≤ Real.sqrt (8 * |Λ| * |T| * (K 1 * Dn) ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            rw [hΛa, hTb]
            have h1 : 2 * (2 * q * Λ) * (t * (K 1 * Dn) ^ 2) ≤ 8 * Λ * T * (K 1 * Dn) ^ 2 := by
              have e : 2 * (2 * q * Λ) * (t * (K 1 * Dn) ^ 2) = (4 * q * Λ) * t * (K 1 * Dn) ^ 2 := by ring
              rw [e]
              have h2 : 4 * q * Λ ≤ 8 * Λ := by nlinarith
              have h3 : (4 * q * Λ) * t ≤ (8 * Λ) * T :=
                mul_le_mul h2 ht.2 hpos.le (by positivity)
              exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
            linarith [h1]
        _ = Real.sqrt (8 * |Λ| * |T|) * K 1 * Dn := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKD]; ring
    have hc1 : 0 ≤ |Cin| * (K m₁ * Dn) := mul_nonneg (abs_nonneg _) (mul_nonneg (hK0 _) hDn0)
    have hc2 : 0 ≤ |Cin| * Dn := mul_nonneg (abs_nonneg _) hDn0
    have hc3 : 0 ≤ Real.sqrt (8 * |Λ| * |T|) * K 1 * Dn :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hK0 1)) hDn0
    calc _ ≤ 2 * |Cin| * (K m₁ * Dn) + Real.sqrt (8 * |Λ| * |T|) * K 1 * Dn := add_le_add hX' hσ
      _ ≤ _ := by nlinarith [hc1, hc2, hc3]

end HRS.A34
