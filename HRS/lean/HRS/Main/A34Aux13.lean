import HRS.Main.A34Aux12

/-!
# Packet A34, helper 13: stability of the statistic at base regularity (abstract data)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_int_tri {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f₁ g₁ f₂ g₂ : Ω → ℝ}
    (h1 : Integrable f₁ P) (h2 : Integrable g₁ P) (h3 : Integrable f₂ P) (h4 : Integrable g₂ P) :
    ∫ ω, |f₁ ω - g₁ ω| ∂P ≤ ∫ ω, |f₁ ω - f₂ ω| ∂P + ∫ ω, |f₂ ω - g₂ ω| ∂P +
      ∫ ω, |g₂ ω - g₁ ω| ∂P := by
  have I1 : Integrable (fun ω => |f₁ ω - f₂ ω|) P := (h1.sub h3).abs
  have I2 : Integrable (fun ω => |f₂ ω - g₂ ω|) P := (h3.sub h4).abs
  have I3 : Integrable (fun ω => |g₂ ω - g₁ ω|) P := (h4.sub h2).abs
  have I0 : Integrable (fun ω => |f₁ ω - g₁ ω|) P := (h1.sub h2).abs
  calc ∫ ω, |f₁ ω - g₁ ω| ∂P ≤ ∫ ω, (|f₁ ω - f₂ ω| + |f₂ ω - g₂ ω| + |g₂ ω - g₁ ω|) ∂P := by
        refine integral_mono I0 ((I1.add I2).add I3) fun ω => ?_
        have h5 := abs_sub_le (f₁ ω) (f₂ ω) (g₁ ω)
        have h6 := abs_sub_le (f₂ ω) (g₂ ω) (g₁ ω)
        have h7 := abs_sub_comm (g₂ ω) (g₁ ω)
        have h8 : |f₁ ω - g₁ ω| ≤ |f₁ ω - f₂ ω| + |f₂ ω - g₁ ω| := h5
        linarith
    _ = _ := by
        have I12 : Integrable (fun ω => |f₁ ω - f₂ ω| + |f₂ ω - g₂ ω|) P := I1.add I2
        rw [integral_add I12 I3, integral_add I1 I2]

theorem a34_cov_nonneg {T t : ℝ} (ht : t ∈ Set.Icc 0 T) (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hρ : A33Rho T ρ) (φ : Torus d → ℝ) : 0 ≤ a34_cov D ρ q t φ := by
  unfold a34_cov
  refine mul_nonneg (by linarith) (setIntegral_nonneg measurableSet_Icc fun r hr => ?_)
  refine integral_nonneg fun x => ?_
  have hrt : r ≤ t := by simpa using hr.2
  have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hrt.trans ht.2⟩
  exact mul_nonneg real_inner_self_nonneg (hρ.nonneg r hrT x)

theorem a34_psi_facts (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (ν₀ MB Λ VB T : ℝ) (m m₀ : ℕ) (hm₀ : m₀ ≤ m) (hmS : mStar d ≤ m)
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (hA : AdjointData s m Rg MB Λ VB D ν₀ T ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (m : ℝ) φ) :
    MemSobolev (m₀ : ℝ) (propagator D ρ 0 t φ) ∧ Continuous (propagator D ρ 0 t φ) := by
  have hm₀m : (m₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm₀
  have hm1 : 1 ≤ m := by have := ClassicalPart.three_le_mStar d; omega
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [a34_prop_zero hd m hmS Rg s MB Λ VB ν₀ T D ρ hA hφc hφ]
    exact ⟨MFAdjoint.memSobolev_mono_idx hφ hm₀m, hφc⟩
  · obtain ⟨K, K₂, hK0, hK₂0, hu⟩ := a34_unif hd s hs0 hsd m hmS Rg MB Λ VB ν₀ T
    obtain ⟨-, hr⟩ := hu D ρ hA ⟨hpos, ht.2⟩ hφc hφ
    obtain ⟨hm1ψ, hC2ψ, -⟩ := hr 0 ⟨le_rfl, hpos.le⟩
    obtain ⟨hs, -⟩ := hm1ψ m hm1 le_rfl
    exact ⟨MFAdjoint.memSobolev_mono_idx hs hm₀m, ClassicalAux.continuous_of_isCk
      (ClassicalAux.isCk_of_le (by norm_num) hC2ψ)⟩

theorem a34_base_abstract (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (ν₀ MB Λ VB T Cin : ℝ) (m m₀ : ℕ) (hm₀ : m₀ ≤ m) (hmS : mStar d ≤ m) :
    ∃ c C : ℝ, 0 ≤ c ∧ 0 < C ∧
      ∀ (D₁ D₂ : DynData d) (ρ₁ ρ₂ : ℝ → Torus d → ℝ) (A₁ A₂ q₁ q₂ Δ : ℝ),
        AdjointData s (m + 2) Rg MB Λ VB D₁ ν₀ T ρ₁ →
        AdjointData s (m + 2) Rg MB Λ VB D₂ ν₀ T ρ₂ → D₁.M = D₂.M → D₁.V = D₂.V → 0 ≤ Δ →
        Δ ≤ 1 → (∀ r ∈ Set.Icc (0 : ℝ) T, Torus.cbNorm (m + 2) (ρ₁ r - ρ₂ r) ≤ Δ) →
        |D₁.invβ - D₂.invβ| ≤ Δ → 0 ≤ q₁ → q₁ ≤ 1 → 0 ≤ q₂ → |2 * q₁ - 2 * q₂| ≤ Δ →
        |A₁| ≤ 1 → |A₁ - A₂| ≤ Δ →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (η : Ω → (Torus d → ℝ) → ℝ), XHyp P η m₀ Cin →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ φ' : Torus d → ℝ, Continuous φ → MemSobolev (m : ℝ) φ →
          Continuous φ' → MemSobolev ((m + 2 : ℕ) : ℝ) φ' →
          wassersteinE 1 (surrogateStatLaw D₁ ρ₁ A₁ q₁ (fun _ : Fin 1 => t) (fun _ => φ) P η)
            (surrogateStatLaw D₂ ρ₂ A₂ q₂ (fun _ : Fin 1 => t) (fun _ => φ) P η) ≤
          ENNReal.ofReal (C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ' * (Δ + Real.sqrt Δ) +
            c * sobolevNorm (m : ℝ) (fun x => φ x - φ' x)) := by
  have hm1 : 1 ≤ m := by have := ClassicalPart.three_le_mStar d; omega
  obtain ⟨c₀, hc₀, hpert⟩ := a34_perturb hd s hs0 hsd Rg ν₀ MB Λ VB T Cin m m₀ hm₀ hmS
  obtain ⟨C, hC, hreal⟩ := a34_stat_real hd s hs0 hsd Rg ν₀ MB Λ VB T Cin m m₀ hm1 hm₀ (by omega)
  refine ⟨2 * c₀, C, by positivity, hC, ?_⟩
  intro D₁ D₂ ρ₁ ρ₂ A₁ A₂ q₁ q₂ Δ hA₁ hA₂ hM hV hΔ hΔ1 hρΔ hβΔ hq₁0 hq₁1 hq₂0 hqΔ hA₁1 hAΔ
    Ω _ P _ η hη t ht φ φ' hφc hφ hφ'c hφ'
  have hA₁m : AdjointData s m Rg MB Λ VB D₁ ν₀ T ρ₁ :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hA₁
  have hA₂m : AdjointData s m Rg MB Λ VB D₂ ν₀ T ρ₂ :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hA₂
  have hcast : (((m + 2 : ℕ)) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hφ'm : MemSobolev (m : ℝ) φ' := MFAdjoint.memSobolev_mono_idx hφ' (by rw [hcast]; linarith)
  have hq2 : 2 * q₂ ≤ 3 := by have := (abs_le.1 hqΔ).1; linarith
  have hA₂2 : |A₂| ≤ 2 := by
    have h := abs_sub_abs_le_abs_sub A₂ A₁
    rw [abs_sub_comm] at h
    linarith
  have hJd : (d : ℝ) / 2 < (m : ℝ) := by
    have h1 := a33_mStar_gt d
    have h2 : (mStar d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmS
    linarith
  obtain ⟨hρ₁, -⟩ := a34_rho m hJd Rg s MB Λ VB ν₀ T D₁ ρ₁ hA₁m
  obtain ⟨hρ₂, -⟩ := a34_rho m hJd Rg s MB Λ VB ν₀ T D₂ ρ₂ hA₂m
  -- the statistic at `φ'`
  obtain ⟨hm₁', hc₁', hm₂', hc₂', hv₁', hv₂', hbd'⟩ := hreal D₁ D₂ ρ₁ ρ₂ A₁ A₂ q₁ q₂ Δ hA₁ hA₂ hM hV
    hΔ hρΔ hβΔ hq₁0 hq₁1 hq₂0 hqΔ hA₁1 hAΔ P η hη t ht φ' hφ' hφ'c
  -- the perturbation
  have hp₁ := hpert D₁ ρ₁ A₁ q₁ hA₁m (by linarith) hq₁0 (by linarith) P η hη t ht φ φ' hφc hφ
    hφ'c hφ'm
  have hp₂ := hpert D₂ ρ₂ A₂ q₂ hA₂m hA₂2 hq₂0 (by linarith) P η hη t ht φ φ' hφc hφ hφ'c hφ'm
  -- facts at `φ`
  obtain ⟨hm₁, hc₁⟩ := a34_psi_facts hd s hs0 hsd Rg ν₀ MB Λ VB T m m₀ hm₀ hmS D₁ ρ₁ hA₁m ht hφc hφ
  obtain ⟨hm₂, hc₂⟩ := a34_psi_facts hd s hs0 hsd Rg ν₀ MB Λ VB T m m₀ hm₀ hmS D₂ ρ₂ hA₂m ht hφc hφ
  rw [a34_stat_unfold, a34_stat_unfold]
  refine (a34_W1_conv P (fun ω => A₁ * η ω (propagator D₁ ρ₁ 0 t φ))
    (fun ω => A₂ * η ω (propagator D₂ ρ₂ 0 t φ)) ((hη.meas _).const_mul _) ((hη.meas _).const_mul _)
    ((a34_X_integrable hη hm₁ hc₁ A₁).sub (a34_X_integrable hη hm₂ hc₂ A₂)) _ _
    (a34_cov_nonneg ht D₁ ρ₁ q₁ hq₁0 hρ₁ φ) (a34_cov_nonneg ht D₂ ρ₂ q₂ hq₂0 hρ₂ φ)).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hX := a34_int_tri (P := P)
    (a34_X_integrable hη hm₁ hc₁ A₁) (a34_X_integrable hη hm₂ hc₂ A₂)
    (a34_X_integrable hη hm₁' hc₁' A₁) (a34_X_integrable hη hm₂' hc₂' A₂)
  have hX2 : ∫ ω, |A₂ * η ω (propagator D₂ ρ₂ 0 t φ') - A₂ * η ω (propagator D₂ ρ₂ 0 t φ)| ∂P =
      ∫ ω, |A₂ * η ω (propagator D₂ ρ₂ 0 t φ) - A₂ * η ω (propagator D₂ ρ₂ 0 t φ')| ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact abs_sub_comm _ _
  rw [hX2] at hX
  have hσ := abs_sub_le (Real.sqrt (a34_cov D₁ ρ₁ q₁ t φ)) (Real.sqrt (a34_cov D₁ ρ₁ q₁ t φ'))
    (Real.sqrt (a34_cov D₂ ρ₂ q₂ t φ))
  have hσ2 := abs_sub_le (Real.sqrt (a34_cov D₁ ρ₁ q₁ t φ')) (Real.sqrt (a34_cov D₂ ρ₂ q₂ t φ'))
    (Real.sqrt (a34_cov D₂ ρ₂ q₂ t φ))
  have hσ3 := abs_sub_comm (Real.sqrt (a34_cov D₂ ρ₂ q₂ t φ')) (Real.sqrt (a34_cov D₂ ρ₂ q₂ t φ))
  have hcc : 2 * c₀ * sobolevNorm (m : ℝ) (fun x => φ x - φ' x) =
      c₀ * sobolevNorm (m : ℝ) (fun x => φ x - φ' x) +
        c₀ * sobolevNorm (m : ℝ) (fun x => φ x - φ' x) := by ring
  linarith [hp₁, hp₂, hbd', hX, hσ, hσ2, hσ3, hcc]

end HRS.A34
