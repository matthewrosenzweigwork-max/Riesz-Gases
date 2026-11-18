import HRS.Main.GFB3Aux3
import HRS.Main.GFB2Aux3

/-!
# Packet GFB3, part 4: `gf_trace_error` (pointwise trace-norm covariance error) and the closed `gf_trace_moment`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform

variable {d : ℕ}

lemma gfb3_majorant_nonneg (d : ℕ) (γ : ℝ) (i : ℕ) (k : NonzeroLattice d) :
    0 ≤ gfb3_majorant d γ i k := by
  unfold gfb3_majorant
  have := Torus.jp_pos k.1
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.rpow_nonneg this.le _)) (pow_nonneg this.le _)

lemma gfb3_Cn_nonneg (d : ℕ) (γ : ℝ) (i : ℕ) : 0 ≤ gfb3_Cn d γ i := by
  unfold gfb3_Cn
  refine mul_nonneg (Nat.cast_nonneg d) (Finset.sum_nonneg fun l _ => ?_)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun k => gfb3_majorant_nonneg d γ _ k))
    (tsum_nonneg fun k => gfb3_majorant_nonneg d γ _ k)

lemma gfb3_Chom_nonneg (d : ℕ) (α : ℝ) : 0 ≤ gfb3_Chom d α := by
  unfold gfb3_Chom
  exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)

lemma gfb3_F_props (hd1 : 1 ≤ d) {γ : ℝ} (hγ : (d : ℝ) + ((d + 1 : ℕ) : ℝ) + 1 < γ) (α : ℝ)
    (hα0 : 0 ≤ α) (hα : 2 * α ≤ d) (B : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ) (hB : ‖B‖ ≤ 1) :
    Torus.IsCk 2 (gfb3_F γ B) ∧ HasFiniteHomSobolev α (gfb3_F γ B) ∧
      homSobolev α (gfb3_F γ B) ≤ gfb3_Chom d α * gfb3_Cn d γ (d + 1) ∧
      ∀ x, |Torus.laplacian (gfb3_F γ B) x| ≤
        d * (gfb3_Cn d γ 0 + gfb3_Cn d γ 1 + gfb3_Cn d γ 2) := by
  have hcd := gfb3_F_contDiff (d + 1) hγ B
  have hCk : Torus.IsCk 2 (gfb3_F γ B) := hcd.of_le (by exact_mod_cast (by omega : 2 ≤ d + 1))
  have hCn := gfb3_Cn_nonneg d γ
  have hhom := gfb3_hom_bound α hα0 hα hcd (K := ‖B‖ * gfb3_Cn d γ (d + 1))
    (fun y => gfb3_F_iter_bound (d + 1) hγ B (d + 1) le_rfl y)
  refine ⟨hCk, hhom.1, hhom.2.trans ?_, fun x => ?_⟩
  · exact mul_le_mul_of_nonneg_left (by nlinarith [hCn (d + 1), norm_nonneg B]) (gfb3_Chom_nonneg d α)
  · have h1 := HRS.PDE.MFPair.abs_laplacian_le (L := 2) le_rfl hCk x
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d))
    unfold Torus.cbNorm
    have hb : ∀ j ∈ Finset.range 3, (⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (gfb3_F γ B)) y‖) ≤
        gfb3_Cn d γ j := by
      intro j hj
      have hj' : j ≤ d + 1 := by have := Finset.mem_range.mp hj; omega
      refine ciSup_le fun y => ?_
      exact (gfb3_F_iter_bound (d + 1) hγ B j hj' y).trans
        (by nlinarith [hCn j, norm_nonneg B])
    calc _ ≤ ∑ j ∈ Finset.range 3, gfb3_Cn d γ j := Finset.sum_le_sum hb
      _ = _ := by simp [Finset.sum_range_succ]

set_option maxHeartbeats 1600000 in
theorem gf_trace_error_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (γ : ℕ) (hγ : 2 * d + 10 < γ)
    (Λ : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (γ + 2 * d + 12) ρ →
        Torus.cbNorm (γ + 2 * d + 12) ρ ≤ Λ → ∀ X : Config d N, X ∉ collisionSet d N →
        ∀ q : ℝ, 0 ≤ q →
          traceNormForm (covForm (γ : ℝ) q (empirical X) - covForm (γ : ℝ) q (withDensityReal ρ)) ≤
            C * q * (Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) +
              (N : ℝ) ^ (-(2 : ℝ) / d)) := by
  classical
  have hγR : (d : ℝ) + ((d + 1 : ℕ) : ℝ) + 1 < (γ : ℝ) := by
    have : ((2 * d + 10 : ℕ) : ℝ) < (γ : ℝ) := by exact_mod_cast hγ
    push_cast at this ⊢
    linarith
  have hγ2 : (d : ℝ) / 2 + 2 < (γ : ℝ) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    push_cast at hγR
    linarith
  obtain ⟨C₀min, hC⟩ := HRS.Uniform.Q12.filtered_coercivity_proof hd s hs0 hsd Λ
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨Cf, hCf, hmain⟩ := hC C₀ hC₀ 1 le_rfl
  set α : ℝ := ((d : ℝ) - s) / 2 with hαdef
  have hα0 : 0 ≤ α := by rw [hαdef]; linarith
  have hα : 2 * α ≤ d := by rw [hαdef]; linarith
  set Kh : ℝ := gfb3_Chom d α * gfb3_Cn d (γ : ℝ) (d + 1) with hKh
  set KΔ : ℝ := d * (gfb3_Cn d (γ : ℝ) 0 + gfb3_Cn d (γ : ℝ) 1 + gfb3_Cn d (γ : ℝ) 2) with hKΔ
  have hKh0 : 0 ≤ Kh := mul_nonneg (gfb3_Chom_nonneg d α) (gfb3_Cn_nonneg d _ _)
  have hKΔ0 : 0 ≤ KΔ := mul_nonneg (Nat.cast_nonneg d) (add_nonneg (add_nonneg (gfb3_Cn_nonneg d _ _)
    (gfb3_Cn_nonneg d _ _)) (gfb3_Cn_nonneg d _ _))
  refine ⟨2 * Cf * (Kh + KΔ + 1), by positivity, ?_⟩
  intro N hN ρ hρ hρk hρΛ X hX q hq
  have hρle : ∀ x, ρ x ≤ Λ := by
    intro x
    have h0 := HRS.PDE.ET.norm_iteratedFDeriv_le_cbNorm (φ := ρ) (k := γ + 2 * d + 12) (j := 0)
      (Nat.zero_le _) hρk (Torus.rep x)
    rw [norm_iteratedFDeriv_zero] at h0
    have : Torus.lift ρ (Torus.rep x) = ρ x := by simp [Torus.lift, Torus.mk_rep]
    rw [this, Real.norm_eq_abs] at h0
    exact (le_abs_self _).trans (h0.trans hρΛ)
  obtain ⟨hnn, hbd⟩ := hmain N hN ρ hρ hρle X hX
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure (by omega) X
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ
  set E : ℝ := rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N with hE
  set n : ℝ := (N : ℝ) ^ (-(2 : ℝ) / d) with hn
  have hn0 : 0 ≤ n := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hsq0 : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hRHS : 0 ≤ 2 * Cf * (Kh + KΔ + 1) * q * (Real.sqrt E + n) :=
    mul_nonneg (mul_nonneg (by positivity) hq) (add_nonneg hsq0 hn0)
  unfold traceNormForm
  refine Real.iSup_le (fun p => ?_) hRHS
  obtain ⟨⟨m, e, f⟩, he, hf⟩ := p
  show ∑ i : Fin m, |(covForm (γ : ℝ) q (empirical X) - covForm (γ : ℝ) q (withDensityReal ρ)) (e i) (f i)| ≤ _
  set D := covForm (γ : ℝ) q (empirical X) - covForm (γ : ℝ) q (withDensityReal ρ) with hD
  set ε : Fin m → ℝ := fun i => if 0 ≤ D (e i) (f i) then 1 else -1 with hεdef
  have hε : ∀ i, |ε i| ≤ 1 := by
    intro i; simp only [hεdef]; split_ifs <;> simp
  have habs : ∀ i, |D (e i) (f i)| = ε i * D (e i) (f i) := by
    intro i
    simp only [hεdef]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hB := gfb3_B_norm_le e f ε hε he hf
  obtain ⟨hCk, hfin, hhom, hlap⟩ := gfb3_F_props hd hγR α hα0 hα (gfb3_B e f ε) hB
  have hsum : ∑ i, |D (e i) (f i)| = 2 * q * (∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(empirical X) -
      ∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(withDensityReal ρ)) := by
    simp_rw [habs]
    have h1 := gfb3_family_cov hγ2 hq (empirical X) e f ε
    have h2 := gfb3_family_cov hγ2 hq (withDensityReal ρ) e f ε
    simp only [hD, ContinuousLinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib, h1, h2]
  rw [hsum]
  have hco := hbd (gfb3_F (γ : ℝ) (gfb3_B e f ε)) (by simpa using hCk) hfin (KΔ) hKΔ0
    (by intro x; simpa using hlap x)
  have e1 : (-(2 * ((1 : ℕ) : ℝ))) / (d : ℝ) = -(2 : ℝ) / d := by norm_num
  rw [e1] at hco
  have hhom' : homSobolev α (gfb3_F (γ : ℝ) (gfb3_B e f ε)) ≤ Kh := hhom
  have hco2 : |∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(empirical X) -
      ∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(withDensityReal ρ)| ≤ Cf * Kh * Real.sqrt E + Cf * n * KΔ := by
    refine hco.trans ?_
    have := mul_le_mul_of_nonneg_left hhom' hCf.le
    nlinarith [mul_le_mul_of_nonneg_right this hsq0]
  calc 2 * q * (∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(empirical X) -
        ∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(withDensityReal ρ))
      ≤ 2 * q * |∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(empirical X) -
        ∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(withDensityReal ρ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ 2 * q * (Cf * Kh * Real.sqrt E + Cf * n * KΔ) := mul_le_mul_of_nonneg_left hco2 (by positivity)
    _ ≤ _ := by
        have h3 : Cf * Kh * Real.sqrt E + Cf * n * KΔ ≤ Cf * (Kh + KΔ + 1) * (Real.sqrt E + n) := by
          nlinarith [mul_nonneg hCf.le hKh0, mul_nonneg hCf.le hKΔ0, mul_nonneg hCf.le hsq0,
            mul_nonneg hCf.le hn0, mul_nonneg (mul_nonneg hCf.le hKh0) hn0,
            mul_nonneg (mul_nonneg hCf.le hKΔ0) hsq0, mul_nonneg (mul_nonneg hCf.le hsq0) hn0]
        nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * q)]

example := (@gf_trace_error_proof : type_of% @HRS.GF.gf_trace_error)

/-- `gf_trace_moment`, closed: the reduction `gfb2_trace_moment_of_error` applied to the proved `gf_trace_error_proof`. -/
theorem gf_trace_moment_proof' (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P ≤
          ENNReal.ofReal (C * qN S N *
            (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 : ℝ) / d))) :=
  gfb2_trace_moment_of_error (@gf_trace_error_proof) b M

example := (@gf_trace_moment_proof' : type_of% @HRS.GF.gf_trace_moment)

end HRS.GF
