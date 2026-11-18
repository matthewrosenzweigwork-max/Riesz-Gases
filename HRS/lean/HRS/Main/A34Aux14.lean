import HRS.Main.A34Aux13

/-!
# Packet A34, helper 14: Proposition A.34 (i), qualitative (base regularity)
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_base_main (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB Cin : ℝ) (m m₀ : ℕ) (hm₀ : m₀ ≤ m)
    (hmS : mStar d ≤ m) (S : MainData d) (hs : S.s = s) (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (m + 2) m)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Ω → (Torus d → ℝ) → ℝ) (hη : XHyp P η m₀ Cin) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (φ : Torus d → ℝ) (hφ : MemSobolev (m : ℝ) φ) (hφc : Continuous φ) :
    Tendsto (fun N => wassersteinE 1
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t) (fun _ => φ) P η)
      (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ) P η))
      atTop (𝓝 0) := by
  have hs0 : 0 ≤ s := hs ▸ S.hs0
  have hsd : s < d := hs ▸ S.hsd
  obtain ⟨c, C, hc, hC, h⟩ := a34_base_abstract S.hd s hs0 hsd Rg ν₀ MB Λ VB T Cin m m₀ hm₀ hmS
  subst hs hT
  obtain ⟨e⟩ := a33_exists_equiv S.hd
  obtain ⟨-, hlim⟩ := a34_trunc_sob hφc hφ e
  -- smooth approximants
  have happ : ∀ n, Continuous (fun x => Torus.mean φ + a33_tr φ e n x) ∧
      MemSobolev ((m + 2 : ℕ) : ℝ) (fun x => Torus.mean φ + a33_tr φ e n x) := by
    intro n
    have hsm : Torus.IsSmooth (fun x => Torus.mean φ + a33_tr φ e n x) := by
      have h1 := a33_tr_smooth φ e n
      unfold Torus.IsSmooth Torus.IsCk at *
      show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => Torus.mean φ + a33_tr φ e n (Torus.mk x))
      exact contDiff_const.add h1
    exact ⟨a33_cont hsm, a33_memSob _ hsm⟩
  have hres : ∀ n, sobolevNorm (m : ℝ) (fun x => φ x - (Torus.mean φ + a33_tr φ e n x)) =
      sobolevNorm (m : ℝ) (a33_res φ e n) := by
    intro n
    congr 1
    funext x
    simp only [a33_res]
    ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact Eventually.of_forall fun N => hεt ▸ le_top
  have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  have hε' : ENNReal.ofReal ε.toReal = ε := ENNReal.ofReal_toReal hεt
  set e0 := ε.toReal with he0def
  -- choose the approximant
  have hsmall : ∀ᶠ n in atTop, sobolevNorm (m : ℝ) (a33_res φ e n) < e0 / 2 / (c + 1) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨n, hn⟩ := hsmall.exists
  set φ' : Torus d → ℝ := fun x => Torus.mean φ + a33_tr φ e n x with hφ'
  obtain ⟨hφ'c, hφ'm⟩ := happ n
  have hpert : c * sobolevNorm (m : ℝ) (fun x => φ x - φ' x) < e0 / 2 := by
    have := hres n
    have h1 : c * sobolevNorm (m : ℝ) (fun x => φ x - φ' x) ≤ (c + 1) * sobolevNorm (m : ℝ)
        (a33_res φ e n) := by
      rw [show sobolevNorm (m : ℝ) (fun x => φ x - φ' x) = sobolevNorm (m : ℝ) (a33_res φ e n) from
        hres n]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    have h2 : (c + 1) * sobolevNorm (m : ℝ) (a33_res φ e n) < e0 / 2 := by
      have := mul_lt_mul_of_pos_left hn (by positivity : 0 < c + 1)
      rwa [mul_div_cancel₀ _ (by positivity)] at this
    linarith
  -- convergence of the discrepancy
  set Np : ℝ := C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ' with hNp
  have hNp0 : 0 ≤ Np := mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hΔt := hcoef.tendsto
  have hΔs : Tendsto (fun N => S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N))
      atTop (𝓝 0) := by
    have := hΔt.add ((Real.continuous_sqrt.tendsto 0).comp hΔt)
    simpa using this
  have hev1 : ∀ᶠ N in atTop, S.coeffDiscrepancy L m N ≤ 1 :=
    hΔt.eventually (ge_mem_nhds (by norm_num))
  have hev2 : ∀ᶠ N in atTop, S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N) <
      e0 / 2 / (Np + 1) := hΔs.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev1, hev2, eventually_ge_atTop 1] with N h1 h2 hN
  have hAN := hcoef.seq_adjoint N hN
  have hAL := hcoef.limit_adjoint
  obtain ⟨hΔ0, hρΔ, hβΔ, hqΔ, hAΔ⟩ := a34_delta_facts S L m N Rg ν₀ MB Λ VB
    (HRS.PDE.StabAux.adjointData_mono (by omega) hAN) (HRS.PDE.StabAux.adjointData_mono (by omega) hAL)
  have hAN' := hcoef.seq_adjoint N hN
  obtain ⟨hΔ0', hρΔ', hβΔ', hqΔ', hAΔ'⟩ := a34_delta_facts S L m N Rg ν₀ MB Λ VB hAN hAL
  have hq := a34_qScale_bounds (N := N) (by omega) (S.hκ N) (S.hinvβ N)
  have hA1 := a34_Ascale_abs_le (N := N) (κ := S.κ N) (invβ := S.invβ N) (S.hκ N)
  refine (h (S.dyn N) (L.dyn S) (S.ρ N) L.ρ (S.AN N) L.A (S.qN N) L.invβstar
    (S.coeffDiscrepancy L m N) hAN hAL rfl rfl hΔ0' h1 hρΔ' hβΔ' hq.1 hq.2 L.hinvβstar hqΔ' hA1 hAΔ'
    P η hη t ht φ φ' hφc hφ hφ'c hφ'm).trans ?_
  rw [← hε']
  refine ENNReal.ofReal_le_ofReal ?_
  have h3 : Np * (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N)) ≤ e0 / 2 := by
    have h4 := mul_le_mul_of_nonneg_left h2.le hNp0
    refine h4.trans ?_
    have : Np * (e0 / 2 / (Np + 1)) ≤ e0 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [he0]
    exact this
  have h5 : C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ' *
      (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N)) =
      Np * (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N)) := rfl
  rw [h5]
  linarith

end HRS.A34
