import HRS.Whole.AppendixALemmas2

/-!
# Packet MPINCR: the propagator time-increment bound S.A.22(i) on the torus

Proof of `HRS.Whole.AppendixALemmas.path_propagator_increment_torus` (statement:
`HRS/Whole/AppendixALemmas2.lean`).  Route: the forward generator `𝓛 = νΔ + b·∇ - 𝒢` maps `H^m` into
`H^{m-2}` with a bound uniform in `0 ≤ ν ≤ νbar` (`TRB.firstOrder_bound` and the Laplacian bound), so a
forward solution is Lipschitz in `H^{m-2}` in time (`quotient_sq_bound`); then the semigroup property and
linearity of the propagator give `U^{r,t}φ - U^{r,s'}φ = U^{r,s'}(U^{s',t}φ - φ)`, and
`adjoint_torus_classical` bounds `U^{r,s'}` on `H^{m-2}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.MP.PropIncr

open HRS HRS.PDE

variable {d : ℕ}

/-! ### Stage 1: the generator maps `H^m` to `H^{m-2}` uniformly in `0 ≤ ν ≤ νbar` -/

theorem mpi_gen_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB νbar : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ), D.invβ ≤ νbar →
      ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ F : Coeff d, MemHs (m : ℝ) F →
        MemHs ((m : ℝ) - 2) (forwardGen D (μ r) F) ∧
        hsNormSq ((m : ℝ) - 2) (forwardGen D (μ r) F) ≤ K * hsNormSq (m : ℝ) F := by
  obtain ⟨K1, hK1, hKb⟩ := TRB.firstOrder_bound hd s hs0 hsd m hm MB Λ VB
  refine ⟨2 * (max νbar 0) ^ 2 + 2 * K1, by positivity, ?_⟩
  intro D ν₀ T μ hA hν r hr F hF
  obtain ⟨hP1, hP2⟩ := hKb D hA.hs hA.hM hA.hV (μ r) (hA.hμ.prob r hr) (hA.hμ.smooth r hr)
    (hA.hμ.bound r hr) F hF
  have hle : (m : ℝ) - 2 ≤ (m : ℝ) - 2 + TRB.eps d s := by
    have := TRB.eps_pos hsd; linarith
  have hP3 := hsNormSq_mono hle hP1
  have hF2 : MemHs (((m : ℝ) - 2) + 2) F := by
    have : ((m : ℝ) - 2) + 2 = m := by ring
    rw [this]; exact hF
  obtain ⟨hL1, hL2⟩ := StabAux.laplace_bound hF2
  have e : ((m : ℝ) - 2) + 2 = m := by ring
  rw [e] at hL2
  obtain ⟨hQ1, hQ2⟩ := StabAux.hsNormSq_const_mul ((m : ℝ) - 2) ((D.invβ : ℝ) : ℂ) _ hL1
  have hν2 : D.invβ ^ 2 ≤ (max νbar 0) ^ 2 := by
    have h0 : 0 ≤ D.invβ := D.hβ
    exact pow_le_pow_left₀ h0 (hν.trans (le_max_left _ _)) 2
  have hQ3 : hsNormSq ((m : ℝ) - 2) (fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff F k) ≤
      (max νbar 0) ^ 2 * hsNormSq (m : ℝ) F := by
    rw [hQ2, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul hν2 hL2 (hsNormSq_nonneg _ _) (sq_nonneg _)
  have hG : forwardGen D (μ r) F = (fun k => ((D.invβ : ℝ) : ℂ) * laplaceCoeff F k) +
      (fun k => transportCoeff D (μ r) F k - nonlocalCoeff D (μ r) F k) := by
    funext k
    simp only [forwardGen, Pi.add_apply]
    ring
  have hP1' : MemHs ((m : ℝ) - 2) (fun k => transportCoeff D (μ r) F k - nonlocalCoeff D (μ r) F k) :=
    hP1.mono hle
  obtain ⟨hs1, hs2⟩ := ET.memHs_add_sq hQ1 hP1'
  rw [hG]
  refine ⟨hs1, hs2.trans ?_⟩
  have := add_le_add (mul_le_mul_of_nonneg_left hQ3 (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left (hP3.trans hP2) (by norm_num : (0 : ℝ) ≤ 2))
  refine this.trans (le_of_eq ?_)
  ring


/-! ### Stage 2: Lipschitz continuity of a forward solution in `H^{m-2}` -/

theorem mpi_coeff_increment (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB νbar : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ), D.invβ ≤ νbar →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φc : Coeff d, MemHs (m : ℝ) φc →
      ∀ B : ℝ, 0 ≤ B → (∀ σ ∈ Set.Icc (0 : ℝ) t, PDE.hsNorm (m : ℝ) (propagatorCoeff D μ (m : ℝ) t φc σ) ≤ B) →
      ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ τ' ∈ Set.Icc (0 : ℝ) t,
        MemHs ((m : ℝ) - 2) (propagatorCoeff D μ (m : ℝ) t φc τ' - propagatorCoeff D μ (m : ℝ) t φc τ) ∧
        hsNormSq ((m : ℝ) - 2) (propagatorCoeff D μ (m : ℝ) t φc τ' - propagatorCoeff D μ (m : ℝ) t φc τ) ≤
          10 * K * B ^ 2 * (τ' - τ) ^ 2 := by
  obtain ⟨K, hK0, hKg⟩ := mpi_gen_bound hd s hs0 hsd m hm R MB Λ VB νbar
  refine ⟨K, hK0, ?_⟩
  intro D ν₀ T μ hA hν t ht φc hφ B hB0 hBd τ hτ τ' hτ'
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨hsol, hw, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  set F : ℝ → Coeff d := propagatorCoeff D μ (m : ℝ) t φc with hFdef
  set G : ℝ → Coeff d := fun σ => forwardGen D (μ (t - σ)) (F σ) with hGdef
  have hFB : ∀ σ ∈ Set.Icc (0 : ℝ) t, hsNormSq (m : ℝ) (F σ) ≤ B ^ 2 := by
    intro σ hσ
    have h1 := hBd σ hσ
    unfold PDE.hsNorm at h1
    exact (Real.sqrt_le_iff.mp h1).2
  have hGb : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs ((m : ℝ) - 2) (G σ) ∧
      hsNormSq ((m : ℝ) - 2) (G σ) ≤ K * B ^ 2 := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := hKg D ν₀ T μ hA hν (t - σ) (ET.tsub_mem_Icc ht hσ) (F σ) (hw.1 σ hσ)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hFB σ hσ) hK0)⟩
  by_cases hne : τ' = τ
  · subst hne
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero]
    refine ⟨by simp [MemHs], ?_⟩
    simp [hsNormSq]
  · have hG : ContinuousInHs ((m : ℝ) - 2) G t :=
      (adjoint_torus_time_regularity hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φc hφ).1
    have hint : ∀ k, ∀ u ∈ Set.Icc (0 : ℝ) t, IntervalIntegrable (fun σ => G σ k) volume 0 u := by
      intro k u hu
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hu.1]
      exact (hsol.integrable k).mono_set (Set.Icc_subset_Icc_right hu.2)
    have hFG : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ τ' ∈ Set.Icc (0 : ℝ) t,
        F τ' k - F τ k = ∫ σ in τ..τ', G σ k := by
      intro k τ hτ τ' hτ'
      rw [hsol.eq k τ hτ, hsol.eq k τ' hτ']
      rw [add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left (hint k τ' hτ')
        (hint k τ hτ)]
    set η : ℝ := 2 * Real.sqrt K * B with hη
    have hη0 : 0 ≤ η := by positivity
    have hη2 : η ^ 2 = 4 * (K * B ^ 2) := by
      rw [hη]; rw [mul_pow, mul_pow, Real.sq_sqrt hK0]; ring
    have hsup : ∀ σ ∈ Set.uIcc τ τ', hsNormSq ((m : ℝ) - 2) (G σ - G τ) ≤ η ^ 2 := by
      intro σ hσ
      have hσ' : σ ∈ Set.Icc (0 : ℝ) t := Set.uIcc_subset_Icc hτ hτ' hσ
      have h1 := hsNormSq_sub_le (hGb σ hσ').1 (hGb τ hτ).1
      rw [hη2]
      nlinarith [(hGb σ hσ').2, (hGb τ hτ).2]
    obtain ⟨hq1, hq2⟩ := TRB.quotient_sq_bound hG hFG hτ hτ' hne η hη0 hsup
    set h : ℂ := ((τ' - τ : ℝ) : ℂ) with hh
    have hh0 : h ≠ 0 := by rw [hh]; exact_mod_cast sub_ne_zero.mpr hne
    set q : Coeff d := fun k => (F τ' k - F τ k) / h - G τ k with hq
    obtain ⟨hs1, hs2⟩ := ET.memHs_add_sq hq1 (hGb τ hτ).1
    have heq : F τ' - F τ = fun k => h * ((q + G τ) k) := by
      funext k
      simp only [Pi.sub_apply, Pi.add_apply, hq]
      field_simp
      ring
    rw [heq]
    obtain ⟨hc1, hc2⟩ := StabAux.hsNormSq_const_mul ((m : ℝ) - 2) h (q + G τ) hs1
    refine ⟨hc1, ?_⟩
    rw [hc2, hh, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have : hsNormSq ((m : ℝ) - 2) (q + G τ) ≤ 10 * K * B ^ 2 := by
      have := (hGb τ hτ).2
      nlinarith [hq2, hη2]
    calc (τ' - τ) ^ 2 * hsNormSq ((m : ℝ) - 2) (q + G τ) ≤ (τ' - τ) ^ 2 * (10 * K * B ^ 2) :=
          mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = _ := by ring


/-! ### Stage 3: linearity of the forward solution operator in the datum -/

theorem mpi_weak_sub {m' t : ℝ} {F₁ F₂ : ℝ → Coeff d} (h₁ : WeakContinuousInHs m' F₁ t)
    (h₂ : WeakContinuousInHs m' F₂ t) : WeakContinuousInHs m' (fun σ => F₁ σ - F₂ σ) t := by
  refine ⟨fun τ hτ => memHs_sub (h₁.1 τ hτ) (h₂.1 τ hτ), fun G hG => ?_⟩
  refine ((h₁.2 G hG).sub (h₂.2 G hG)).congr fun τ hτ => ?_
  exact ET.hsInner_sub_left (h₁.1 τ hτ) (h₂.1 τ hτ) hG

theorem mpi_forward_sub (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d}
    {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ} (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) {φc φc' : Coeff d} {F₁ F₂ : ℝ → Coeff d}
    (h₁ : IsForwardSolution D μ t φc F₁) (h₂ : IsForwardSolution D μ t φc' F₂) :
    IsForwardSolution D μ t (φc - φc') (fun σ => F₁ σ - F₂ σ) := by
  obtain ⟨K, hK0, hKm⟩ := uniform_multBound hd hA
  have hrT : ∀ σ ∈ Set.Icc (0 : ℝ) t, t - σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hsub : ∀ σ ∈ Set.Icc (0 : ℝ) t, forwardGen D (μ (t - σ)) (F₁ σ - F₂ σ) =
      forwardGen D (μ (t - σ)) (F₁ σ) - forwardGen D (μ (t - σ)) (F₂ σ) := fun σ hσ =>
    forwardGen_sub_H1 D _ (hKm _ (hrT σ hσ)).1.memHs0
      (fun j => ((hKm _ (hrT σ hσ)).2 j).memHs0) (h₁.h1 σ hσ) (h₂.h1 σ hσ)
  refine ⟨fun σ hσ => memHs_sub (h₁.h1 σ hσ) (h₂.h1 σ hσ), fun k => ?_, fun k τ hτ => ?_⟩
  · refine ((h₁.integrable k).sub (h₂.integrable k)).congr_fun (fun σ hσ => ?_) measurableSet_Icc
    simp only [hsub σ hσ, Pi.sub_apply]
  · have hi : ∀ (F : ℝ → Coeff d), (∀ k, IntegrableOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k)
        (Set.Icc 0 t)) → IntervalIntegrable (fun σ => forwardGen D (μ (t - σ)) (F σ) k)
          volume 0 τ := fun F hF => by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
      exact (hF k).mono_set (Set.Icc_subset_Icc_right hτ.2)
    show F₁ τ k - F₂ τ k = (φc - φc') k + ∫ σ in (0:ℝ)..τ,
      forwardGen D (μ (t - σ)) (F₁ σ - F₂ σ) k
    have hc : ∫ σ in (0:ℝ)..τ, forwardGen D (μ (t - σ)) (F₁ σ - F₂ σ) k =
        ∫ σ in (0:ℝ)..τ, (forwardGen D (μ (t - σ)) (F₁ σ) k -
          forwardGen D (μ (t - σ)) (F₂ σ) k) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le hτ.1] at hσ
      simp only [hsub σ ⟨hσ.1, hσ.2.trans hτ.2⟩, Pi.sub_apply]
    rw [hc, intervalIntegral.integral_sub (hi F₁ h₁.integrable) (hi F₂ h₂.integrable),
      h₁.eq k τ hτ, h₂.eq k τ hτ]
    simp only [Pi.sub_apply]
    ring

theorem mpi_pc_sub (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T)
    (c₁ c₀ : Coeff d) (h₁ : MemHs (m : ℝ) c₁) (h₀ : MemHs (m : ℝ) c₀) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t, propagatorCoeff D μ (m : ℝ) t (c₁ - c₀) τ =
      propagatorCoeff D μ (m : ℝ) t c₁ τ - propagatorCoeff D μ (m : ℝ) t c₀ τ := by
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨s1, w1, -⟩ := hspec D ν₀ T μ hA t ht c₁ h₁
  obtain ⟨s0, w0, -⟩ := hspec D ν₀ T μ hA t ht c₀ h₀
  obtain ⟨sd, wd, -⟩ := hspec D ν₀ T μ hA t ht (c₁ - c₀) (memHs_sub h₁ h₀)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact forward_unique_H1 hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht (c₁ - c₀) _ _ sd
    (weakContinuousInHs_mono hm1 wd) (mpi_forward_sub hd hA ht s1 s0)
    (weakContinuousInHs_mono hm1 (mpi_weak_sub w1 w0))

theorem mpi_toFun_sub (a b : Coeff d) (ha : Summable fun k => ‖a k‖)
    (hb : Summable fun k => ‖b k‖) (x : Torus d) :
    toFun (a - b) x = toFun a x - toFun b x := by
  unfold toFun series
  have h1 := summable_series_terms a ha x
  have h2 := summable_series_terms b hb x
  have : (fun k => (a - b) k * Torus.mode k x) =
      fun k => a k * Torus.mode k x - b k * Torus.mode k x := by
    funext k; simp only [Pi.sub_apply]; ring
  rw [this, h1.tsum_sub h2, Complex.sub_re]


/-! ### Stage 4: the terminal-time-zero propagator and the main estimate -/

theorem mpi_isClassical_zero (D : DynData d) (hK : ClassicalAux.ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) (μ : ℝ → Torus d → ℝ) (hμ : Torus.IsCk 1 (μ 0)) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) : IsClassicalAdjointSolution D μ 0 ψ (fun _ => ψ) := by
  refine ⟨fun r hr => hψ, fun j hj => ?_, rfl, ?_, ?_⟩
  · have : Continuous fun y : Euc d => iteratedFDeriv ℝ j (Torus.lift ψ) y :=
      hψ.continuous_iteratedFDeriv (by exact_mod_cast hj)
    exact this.comp continuous_snd
  · intro x r hr
    exfalso
    simp at hr
  · have hc : Continuous (backwardGenerator D (μ 0) ψ) :=
      ClassicalPart.continuous_backwardGenerator D hK hV hμ hψ
    have h0 : ∀ p : Set.Icc (0 : ℝ) 0 × Torus d, p.1.1 = 0 := fun p => by
      have := p.1.2
      exact le_antisymm this.2 this.1
    refine (hc.comp continuous_snd).congr fun p => ?_
    simp only [Function.comp_apply, h0 p]

theorem mpi_propagator_zero (D : DynData d) (hK : ClassicalAux.ConvKernelFacts d D.s)
    (hV : Torus.IsCk 1 D.V) (μ : ℝ → Torus d → ℝ) (hμ : Torus.IsCk 1 (μ 0)) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) : propagator D μ 0 0 ψ = ψ := by
  have hex : ∃ f, IsClassicalAdjointSolution D μ 0 ψ f :=
    ⟨_, mpi_isClassical_zero D hK hV μ hμ hψ⟩
  simp only [propagator, hex, dite_true]
  exact hex.choose_spec.terminal


theorem mpi_zero_memSobolev (m' : ℝ) :
    MemSobolev m' (toFun (0 : Coeff d)) ∧ sobolevNorm m' (toFun (0 : Coeff d)) = 0 := by
  have h := ClassicalPart.memSobolev_toFun (m := m') (c := (0 : Coeff d))
    (by simp) (by simp [MemHs]) (by simp [IsRealCoeff])
  refine ⟨h.1, h.2.trans ?_⟩
  simp [PDE.hsNorm, hsNormSq]

theorem mpi_main (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m2 : ℕ)
    (hm : mStar d ≤ m2 + 2) (R : Regime) (MB Λ VB νbar ν₀ T : ℝ) :
    ∃ C : ℝ, ∀ (D : DynData d) (μ : ℝ → Torus d → ℝ),
      AdjointData s (m2 + 2) R MB Λ VB D ν₀ T μ → D.invβ ≤ νbar →
      ∀ r s' t : ℝ, 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ φ : Torus d → ℝ,
        MemSobolev (((m2 + 2 : ℕ)) : ℝ) φ → Continuous φ →
          MemSobolev (m2 : ℝ) (fun x => propagator D μ r t φ x - propagator D μ r s' φ x) ∧
          sobolevNorm (m2 : ℝ) (fun x => propagator D μ r t φ x - propagator D μ r s' φ x) ≤
            C * |t - s'| * sobolevNorm (((m2 + 2 : ℕ)) : ℝ) φ := by
  set m : ℕ := m2 + 2 with hmdef
  have hm3 : 3 ≤ m := ClassicalPart.one_le_of_mStar hm
  have hm1 : 1 ≤ m := by omega
  have hm2_1 : 1 ≤ m2 := by omega
  have hm2m : m2 ≤ m := by omega
  have hmd : (d : ℝ) / 2 < m := by
    obtain ⟨m'', h1, h2⟩ := ClassicalPart.exists_mid (d := d) hm
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hmd2 : (d : ℝ) / 2 + ((2 : ℕ) : ℝ) < m := by
    obtain ⟨m'', h1, h2⟩ := ClassicalPart.exists_mid (d := d) hm
    push_cast; linarith
  have hcast : ((m : ℝ) - 2) = (m2 : ℝ) := by rw [hmdef]; push_cast; ring
  obtain ⟨K, hK0, hKinc⟩ := mpi_coeff_increment hd s hs0 hsd m hm1 R MB Λ VB νbar
  obtain ⟨Cm, hCm, hspecm⟩ := propagatorCoeff_spec hd s hs0 hsd m hm1 R MB Λ VB
  obtain ⟨C₀, Cs, hC₀, hCs, hcls⟩ := adjoint_torus_classical hd s hs0 hsd m hm R MB Λ VB
  set l1 : ℝ := |R.lambdaM Cm ν₀ (thetaOrder d s)| with hl1
  set l2 : ℝ := |R.lambdaM (Cs m2) ν₀ (thetaOrder d s)| with hl2
  refine ⟨Real.exp (l2 * T) * (Real.sqrt (10 * K) * Real.exp (l1 * T)), ?_⟩
  intro D μ hA hν r s' t hr hrs hst htT φ hφS hφc
  have hT0 : 0 < T := hA.hT
  by_cases hseq : s' = t
  · subst hseq
    have hz : (fun x => propagator D μ r s' φ x - propagator D μ r s' φ x) = toFun (0 : Coeff d) := by
      funext x; simp [toFun, series]
    rw [hz]
    obtain ⟨h1, h2⟩ := mpi_zero_memSobolev (d := d) (m2 : ℝ)
    refine ⟨h1, ?_⟩
    rw [h2]; simp
  · have hlt : s' < t := lt_of_le_of_ne hst hseq
    have ht : t ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_lt (hr.trans hrs) hlt, htT⟩
    -- the datum
    obtain ⟨hc0, hc0n⟩ := hsNormSq_coeffOf (m : ℝ) φ hφS
    set c0 : Coeff d := coeffOf φ with hc0def
    have hre0 : IsRealCoeff c0 := isRealCoeff_coeffOf φ (ClassicalAux.integrable_of_continuous hφc)
    have hsum0 : Summable fun k => ‖c0 k‖ := summable_norm_of_memHs (m : ℝ) hmd c0 hc0
    have hφeq : toFun c0 = φ := toFun_coeffOf φ hφc hsum0
    have hnφ : sobolevNorm (m : ℝ) φ = PDE.hsNorm (m : ℝ) c0 := ClassicalPart.sobolevNorm_eq_hsNorm hφS
    -- the forward solution
    obtain ⟨hsol, hw, hb⟩ := hspecm D ν₀ T μ hA t ht c0 hc0
    have hreal := ClassicalPart.propagatorCoeff_real hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T μ hA t ht
      c0 hc0 hre0
    set F : ℝ → Coeff d := propagatorCoeff D μ (m : ℝ) t c0 with hFdef
    have hF0 : F 0 = c0 := by
      funext k
      rw [hsol.eq k 0 ⟨le_rfl, ht.1.le⟩]
      simp
    set B : ℝ := Real.exp (l1 * T) * PDE.hsNorm (m : ℝ) c0 with hBdef
    have hnn : 0 ≤ PDE.hsNorm (m : ℝ) c0 := Real.sqrt_nonneg _
    have hB0 : 0 ≤ B := by positivity
    have hBd : ∀ σ ∈ Set.Icc (0 : ℝ) t, PDE.hsNorm (m : ℝ) (F σ) ≤ B := by
      intro σ hσ
      refine (hb σ hσ).trans ?_
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hnn
      have h1 : R.lambdaM Cm ν₀ (thetaOrder d s) * σ ≤ l1 * σ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hσ.1
      have h2 : l1 * σ ≤ l1 * T := mul_le_mul_of_nonneg_left (hσ.2.trans htT) (abs_nonneg _)
      linarith
    have hτ' : t - s' ∈ Set.Icc (0 : ℝ) t := ⟨by linarith, by linarith [hr.trans hrs]⟩
    have hinc := hKinc D ν₀ T μ hA hν t ht c0 hc0 B hB0 hBd 0 ⟨le_rfl, ht.1.le⟩ (t - s') hτ'
    rw [← hFdef, hF0, hcast] at hinc
    obtain ⟨hincm, hincn⟩ := hinc
    set c1 : Coeff d := F (t - s') with hc1def
    have hc1m : MemHs (m : ℝ) c1 := hw.1 _ hτ'
    have hc1re : IsRealCoeff c1 := hreal _ hτ'
    have hsum1 : Summable fun k => ‖c1 k‖ := summable_norm_of_memHs (m : ℝ) hmd c1 hc1m
    set c : Coeff d := c1 - c0 with hcdef
    have hcm : MemHs (m : ℝ) c := memHs_sub hc1m hc0
    have hcre : IsRealCoeff c := by
      intro k
      simp only [hcdef, Pi.sub_apply, map_sub]
      rw [hc1re k, hre0 k]
    have hsumc : Summable fun k => ‖c k‖ := summable_norm_of_memHs (m : ℝ) hmd c hcm
    obtain ⟨hψS, hψSn⟩ := ClassicalPart.memSobolev_toFun (m := (m : ℝ)) hsumc hcm hcre
    have hψnorm : PDE.hsNorm (m2 : ℝ) c ≤ Real.sqrt (10 * K) * B * (t - s') := by
      unfold PDE.hsNorm
      refine Real.sqrt_le_iff.2 ⟨by have := sub_nonneg.2 hlt.le; positivity, ?_⟩
      have e : (Real.sqrt (10 * K) * B * (t - s')) ^ 2 = 10 * K * B ^ 2 * (t - s' - 0) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
      rw [e]; exact hincn
    obtain ⟨hψS2, hψS2n⟩ := ClassicalPart.memSobolev_toFun (m := (m2 : ℝ)) hsumc hincm hcre
    have hts : 0 ≤ t - s' := sub_nonneg.2 hlt.le
    have habs : |t - s'| = t - s' := abs_of_nonneg hts
    have hex2 : 1 ≤ Real.exp (l2 * T) := Real.one_le_exp (mul_nonneg (abs_nonneg _) hT0.le)
    have hX0 : 0 ≤ Real.sqrt (10 * K) * Real.exp (l1 * T) * (t - s') *
        PDE.hsNorm (m : ℝ) c0 := by positivity
    have hBeq : Real.sqrt (10 * K) * B * (t - s') =
        Real.sqrt (10 * K) * Real.exp (l1 * T) * (t - s') * PDE.hsNorm (m : ℝ) c0 := by
      rw [hBdef]; ring
    by_cases hs'0 : s' = 0
    · obtain rfl : s' = 0 := hs'0
      obtain rfl : r = 0 := le_antisymm (hrs) hr
      have hV1 : Torus.IsCk 1 D.V :=
        ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)) hA.hV.1
      have hμ1 : Torus.IsCk 1 (μ 0) :=
        ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
          (hA.hμ.smooth 0 ⟨le_rfl, hT0.le⟩)
      obtain ⟨C2, hC2⟩ := toFun_isCk_le (d := d) 2 (m : ℝ) hmd2
      have hφC2 : Torus.IsCk 2 φ := by
        have := (hC2 c0 hc0 hre0).1
        rw [hφeq] at this
        exact_mod_cast this
      have hU0 : propagator D μ 0 0 φ = φ :=
        mpi_propagator_zero D (ClassicalAux.convKernelFacts hd D) hV1 μ hμ1 hφC2
      have hU1 : propagator D μ 0 t φ = fun x => toFun c1 x :=
        ClassicalPart.propagator_eq_toFun hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ hφc hφS 0
          ⟨le_rfl, ht.1.le⟩
      have hfun : (fun x => propagator D μ 0 t φ x - propagator D μ 0 0 φ x) = toFun c := by
        funext x
        rw [hU1, hU0]
        have := mpi_toFun_sub c1 c0 hsum1 hsum0 x
        rw [hφeq] at this
        exact this.symm
      rw [hfun]
      refine ⟨hψS2, ?_⟩
      rw [hψS2n, hnφ, habs]
      calc PDE.hsNorm (m2 : ℝ) c ≤ Real.sqrt (10 * K) * B * (t - 0) := hψnorm
        _ = Real.sqrt (10 * K) * Real.exp (l1 * T) * (t - 0) * PDE.hsNorm (m : ℝ) c0 := hBeq
        _ ≤ Real.exp (l2 * T) * (Real.sqrt (10 * K) * Real.exp (l1 * T) * (t - 0) *
              PDE.hsNorm (m : ℝ) c0) := le_mul_of_one_le_left hX0 hex2
        _ = _ := by ring
    · have hs'pos : 0 < s' := lt_of_le_of_ne (hr.trans hrs) (Ne.symm hs'0)
      have hs'T : s' ∈ Set.Ioc (0 : ℝ) T := ⟨hs'pos, hst.trans htT⟩
      have hτr : s' - r ∈ Set.Icc (0 : ℝ) s' := ⟨by linarith, by linarith⟩
      have hsem := propagator_semigroup hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ hφc hφS r s'
        hr hrs hlt
      have hU1 : propagator D μ s' t φ = fun x => toFun c1 x :=
        ClassicalPart.propagator_eq_toFun hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φ hφc hφS s'
          ⟨hs'pos.le, hlt.le⟩
      obtain ⟨hg1S, -⟩ := ClassicalPart.memSobolev_toFun (m := (m : ℝ)) hsum1 hc1m hc1re
      have hg1c : Continuous (toFun c1) := continuous_toFun c1 hsum1
      have hψc : Continuous (toFun c) := continuous_toFun c hsumc
      have hP : ∀ g : Torus d → ℝ, Continuous g → MemSobolev (m : ℝ) g → ∀ x,
          propagator D μ r s' g x = toFun (propagatorCoeff D μ (m : ℝ) s' (coeffOf g) (s' - r)) x :=
        fun g hgc hgS x => congrFun (ClassicalPart.propagator_eq_toFun hd s hs0 hsd m hm R MB Λ VB
          D ν₀ T μ hA s' hs'T g hgc hgS r ⟨hr, hrs⟩) x
      obtain ⟨-, hw1, -⟩ := hspecm D ν₀ T μ hA s' hs'T c1 hc1m
      obtain ⟨-, hw0, -⟩ := hspecm D ν₀ T μ hA s' hs'T c0 hc0
      have hsp1 := summable_norm_of_memHs (m : ℝ) hmd _ (hw1.1 _ hτr)
      have hsp0 := summable_norm_of_memHs (m : ℝ) hmd _ (hw0.1 _ hτr)
      have hlin := mpi_pc_sub hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T μ hA s' hs'T c1 c0 hc1m hc0
        (s' - r) hτr
      have hcof1 : coeffOf (toFun c1) = c1 := coeffOf_toFun c1 hc1re hsum1
      have hcofc : coeffOf (toFun c) = c := coeffOf_toFun c hcre hsumc
      have hfun : (fun x => propagator D μ r t φ x - propagator D μ r s' φ x) =
          propagator D μ r s' (toFun c) := by
        funext x
        rw [hsem, hU1]
        have e1 := hP (toFun c1) hg1c hg1S x
        rw [hcof1] at e1
        have e0 := hP φ hφc hφS x
        have ec := hP (toFun c) hψc hψS x
        rw [hcofc, hcdef, hlin] at ec
        have hsub := mpi_toFun_sub (propagatorCoeff D μ (m : ℝ) s' c1 (s' - r))
          (propagatorCoeff D μ (m : ℝ) s' c0 (s' - r)) hsp1 hsp0 x
        rw [e1, e0, ec, hsub]
      rw [hfun]
      obtain ⟨-, -, h3, -⟩ := hcls D ν₀ T μ hA s' hs'T (toFun c) hψc hψS
      obtain ⟨hMem, hbd⟩ := h3 m2 hm2_1 hm2m r ⟨hr, hrs⟩
      refine ⟨hMem, ?_⟩
      rw [hψS2n] at hbd
      have hexp : Real.exp (R.lambdaM (Cs m2) ν₀ (thetaOrder d s) * (s' - r)) ≤ Real.exp (l2 * T) := by
        refine Real.exp_le_exp.2 ?_
        have h1 : R.lambdaM (Cs m2) ν₀ (thetaOrder d s) * (s' - r) ≤ l2 * (s' - r) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hτr.1
        have h2 : l2 * (s' - r) ≤ l2 * T :=
          mul_le_mul_of_nonneg_left (by linarith [hst.trans htT]) (abs_nonneg _)
        linarith
      rw [hnφ, habs]
      calc sobolevNorm (m2 : ℝ) (propagator D μ r s' (toFun c))
          ≤ Real.exp (R.lambdaM (Cs m2) ν₀ (thetaOrder d s) * (s' - r)) * PDE.hsNorm (m2 : ℝ) c := hbd
        _ ≤ Real.exp (l2 * T) * PDE.hsNorm (m2 : ℝ) c :=
            mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg _)
        _ ≤ Real.exp (l2 * T) * (Real.sqrt (10 * K) * B * (t - s')) :=
            mul_le_mul_of_nonneg_left hψnorm (Real.exp_pos _).le
        _ = Real.exp (l2 * T) * (Real.sqrt (10 * K) * Real.exp (l1 * T) * (t - s') *
              PDE.hsNorm (m : ℝ) c0) := by rw [hBeq]
        _ = _ := by ring


/-! ### The theorem -/

open HRS.Whole.AppendixALemmas (qT)

theorem path_propagator_increment_torus_proof (s : ℝ) (Rg : PDE.Regime)
    (ν₀ MB Λ T VB νbar : ℝ) :
    ∃ C : ℝ, ∀ {ι : Type} (D : ι → DynData d) (ρ : ι → ℝ → Torus d → ℝ),
      (∀ i, PDE.AdjointData s (Main.gammaIdx d + 2) Rg MB Λ VB (D i) ν₀ T (ρ i)) →
      (∀ i, (D i).invβ ≤ νbar) →
      ∀ i : ι, ∀ r s' t : ℝ, 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ φ : Torus d → ℝ,
        HRS.MemSobolev ((qT d : ℕ) : ℝ) φ → Continuous φ →
          HRS.MemSobolev ((qT d - 2 : ℕ) : ℝ) (fun x => propagator (D i) (ρ i) r t φ x -
              propagator (D i) (ρ i) r s' φ x) ∧
          HRS.sobolevNorm ((qT d - 2 : ℕ) : ℝ) (fun x => propagator (D i) (ρ i) r t φ x -
              propagator (D i) (ρ i) r s' φ x) ≤
            C * |t - s'| * HRS.sobolevNorm ((qT d : ℕ) : ℝ) φ := by
  by_cases hcase : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  · obtain ⟨hd, hs0, hsd⟩ := hcase
    have hm : mStar d ≤ Main.gammaIdx d + 2 := by
      unfold Main.gammaIdx; omega
    obtain ⟨C, hC⟩ := mpi_main hd s hs0 hsd (Main.gammaIdx d) hm Rg MB Λ VB νbar ν₀ T
    refine ⟨C, fun {ι} D ρ hA hν i r s' t hr hrs hst htT φ hφS hφc => ?_⟩
    have e2 : qT d - 2 = Main.gammaIdx d := by
      show Main.gammaIdx d + 2 - 2 = Main.gammaIdx d
      omega
    rw [e2]
    exact hC (D i) (ρ i) (hA i) (hν i) r s' t hr hrs hst htT φ hφS hφc
  · refine ⟨0, fun {ι} D ρ hA hν i r s' t hr hrs hst htT φ hφS hφc => ?_⟩
    exfalso
    apply hcase
    have h0 := (D i).hs0
    have h1 := (D i).hsd
    have hs := (hA i).hs
    rw [hs] at h0 h1
    refine ⟨?_, h0, h1⟩
    have : (0 : ℝ) < d := lt_of_le_of_lt h0 h1
    exact_mod_cast this

example := (@path_propagator_increment_torus_proof :
  type_of% @HRS.Whole.AppendixALemmas.path_propagator_increment_torus)

end HRS.MP.PropIncr
