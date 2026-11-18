import HRS.Sections.AdjKGlue

/-!
# ADJKA part 1: Lipschitz increment of the adjoint propagator at the diagonal (function level)

`adjka_lip_core`: abstract weighted-`ℓ²` Minkowski inequality for a coefficient integral.
`adjka_forward_lip`: `‖F(τ) - φ‖_{H^a} ≤ C τ ‖φ‖_{H^{a+2}}` for a forward solution.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.AdjK

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ}

theorem adjka_lip_core (a τ G : ℝ) (hτ : 0 ≤ τ) (hG : 0 ≤ G) (w : Coeff d) (g : ℝ → Coeff d)
    (hint : ∀ k, IntervalIntegrable (fun σ => g σ k) volume 0 τ)
    (hw : ∀ k, w k = ∫ σ in (0 : ℝ)..τ, g σ k)
    (hg : ∀ σ ∈ Set.Icc (0 : ℝ) τ, MemHs a (g σ) ∧ hsNormSq a (g σ) ≤ G ^ 2) :
    MemHs a w ∧ hsNormSq a w ≤ (τ * G) ^ 2 := by
  classical
  have hnn : ∀ k, 0 ≤ sobWeight a k * ‖w k‖ ^ 2 := fun k =>
    mul_nonneg (sobWeight_pos a k).le (sq_nonneg _)
  have hbd : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight a k * ‖w k‖ ^ 2 ≤ (τ * G) ^ 2 := by
    intro S
    set A := ∑ k ∈ S, sobWeight a k * ‖w k‖ ^ 2 with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => hnn k
    have hid : ((A : ℝ) : ℂ) = ∫ σ in (0 : ℝ)..τ,
        ∑ k ∈ S, ((sobWeight a k : ℝ) : ℂ) * (starRingEnd ℂ (w k) * g σ k) := by
      rw [intervalIntegral.integral_finset_sum]
      · rw [hA]; push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hw k,
          Complex.conj_mul']
      · intro k _
        exact ((hint k).const_mul _).const_mul _
    have hb : ∀ σ ∈ Set.uIoc (0 : ℝ) τ,
        ‖∑ k ∈ S, ((sobWeight a k : ℝ) : ℂ) * (starRingEnd ℂ (w k) * g σ k)‖ ≤ Real.sqrt A * G := by
      intro σ hσ
      rw [Set.uIoc_of_le hτ] at hσ
      obtain ⟨hm, hn⟩ := hg σ ⟨hσ.1.le, hσ.2⟩
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∀ k ∈ S, ‖((sobWeight a k : ℝ) : ℂ) * (starRingEnd ℂ (w k) * g σ k)‖ =
          (Real.sqrt (sobWeight a k) * ‖w k‖) * (Real.sqrt (sobWeight a k) * ‖g σ k‖) := by
        intro k _
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg (sobWeight_pos a k).le]
        have := Real.mul_self_sqrt (sobWeight_pos a k).le
        calc sobWeight a k * (‖w k‖ * ‖g σ k‖) =
            (Real.sqrt (sobWeight a k) * Real.sqrt (sobWeight a k)) * (‖w k‖ * ‖g σ k‖) := by
              rw [this]
          _ = _ := by ring
      rw [Finset.sum_congr rfl h1]
      refine (Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans ?_
      have e1 : ∑ k ∈ S, (Real.sqrt (sobWeight a k) * ‖w k‖) ^ 2 = A := by
        rw [hA]; refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_pow, Real.sq_sqrt (sobWeight_pos a k).le]
      have e2 : ∑ k ∈ S, (Real.sqrt (sobWeight a k) * ‖g σ k‖) ^ 2 ≤ G ^ 2 := by
        refine le_trans (le_of_eq ?_) ((sum_le_hsNormSq hm S).trans hn)
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_pow, Real.sq_sqrt (sobWeight_pos a k).le]
      rw [e1]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      calc Real.sqrt (∑ k ∈ S, (Real.sqrt (sobWeight a k) * ‖g σ k‖) ^ 2) ≤ Real.sqrt (G ^ 2) :=
            Real.sqrt_le_sqrt e2
        _ = G := Real.sqrt_sq hG
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [← hid, Complex.norm_real, Real.norm_of_nonneg hA0, sub_zero, abs_of_nonneg hτ] at hnorm
    have hsA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0
    rcases (Real.sqrt_nonneg A).eq_or_lt with h0 | hpos
    · have : A = 0 := by rw [← hsA, ← h0]; ring
      rw [this]; positivity
    · have h2 : Real.sqrt A ≤ τ * G := by
        have : Real.sqrt A * Real.sqrt A ≤ Real.sqrt A * (τ * G) := by
          calc Real.sqrt A * Real.sqrt A = A := hsA
            _ ≤ Real.sqrt A * G * τ := hnorm
            _ = Real.sqrt A * (τ * G) := by ring
        exact le_of_mul_le_mul_left this hpos
      calc A = Real.sqrt A ^ 2 := by rw [sq, hsA]
        _ ≤ (τ * G) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  exact ⟨summable_of_sum_le hnn hbd, Real.tsum_le_of_sum_le hnn hbd⟩


theorem adjka_forward_lip (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (hK2 : (d : ℝ) + |a + 2| + 4 ≤ K)
    (ν₀ νM : ℝ) (hν₀ : 0 < ν₀) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (D : DynData d) (T : ℝ) (μ : ℝ → Torus d → ℝ) (m : ℕ) (R : Regime)
      (MB' Λ VB ν₁ : ℝ), AdjointData s m R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → ν₀ ≤ D.invβ → D.invβ ≤ νM →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ (φc : Coeff d) (F : ℝ → Coeff d), IsForwardSolution D μ t φc F →
        ContinuousInHs (a + 2 + 2) F t → ContinuousInHs ((m : ℝ) + 2) F t →
        ∀ τ ∈ Set.Icc (0 : ℝ) t,
          hsNormSq a (F τ - φc) ≤ B * hsNormSq (a + 2) φc * τ ^ 2 * Real.exp (A * τ) := by
  obtain ⟨C₁, hC₁, hgen⟩ := gen_hs_bound s hsd K MB Bμ BV hMB hBμ hBV a hK
  obtain ⟨C₂, hC₂, hE⟩ := forward_energy_bound s hsd K MB Bμ BV hMB hBμ hBV (a + 2) hK2 ν₀ hν₀
  refine ⟨2 * C₂, 2 * νM ^ 2 + C₁, by positivity, by positivity, ?_⟩
  intro D T μ m R MB' Λ VB ν₁ hA hG hν hνM t ht φc F hF hc4 hcm τ hτ
  have hνle : 2 * D.invβ ^ 2 + C₁ ≤ 2 * νM ^ 2 + C₁ := by
    have h0 : 0 ≤ D.invβ := D.hβ
    nlinarith
  have hφ0 : F 0 = φc := by
    funext k
    have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
    simpa using this
  have hφc2 : MemHs (a + 2) φc := by
    have := (hc4.1 0 ⟨le_rfl, ht.1.le⟩).mono (show a + 2 ≤ a + 2 + 2 by linarith)
    rwa [hφ0] at this
  set N := hsNormSq (a + 2) φc with hN
  have hN0 : 0 ≤ N := hsNormSq_nonnegE _ _
  set c1 : ℝ := 2 * νM ^ 2 + C₁ with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hτt : τ ≤ t := hτ.2
  have hsub : ∀ σ ∈ Set.Icc (0 : ℝ) τ, σ ∈ Set.Icc (0 : ℝ) t := fun σ hσ => ⟨hσ.1, hσ.2.trans hτt⟩
  have hgσ : ∀ σ ∈ Set.Icc (0 : ℝ) τ,
      MemHs a (forwardGen D (μ (t - σ)) (F σ)) ∧
        hsNormSq a (forwardGen D (μ (t - σ)) (F σ)) ≤
          (Real.sqrt (c1 * Real.exp (2 * C₂ * τ) * N)) ^ 2 := by
    intro σ hσ
    have hσt := hsub σ hσ
    have hF2 : MemHs (a + 2) (F σ) := (hc4.1 σ hσt).mono (show a + 2 ≤ a + 2 + 2 by linarith)
    obtain ⟨h1, h2⟩ := hgen D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσt)) (F σ) hF2 (hF.h1 σ hσt)
    refine ⟨h1, ?_⟩
    have h3 := hE D T μ m R MB' Λ VB ν₁ hA hG hν t ht φc F hF hc4 hcm σ hσt
    rw [Real.sq_sqrt (by positivity)]
    calc hsNormSq a (forwardGen D (μ (t - σ)) (F σ)) ≤ (2 * D.invβ ^ 2 + C₁) * hsNormSq (a + 2) (F σ) := h2
      _ ≤ c1 * hsNormSq (a + 2) (F σ) :=
          mul_le_mul_of_nonneg_right hνle (hsNormSq_nonnegE _ _)
      _ ≤ c1 * (Real.exp (2 * C₂ * σ) * N) := mul_le_mul_of_nonneg_left h3 hc10
      _ ≤ c1 * (Real.exp (2 * C₂ * τ) * N) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hN0) hc10
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ.2 (by positivity))
      _ = _ := by ring
  have hint : ∀ k, IntervalIntegrable (fun σ => forwardGen D (μ (t - σ)) (F σ) k) volume 0 τ := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact (hF.integrable k).mono_set (Set.Icc_subset_Icc_right hτt)
  have hw : ∀ k, (F τ - φc) k = ∫ σ in (0 : ℝ)..τ, forwardGen D (μ (t - σ)) (F σ) k := by
    intro k
    have := hF.eq k τ hτ
    rw [Pi.sub_apply, this]; ring
  obtain ⟨-, hlip⟩ := adjka_lip_core a τ _ hτ.1 (Real.sqrt_nonneg _) (F τ - φc)
    (fun σ => forwardGen D (μ (t - σ)) (F σ)) hint hw hgσ
  refine hlip.trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring


theorem adjka_prop_lip (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K MB Bμ BV : ℝ)
    (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K)
    (hK2 : (d : ℝ) + |a + 2| + 4 ≤ K) (ν₀ νM : ℝ) (hν₀ : 0 < ν₀)
    (J : ℕ) (hJa : a + 2 + 2 < J) (hJ3 : (3 : ℝ) < J) (hJm : mStar d ≤ J) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (R : Regime) (MB' Λ VB ν₁ : ℝ) (D : DynData d) (T : ℝ)
      (μ : ℝ → Torus d → ℝ), AdjointData s J R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → ν₀ ≤ D.invβ → D.invβ ≤ νM →
      ∀ {φ : Torus d → ℝ}, Dom J φ → ∀ {u t : ℝ}, 0 ≤ u → u ≤ t → 0 < t → t ≤ T →
        MemSobolev a (fun x => propagator D μ u t φ x - φ x) ∧
          sobolevNorm a (fun x => propagator D μ u t φ x - φ x) ^ 2 ≤
            B * sobolevNorm (a + 2) φ ^ 2 * (t - u) ^ 2 * Real.exp (A * (t - u)) := by
  obtain ⟨A, B, hA0, hB0, hH⟩ := adjka_forward_lip s hsd K MB Bμ BV hMB hBμ hBV a hK hK2 ν₀ νM hν₀
  refine ⟨A, B, hA0, hB0, fun R MB' Λ VB ν₁ D T μ hA hG hν hνM φ hφ u t hu hut ht0 htT => ?_⟩
  have hJ1 : 1 ≤ J := by
    have : (3 : ℝ) < J := hJ3
    exact_mod_cast (by linarith : (1 : ℝ) ≤ J)
  have htm : t ∈ Set.Ioc 0 T := ⟨ht0, htT⟩
  have hutm : u ∈ Set.Icc 0 t := ⟨hu, hut⟩
  have hJd : (d : ℝ) / 2 < J := by
    have := mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJm
    linarith
  have hφa : MemSobolev a φ := MFAdjoint.memSobolev_mono_idx (m := J) hφ.2 (by linarith)
  have hφa2 : MemSobolev (a + 2) φ := MFAdjoint.memSobolev_mono_idx (m := J) hφ.2 (by linarith)
  obtain ⟨hprop, hpc⟩ := prop_facts hd s hs0 hsd J hJm R MB' Λ VB D ν₁ T μ hA htm hφ hutm
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd J hJ1 R MB' Λ VB
  have hφc : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  obtain ⟨hsol, hw, -⟩ := hspec D ν₁ T μ hA t htm (coeffOf φ) hφc
  set F := propagatorCoeff D μ J t (coeffOf φ) with hF
  have hc4 : ContinuousInHs (a + 2 + 2) F t := forward_strong_continuity (J : ℝ) t F hw (a + 2 + 2) hJa
  have hA1 : AdjointData s 1 R MB' Λ VB D ν₁ T μ := StabAux.adjointData_mono hJ1 hA
  have hcm : ContinuousInHs (((1 : ℕ) : ℝ) + 2) F t :=
    forward_strong_continuity (J : ℝ) t F hw _ (by push_cast; linarith)
  have hτ : t - u ∈ Set.Icc (0 : ℝ) t := ⟨by linarith, by linarith⟩
  have hen := hH D T μ 1 R MB' Λ VB ν₁ hA1 hG hν hνM t htm (coeffOf φ) F hsol hc4 hcm (t - u) hτ
  obtain ⟨hreal, hsum⟩ := pc_data hd s hs0 hsd J hJ1 hJd R MB' Λ VB D ν₁ T μ hA htm hφ hτ
  have hcoef : coeffOf (propagator D μ u t φ) = F (t - u) := by
    rw [hprop]; exact coeffOf_toFun _ hreal hsum
  have hcd : Continuous (fun x => propagator D μ u t φ x - φ x) := hpc.sub hφ.1
  have hcoefd : coeffOf (fun x => propagator D μ u t φ x - φ x) = fun k => F (t - u) k - coeffOf φ k := by
    have := coeffOf_lin hpc hφ.1 1 (-1)
    have e : (fun x => propagator D μ u t φ x - φ x) =
        fun x => (1 : ℝ) * propagator D μ u t φ x + (-1 : ℝ) * φ x := by funext x; ring
    rw [e, this, hcoef]
    funext k; push_cast; ring
  have hmemA2 : MemHs (a + 2) (F (t - u)) := (hc4.1 (t - u) hτ).mono (by linarith)
  have hmemφ2 : MemHs (a + 2) (coeffOf φ) := (hsNormSq_coeffOf (a + 2) φ hφa2).1
  have hmemd : MemHs a (F (t - u) - coeffOf φ) :=
    (memHs_sub hmemA2 hmemφ2).mono (by linarith)
  have hMS : MemSobolev a (fun x => propagator D μ u t φ x - φ x) :=
    memSobolev_of_memHs a _ (ClassicalAux.memLp_two_of_continuous hcd) (by
      rw [hcoefd]; exact hmemd)
  refine ⟨hMS, ?_⟩
  have e1 := (hsNormSq_coeffOf a _ hMS).2
  have e2 := (hsNormSq_coeffOf (a + 2) φ hφa2).2
  rw [hcoefd] at e1
  rw [← e1, ← e2]
  exact hen

end HRS.AdjK
