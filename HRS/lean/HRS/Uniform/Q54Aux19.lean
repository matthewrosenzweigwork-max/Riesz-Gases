import HRS.Uniform.Q54Aux14

/-!
# Q54, part 19: parabolic smoothing of the adjoint propagator over a unit time interval

For a forward solution `F` (datum `φc`) in `C([0,t]; H^{a+δ+2})`, `0 < δ ≤ 1`, `t ≥ 1`:
`‖F(1)‖²_{H^{a+δ}} ≤ M ‖φc‖²_{H^a}` with `M` independent of the coefficients subject to `GenHyp` (Lyapunov functional
`τ ‖F‖²_{a+δ} + λ ‖F‖²_a` and Gronwall).  Function level: `prop_smooth`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem forward_smooth (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hKa : (d : ℝ) + |a| + 4 ≤ K)
    (hKb : (d : ℝ) + |a + δ| + 4 ≤ K) (ν₀ : ℝ) (hν₀ : 0 < ν₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (D : DynData d) (T : ℝ) (μ : ℝ → Torus d → ℝ) (m : ℕ) (R : Regime)
      (MB' Λ VB ν₁ : ℝ), AdjointData s m R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → ν₀ ≤ D.invβ →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ (φc : Coeff d) (F : ℝ → Coeff d), IsForwardSolution D μ t φc F →
        ContinuousInHs (a + 2) F t → ContinuousInHs (a + δ + 2) F t →
        ContinuousInHs ((m : ℝ) + 2) F t → 1 ≤ t →
        hsNormSq (a + δ) (F 1) ≤ M * hsNormSq a φc := by
  obtain ⟨C₁a, hC₁a, hgenA⟩ := gen_hs_bound s hsd K MB Bμ BV hMB hBμ hBV a hKa
  obtain ⟨C₁b, hC₁b, hgenB⟩ := gen_hs_bound s hsd K MB Bμ BV hMB hBμ hBV (a + δ) hKb
  obtain ⟨Ca, hCa, hformA⟩ := gen_form s hsd K MB Bμ BV hMB hBμ hBV a hKa ν₀ hν₀
  obtain ⟨Cb, hCb, hformB⟩ := gen_form s hsd K MB Bμ BV hMB hBμ hBV (a + δ) hKb ν₀ hν₀
  set lam : ℝ := (1 + 2 * Cb) / ν₀ with hlam
  have hlam0 : 0 ≤ lam := by positivity
  refine ⟨Real.exp (2 * Ca) * lam, by positivity, ?_⟩
  intro D T μ m R MB' Λ VB ν₁ hA hG hν t ht φc F hF hcA hcB hcm ht1
  obtain ⟨BA, hBA0, hBA⟩ := bounded_of_continuousInHs hcA
  obtain ⟨BB, hBB0, hBB⟩ := bounded_of_continuousInHs hcB
  set c1a : ℝ := 2 * D.invβ ^ 2 + C₁a with hc1a
  set c1b : ℝ := 2 * D.invβ ^ 2 + C₁b with hc1b
  have hc1a0 : 0 ≤ c1a := by positivity
  have hc1b0 : 0 ≤ c1b := by positivity
  have hgσA : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs a (forwardGen D (μ (t - σ)) (F σ)) ∧
        hsNormSq a (forwardGen D (μ (t - σ)) (F σ)) ≤ c1a * hsNormSq (a + 2) (F σ) := by
    intro σ hσ
    exact hgenA D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσ)) (F σ) (hcA.1 σ hσ) (hF.h1 σ hσ)
  have hgσB : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs (a + δ) (forwardGen D (μ (t - σ)) (F σ)) ∧
        hsNormSq (a + δ) (forwardGen D (μ (t - σ)) (F σ)) ≤ c1b * hsNormSq (a + δ + 2) (F σ) := by
    intro σ hσ
    exact hgenB D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσ)) (F σ) (hcB.1 σ hσ) (hF.h1 σ hσ)
  have hcoordD : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt (fun τ => F τ k) (forwardGen D (μ (t - τ)) (F τ) k) (Set.Icc 0 t) τ :=
    fun k => hasDerivWithinAt_of_primitive (gen_coord_continuousOn hA ht hcm k) (φc k) (hF.eq k)
  have hderivA := hasDeriv_energy_abstract (t := t) a F (fun σ => forwardGen D (μ (t - σ)) (F σ))
    (c1a * BA) BA (by positivity) hBA0 hcA.1 hBA (fun σ hσ => (hgσA σ hσ).1)
    (fun σ hσ => (hgσA σ hσ).2.trans (mul_le_mul_of_nonneg_left (hBA σ hσ) hc1a0))
    (fun k => continuousOn_coord_of_continuousInHs hcA k)
    (fun k => gen_coord_continuousOn hA ht hcm k) hcoordD
  have hderivB := hasDeriv_energy_abstract (t := t) (a + δ) F
    (fun σ => forwardGen D (μ (t - σ)) (F σ))
    (c1b * BB) BB (by positivity) hBB0 hcB.1 hBB (fun σ hσ => (hgσB σ hσ).1)
    (fun σ hσ => (hgσB σ hσ).2.trans (mul_le_mul_of_nonneg_left (hBB σ hσ) hc1b0))
    (fun k => continuousOn_coord_of_continuousInHs hcB k)
    (fun k => gen_coord_continuousOn hA ht hcm k) hcoordD
  -- the two differential inequalities
  have hineqY : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      (hsInner a (forwardGen D (μ (t - σ)) (F σ)) (F σ)).re ≤
        2 * Ca * ((1 / 2 : ℝ) * hsNormSq a (F σ)) - ν₀ * ((1 / 2 : ℝ) * hsNormSq (a + δ) (F σ)) := by
    intro σ hσ
    have h1 := hformA D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσ)) hν (F σ)
      (hcA.1 σ hσ) (hF.h1 σ hσ)
    have hmem : MemHs (a + 1) (F σ) := (hcB.1 σ hσ).mono (by linarith)
    have h2 : hsNormSq (a + δ) (F σ) ≤ hsNormSq (a + 1) (F σ) :=
      MFApriori.hsNormSq_mono' (by linarith) hmem
    nlinarith
  have hineqZ : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      (hsInner (a + δ) (forwardGen D (μ (t - σ)) (F σ)) (F σ)).re ≤
        2 * Cb * ((1 / 2 : ℝ) * hsNormSq (a + δ) (F σ)) := by
    intro σ hσ
    have h1 := hformB D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσ)) hν (F σ)
      (hcB.1 σ hσ) (hF.h1 σ hσ)
    have h2 : 0 ≤ (ν₀ / 2) * hsNormSq (a + δ + 1) (F σ) :=
      mul_nonneg (by positivity) (hsNormSq_nonnegE _ _)
    nlinarith
  -- the Lyapunov functional on `[0,1]`
  have ht1' : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc 0 t := Set.Icc_subset_Icc_right ht1
  set Y : ℝ → ℝ := fun τ => (1 / 2 : ℝ) * hsNormSq a (F τ) with hY
  set Z : ℝ → ℝ := fun τ => (1 / 2 : ℝ) * hsNormSq (a + δ) (F τ) with hZ
  set Y' : ℝ → ℝ := fun τ => (hsInner a (forwardGen D (μ (t - τ)) (F τ)) (F τ)).re with hY'
  set Z' : ℝ → ℝ := fun τ => (hsInner (a + δ) (forwardGen D (μ (t - τ)) (F τ)) (F τ)).re with hZ'
  have hY0 : ∀ τ, 0 ≤ Y τ := fun τ => mul_nonneg (by norm_num) (hsNormSq_nonnegE _ _)
  have hZ0 : ∀ τ, 0 ≤ Z τ := fun τ => mul_nonneg (by norm_num) (hsNormSq_nonnegE _ _)
  have hW := gronwall_aux (t := 1) (y := fun τ => τ * Z τ + lam * Y τ)
    (y' := fun τ => Z τ + τ * Z' τ + lam * Y' τ) (2 * Ca)
    (fun τ hτ => by
      have h1 : HasDerivWithinAt (fun τ => τ * Z τ) (1 * Z τ + τ * Z' τ) (Set.Icc 0 1) τ :=
        (hasDerivWithinAt_id τ _).mul ((hderivB τ (ht1' hτ)).mono ht1')
      have h2 : HasDerivWithinAt (fun τ => lam * Y τ) (lam * Y' τ) (Set.Icc 0 1) τ :=
        ((hderivA τ (ht1' hτ)).mono ht1').const_mul lam
      have := h1.add h2
      convert this using 1
      ring)
    (fun τ hτ => by
      have hτ' := ht1' hτ
      have hy := hineqY τ hτ'
      have hz := hineqZ τ hτ'
      have hlamν : lam * ν₀ = 1 + 2 * Cb := by rw [hlam]; field_simp
      have hYτ := hY0 τ
      have hZτ := hZ0 τ
      have hτ0 := hτ.1
      have hτ1 := hτ.2
      have hz' : τ * Z' τ ≤ τ * (2 * Cb * Z τ) := mul_le_mul_of_nonneg_left hz hτ0
      have hy' : lam * Y' τ ≤ lam * (2 * Ca * Y τ - ν₀ * Z τ) := mul_le_mul_of_nonneg_left hy hlam0
      have e1 : lam * (2 * Ca * Y τ - ν₀ * Z τ) = 2 * Ca * (lam * Y τ) - (1 + 2 * Cb) * Z τ := by
        rw [← hlamν]; ring
      have hCbZ : 0 ≤ 2 * Cb * (1 - τ) * Z τ := by
        have : 0 ≤ 1 - τ := by linarith
        positivity
      have hCaτ : 0 ≤ 2 * Ca * (τ * Z τ) := by positivity
      show Z τ + τ * Z' τ + lam * Y' τ ≤ 2 * Ca * (τ * Z τ + lam * Y τ)
      nlinarith)
    1 ⟨zero_le_one, le_rfl⟩
  have h0 : F 0 = φc := by
    funext k
    have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
    simpa using this
  simp only [mul_zero, zero_add, one_mul, Real.exp_zero, mul_one] at hW
  have hW' : Z 1 + lam * Y 1 ≤ Real.exp (2 * Ca) * (lam * Y 0) := by
    simpa [mul_one, zero_mul, zero_add] using hW
  have hY1 := hY0 1
  have hlY : 0 ≤ lam * Y 1 := mul_nonneg hlam0 hY1
  have hZ1 : Z 1 ≤ Real.exp (2 * Ca) * (lam * Y 0) := by linarith
  have hY0e : Y 0 = (1 / 2 : ℝ) * hsNormSq a φc := by simp only [hY, h0]
  have : (1 / 2 : ℝ) * hsNormSq (a + δ) (F 1) ≤
      Real.exp (2 * Ca) * (lam * ((1 / 2 : ℝ) * hsNormSq a φc)) := by
    have := hZ1
    simp only [hZ] at this
    rwa [hY0e] at this
  nlinarith

theorem prop_smooth (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB)
    (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV) (a δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hKa : (d : ℝ) + |a| + 4 ≤ K) (hKb : (d : ℝ) + |a + δ| + 4 ≤ K) (ν₀ : ℝ) (hν₀ : 0 < ν₀)
    (J : ℕ) (hJa : a + δ + 2 < J) (hJ3 : (3 : ℝ) < J) (hJm : mStar d ≤ J) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : Regime) (MB' Λ VB ν₁ : ℝ) (D : DynData d) (T : ℝ)
      (μ : ℝ → Torus d → ℝ), AdjointData s J R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → ν₀ ≤ D.invβ →
      ∀ {φ : Torus d → ℝ}, Dom J φ → ∀ {u : ℝ}, 0 ≤ u → u + 1 ≤ T →
        MemSobolev (a + δ) (propagator D μ u (u + 1) φ) ∧
          sobolevNorm (a + δ) (propagator D μ u (u + 1) φ) ≤ M * sobolevNorm a φ := by
  obtain ⟨M, hM0, hM⟩ := forward_smooth s hsd K MB Bμ BV hMB hBμ hBV a δ hδ0 hδ1 hKa hKb ν₀ hν₀
  refine ⟨Real.sqrt M, Real.sqrt_nonneg _, fun R MB' Λ VB ν₁ D T μ hA hG hν φ hφ u hu huT => ?_⟩
  set t : ℝ := u + 1 with ht
  have hJ1 : 1 ≤ J := by
    have : (3 : ℝ) < J := hJ3
    exact_mod_cast (by linarith : (1 : ℝ) ≤ J)
  have ht0 : 0 < t := by rw [ht]; linarith
  have htm : t ∈ Set.Ioc 0 T := ⟨ht0, huT⟩
  have hutm : u ∈ Set.Icc 0 t := ⟨hu, by rw [ht]; linarith⟩
  have hJd : (d : ℝ) / 2 < J := by
    have := mStar_gt d
    have : (mStar d : ℝ) ≤ J := by exact_mod_cast hJm
    linarith
  have hφa : MemSobolev a φ := MFAdjoint.memSobolev_mono_idx (m := J) hφ.2 (by
    have : a ≤ a + δ := by linarith
    linarith)
  obtain ⟨hprop, hpc⟩ := prop_facts hd s hs0 hsd J hJm R MB' Λ VB D ν₁ T μ hA htm hφ hutm
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd J hJ1 R MB' Λ VB
  have hφc : MemHs (J : ℝ) (coeffOf φ) := (hsNormSq_coeffOf (J : ℝ) φ hφ.2).1
  obtain ⟨hsol, hw, -⟩ := hspec D ν₁ T μ hA t htm (coeffOf φ) hφc
  set F := propagatorCoeff D μ J t (coeffOf φ) with hF
  have hcA : ContinuousInHs (a + 2) F t :=
    forward_strong_continuity (J : ℝ) t F hw (a + 2) (by linarith)
  have hcB : ContinuousInHs (a + δ + 2) F t := forward_strong_continuity (J : ℝ) t F hw _ hJa
  have hA1 : AdjointData s 1 R MB' Λ VB D ν₁ T μ := StabAux.adjointData_mono hJ1 hA
  have hcm : ContinuousInHs (((1 : ℕ) : ℝ) + 2) F t :=
    forward_strong_continuity (J : ℝ) t F hw _ (by push_cast; linarith)
  have hen := hM D T μ 1 R MB' Λ VB ν₁ hA1 hG hν t htm (coeffOf φ) F hsol hcA hcB hcm (by rw [ht]; linarith)
  obtain ⟨hreal, hsum⟩ := pc_data hd s hs0 hsd J hJ1 hJd R MB' Λ VB D ν₁ T μ hA htm hφ
    (τ := t - u) ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
  have h1 : t - u = 1 := by rw [ht]; ring
  have hcoef : coeffOf (propagator D μ u t φ) = F (t - u) := by
    rw [hprop]; exact coeffOf_toFun _ hreal hsum
  have hmemB : MemHs (a + δ) (F (t - u)) := by
    refine (hcB.1 (t - u) ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩).mono (by linarith)
  have hMS : MemSobolev (a + δ) (propagator D μ u t φ) :=
    memSobolev_of_memHs (a + δ) _ (ClassicalAux.memLp_two_of_continuous hpc) (by rw [hcoef]; exact hmemB)
  refine ⟨hMS, ?_⟩
  have e1 := (hsNormSq_coeffOf (a + δ) _ hMS).2
  have e2 := (hsNormSq_coeffOf a φ hφa).2
  rw [hcoef, h1] at e1
  have hsq : sobolevNorm (a + δ) (propagator D μ u t φ) ^ 2 ≤ (Real.sqrt M * sobolevNorm a φ) ^ 2 := by
    rw [← e1, mul_pow, Real.sq_sqrt hM0, ← e2]
    exact hen
  exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end HRS.Uniform.Q54
