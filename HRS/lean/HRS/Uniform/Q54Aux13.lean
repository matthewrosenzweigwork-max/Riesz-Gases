import HRS.Uniform.Q54Aux12

/-!
# Q54, part 13: Hölder continuity of the propagator at the diagonal (real index)

For a forward solution `F` with datum `φc ∈ H^{a+2}`: `‖F(τ) - φc‖²_{H^a} ≤ C τ e^{Aτ} ‖φc‖²_{H^{a+2}}`, uniformly in the
terminal time (energy inequality for `w = F - φc`, `w' = 𝓛w + 𝓛φc`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem forward_hold (s : ℝ) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ)
    (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (ν₀ νM : ℝ) (hν₀ : 0 < ν₀) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (D : DynData d) (T : ℝ) (μ : ℝ → Torus d → ℝ) (m : ℕ) (R : Regime)
      (MB' Λ VB ν₁ : ℝ), AdjointData s m R MB' Λ VB D ν₁ T μ →
      (∀ r ∈ Set.Icc (0 : ℝ) T, GenHyp d s K MB Bμ BV D (μ r)) → ν₀ ≤ D.invβ → D.invβ ≤ νM →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ (φc : Coeff d) (F : ℝ → Coeff d), IsForwardSolution D μ t φc F →
        ContinuousInHs (a + 2) F t → ContinuousInHs ((m : ℝ) + 2) F t →
        ∀ τ ∈ Set.Icc (0 : ℝ) t,
          hsNormSq a (F τ - φc) ≤ B * hsNormSq (a + 2) φc * τ * Real.exp (A * τ) := by
  obtain ⟨C₁, hC₁, hgen⟩ := gen_hs_bound s hsd K MB Bμ BV hMB hBμ hBV a hK
  obtain ⟨C₂, hC₂, hform⟩ := gen_form s hsd K MB Bμ BV hMB hBμ hBV a hK ν₀ hν₀
  refine ⟨2 * C₂ + 1, 2 * νM ^ 2 + C₁, by linarith, by positivity, ?_⟩
  intro D T μ m R MB' Λ VB ν₁ hA hG hν hνM t ht φc F hF hcA hcm τ hτ
  have hc10 : 0 ≤ 2 * D.invβ ^ 2 + C₁ := by positivity
  have hνle : 2 * D.invβ ^ 2 + C₁ ≤ 2 * νM ^ 2 + C₁ := by
    have h0 : 0 ≤ D.invβ := D.hβ
    nlinarith
  obtain ⟨B1, hB10, hB1⟩ := bounded_of_continuousInHs hcA
  -- the datum
  have hφc2 : MemHs (a + 2) φc := by
    have := hcA.1 0 ⟨le_rfl, ht.1.le⟩
    have h0 : F 0 = φc := by
      funext k
      have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
      simpa using this
    rwa [h0] at this
  have hφc1 : MemHs 1 φc := by
    have := hF.h1 0 ⟨le_rfl, ht.1.le⟩
    have h0 : F 0 = φc := by
      funext k
      have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
      simpa using this
    rwa [h0] at this
  set w : ℝ → Coeff d := fun σ => F σ - φc with hw
  have hwm : ∀ σ ∈ Set.Icc (0 : ℝ) t, MemHs (a + 2) (w σ) := fun σ hσ => memHs_sub (hcA.1 σ hσ) hφc2
  have hcw : ContinuousInHs (a + 2) w t := by
    refine ⟨hwm, fun τ₀ hτ₀ => ?_⟩
    have := hcA.2 τ₀ hτ₀
    refine this.congr fun σ => ?_
    simp only [hw]
    congr 1
    funext k; simp
  obtain ⟨Bw, hBw0, hBw⟩ := bounded_of_continuousInHs hcw
  -- derivative of the energy of `w`
  obtain ⟨Kb1, -, hgenσ⟩ : ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ σ ∈ Set.Icc (0 : ℝ) t,
      MemHs a (forwardGen D (μ (t - σ)) (F σ)) ∧
        hsNormSq a (forwardGen D (μ (t - σ)) (F σ)) ≤ (2 * D.invβ ^ 2 + C₁) * hsNormSq (a + 2) (F σ) := by
    refine ⟨0, le_rfl, fun σ hσ => ?_⟩
    exact hgen D (μ (t - σ)) (hG _ (tsub_mem_Icc ht hσ)) (F σ) (hcA.1 σ hσ) (hF.h1 σ hσ)
  have hderiv := hasDeriv_energy_abstract (t := t) a w (fun σ => forwardGen D (μ (t - σ)) (F σ))
    ((2 * D.invβ ^ 2 + C₁) * B1) Bw (by positivity) hBw0 hwm hBw (fun σ hσ => (hgenσ σ hσ).1)
    (fun σ hσ => (hgenσ σ hσ).2.trans (mul_le_mul_of_nonneg_left (hB1 σ hσ) hc10))
    (fun k => continuousOn_coord_of_continuousInHs hcw k)
    (fun k => gen_coord_continuousOn hA ht hcm k)
    (fun k => by
      have := hasDerivWithinAt_of_primitive (gen_coord_continuousOn hA ht hcm k) (φc k) (hF.eq k)
      intro σ hσ
      exact (this σ hσ).sub_const (φc k))
  -- the differential inequality
  set Aco : ℝ := 2 * C₂ + 1 with hAco
  set B₀sq : ℝ := (2 * D.invβ ^ 2 + C₁) * hsNormSq (a + 2) φc with hB₀
  have hB0' : 0 ≤ B₀sq := mul_nonneg hc10 (hsNormSq_nonnegE _ _)
  have hineq : ∀ σ ∈ Set.Icc (0 : ℝ) t,
      (hsInner a (forwardGen D (μ (t - σ)) (F σ)) (w σ)).re ≤
        Aco * ((1 / 2 : ℝ) * hsNormSq a (w σ)) + B₀sq / 2 := by
    intro σ hσ
    have hGσ := hG _ (tsub_mem_Icc ht hσ)
    obtain ⟨h0, hdr⟩ := genHyp_memHs0 hsd hGσ (by linarith [abs_nonneg a, Nat.cast_nonneg (α := ℝ) d]) hMB hBμ hBV
    have h1F := hF.h1 σ hσ
    have hwσ2 := hwm σ hσ
    have hwσ1 : MemHs 1 (w σ) := memHs_sub h1F hφc1
    -- linearity
    have hlinear : forwardGen D (μ (t - σ)) (w σ) =
        forwardGen D (μ (t - σ)) (F σ) - forwardGen D (μ (t - σ)) φc :=
      forwardGen_sub_H1 D _ h0 hdr h1F hφc1
    have hgF := hgen D (μ (t - σ)) hGσ (F σ) (hcA.1 σ hσ) h1F
    have hgφ := hgen D (μ (t - σ)) hGσ φc hφc2 hφc1
    have hwa : MemHs a (w σ) := hwσ2.mono (by linarith)
    have hsplit : hsInner a (forwardGen D (μ (t - σ)) (F σ)) (w σ) =
        hsInner a (forwardGen D (μ (t - σ)) (w σ)) (w σ) +
          hsInner a (forwardGen D (μ (t - σ)) φc) (w σ) := by
      have := hsInner_sub_left (r := a) hgF.1 hgφ.1 hwa
      rw [← hlinear] at this
      rw [this]; ring
    have hform' := hform D (μ (t - σ)) hGσ hν (w σ) hwσ2 hwσ1
    have hnn : 0 ≤ (ν₀ / 2) * hsNormSq (a + 1) (w σ) := mul_nonneg (by positivity) (hsNormSq_nonnegE _ _)
    have hX := hsNormSq_nonnegE a (w σ)
    have hcs := norm_hsInner_le hgφ.1 hwa
    have hre : (hsInner a (forwardGen D (μ (t - σ)) φc) (w σ)).re ≤
        Real.sqrt (hsNormSq a (forwardGen D (μ (t - σ)) φc)) * Real.sqrt (hsNormSq a (w σ)) :=
      (Complex.re_le_norm _).trans hcs
    have hφb : hsNormSq a (forwardGen D (μ (t - σ)) φc) ≤ B₀sq := hgφ.2
    have hsq : Real.sqrt (hsNormSq a (forwardGen D (μ (t - σ)) φc)) * Real.sqrt (hsNormSq a (w σ)) ≤
        hsNormSq a (w σ) / 2 + B₀sq / 2 := by
      have h1 : Real.sqrt (hsNormSq a (forwardGen D (μ (t - σ)) φc)) ≤ Real.sqrt B₀sq :=
        Real.sqrt_le_sqrt hφb
      have hB0 : 0 ≤ B₀sq := hB0'
      have h2 : Real.sqrt B₀sq * Real.sqrt (hsNormSq a (w σ)) ≤ hsNormSq a (w σ) / 2 + B₀sq / 2 := by
        nlinarith [sq_nonneg (Real.sqrt B₀sq - Real.sqrt (hsNormSq a (w σ))), Real.sq_sqrt hB0, Real.sq_sqrt hX]
      exact (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)).trans h2
    rw [hsplit, Complex.add_re]
    have hAco' : Aco * ((1 / 2 : ℝ) * hsNormSq a (w σ)) = (C₂ + 1 / 2) * hsNormSq a (w σ) := by
      rw [hAco]; ring
    rw [hAco']
    nlinarith
  -- Gronwall for z = y + B/A
  have hAco0 : 0 < Aco := by linarith
  have hz := gronwall_aux (t := t) (y := fun σ => (1 / 2 : ℝ) * hsNormSq a (w σ) + (B₀sq / 2) / Aco)
    (y' := fun σ => (hsInner a (forwardGen D (μ (t - σ)) (F σ)) (w σ)).re) Aco
    (fun σ hσ => (hderiv σ hσ).add_const _)
    (fun σ hσ => by
      have := hineq σ hσ
      have e : Aco * ((1 / 2 : ℝ) * hsNormSq a (w σ) + B₀sq / 2 / Aco) =
          Aco * ((1 / 2 : ℝ) * hsNormSq a (w σ)) + B₀sq / 2 := by
        field_simp
      rw [e]; exact this) τ hτ
  have hw0 : w 0 = 0 := by
    funext k
    have := hF.eq k 0 ⟨le_rfl, ht.1.le⟩
    simp [hw, this]
  have hy0 : hsNormSq a (w 0) = 0 := by rw [hw0]; simp [hsNormSq]
  simp only [hy0, mul_zero, zero_add] at hz
  -- conclude
  have hB0 : 0 ≤ B₀sq := hB0'
  have hexp : Real.exp (Aco * τ) - 1 ≤ Aco * τ * Real.exp (Aco * τ) := by
    have := Real.add_one_le_exp (-(Aco * τ))
    have h2 : Real.exp (-(Aco * τ)) * Real.exp (Aco * τ) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (Aco * τ), Real.exp_pos (-(Aco * τ))]
  have hdiv : (1 / 2 : ℝ) * hsNormSq a (w τ) ≤ (B₀sq / 2 / Aco) * (Real.exp (Aco * τ) - 1) := by
    have h1 : (1 / 2 : ℝ) * hsNormSq a (w τ) + B₀sq / 2 / Aco ≤ Real.exp (Aco * τ) * (B₀sq / 2 / Aco) := hz
    nlinarith
  have hmain : hsNormSq a (w τ) ≤ B₀sq * τ * Real.exp (Aco * τ) := by
    have : (B₀sq / 2 / Aco) * (Real.exp (Aco * τ) - 1) ≤ (B₀sq / 2 / Aco) * (Aco * τ * Real.exp (Aco * τ)) :=
      mul_le_mul_of_nonneg_left hexp (div_nonneg (div_nonneg hB0 (by norm_num)) hAco0.le)
    have e : (B₀sq / 2 / Aco) * (Aco * τ * Real.exp (Aco * τ)) = (B₀sq / 2) * τ * Real.exp (Aco * τ) := by
      field_simp
    nlinarith
  calc hsNormSq a (F τ - φc) = hsNormSq a (w τ) := rfl
    _ ≤ B₀sq * τ * Real.exp (Aco * τ) := hmain
    _ ≤ (2 * νM ^ 2 + C₁) * hsNormSq (a + 2) φc * τ * Real.exp (Aco * τ) := by
        have h1 : 0 ≤ hsNormSq (a + 2) φc := hsNormSq_nonnegE _ _
        have h2 : 0 ≤ τ * Real.exp (Aco * τ) := mul_nonneg hτ.1 (Real.exp_pos _).le
        rw [hB₀]
        nlinarith [mul_nonneg h1 h2]

end HRS.Uniform.Q54
