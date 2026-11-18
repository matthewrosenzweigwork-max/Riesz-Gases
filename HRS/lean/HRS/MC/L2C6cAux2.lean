import HRS.MC.L2C6cAux1

/-!
# Packet L2C-6c, helper 2: second moment of the coupled difference

From the centred Gaussian initial laws, the two linear fluctuation solutions and `IsSameNoise`
(with `p = p' = 1`), `η^t(φ) - ηs^t(φ) = A + B`, `A = Y₀(ψ) - Ys₀(ψ')`, `B = G - Gs` a difference of two
coordinates of the centred Gaussian noise vector.  Without independence:
`E[(η^t(φ) - ηs^t(φ))²] ≤ 4 Cov(ψ,ψ) + 4 Cov'(ψ',ψ') + 2 max(Σ₁₁ + Σ₂₂ - 2Σ₁₂, 0)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open HRS HRS.Sec7

namespace HRS.MC.L2C6c

variable {d : ℕ}

/-- The initial part `Y₀(ψ)` of a centred Gaussian initial field: `MemLp 2` with second moment `Cov ψ ψ`. -/
theorem l2c6c_init_part {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (m : ℝ)
    (Cov : (Torus d → ℝ) → (Torus d → ℝ) → ℝ) (Y₀ : Ω → NegSobolev d m)
    (hY : IsCenteredGaussianWithCov m (P.map Y₀) Cov) (hY₀ : AEMeasurable Y₀ P)
    {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    MemLp (fun ω => NegSobolev.eval (Y₀ ω) ψ) 2 P ∧
      ∫ ω, NegSobolev.eval (Y₀ ω) ψ ^ 2 ∂P = Cov ψ ψ := by
  have : IsGaussian (P.map Y₀) := hY.1.1
  have hcont := HRS.MC.L2C6Aux.l2c6_eval_continuous m hψ
  refine ⟨(HRS.MC.L2C6Aux.l2c6_eval_memLp m hψ (P.map Y₀)).comp_of_map hY₀, ?_⟩
  have h1 : ∫ ω, NegSobolev.eval (Y₀ ω) ψ ^ 2 ∂P = ∫ F, NegSobolev.eval F ψ ^ 2 ∂(P.map Y₀) :=
    (integral_map (f := fun F : NegSobolev d m => NegSobolev.eval F ψ ^ 2) hY₀
      (show Continuous fun F : NegSobolev d m => NegSobolev.eval F ψ ^ 2 from
        hcont.pow 2).aestronglyMeasurable).symm
  rw [h1, ← hY.2 ψ ψ hψ hψ]
  simp [sq]

theorem l2c6c_second_moment {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DynData d) (ρ ρ' : ℝ → Torus d → ℝ) (m : ℝ)
    (Cov Cov' : (Torus d → ℝ) → (Torus d → ℝ) → ℝ)
    (Y₀ Ys₀ : Ω → NegSobolev d m) (Y Ys : ℝ → Ω → NegSobolev d m)
    (hY : IsCenteredGaussianWithCov m (P.map Y₀) Cov)
    (hYs : IsCenteredGaussianWithCov m (P.map Ys₀) Cov')
    (hS : ∀ T : ℝ, IsLinearFluctuationSolution P D ρ m D.invβ T Y₀ Y)
    (hS' : ∀ T : ℝ, IsLinearFluctuationSolution P D ρ' m D.invβ T Ys₀ Ys)
    (hN : IsSameNoise D ρ ρ' m P Y₀ Ys₀ Y Ys)
    {t : ℝ} (ht : 0 ≤ t) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth (propagator D ρ 0 t φ)) (hψ' : Torus.IsSmooth (propagator D ρ' 0 t φ)) :
    MemLp (fun ω => NegSobolev.eval (Y t ω) φ - NegSobolev.eval (Ys t ω) φ) 2 P ∧
    ∫ ω, (NegSobolev.eval (Y t ω) φ - NegSobolev.eval (Ys t ω) φ) ^ 2 ∂P ≤
      4 * Cov (propagator D ρ 0 t φ) (propagator D ρ 0 t φ) +
      4 * Cov' (propagator D ρ' 0 t φ) (propagator D ρ' 0 t φ) +
      2 * max (crossNoiseCov D D.invβ ρ ρ t t φ φ + crossNoiseCov D D.invβ ρ' ρ' t t φ φ -
        2 * crossNoiseCov D D.invβ ρ ρ' t t φ φ) 0 := by
  set ψ := propagator D ρ 0 t φ with hψdef
  set ψ' := propagator D ρ' 0 t φ with hψ'def
  have hY₀ : AEMeasurable Y₀ P := by
    refine (((hS 0).meas 0).aemeasurable).congr ?_
    filter_upwards [(hS 0).init] with ω h using h
  have hYs₀ : AEMeasurable Ys₀ P := by
    refine (((hS' 0).meas 0).aemeasurable).congr ?_
    filter_upwards [(hS' 0).init] with ω h using h
  obtain ⟨hma, hEa⟩ := l2c6c_init_part P m Cov Y₀ hY hY₀ hψ
  obtain ⟨hmb, hEb⟩ := l2c6c_init_part P m Cov' Ys₀ hYs hYs₀ hψ'
  -- the noise vector
  obtain ⟨-, hlaw⟩ := hN 1 1 (fun _ => t) (fun _ => φ) (fun _ => t) (fun _ => φ) (fun _ => ht)
    (fun _ => ht) (fun _ => hφ) (fun _ => hφ)
  set G : Ω → EuclideanSpace ℝ PI := fun ω => WithLp.toLp 2 (Sum.elim
      (fun a : Fin 1 => noisePart D ρ Y₀ Y t φ ω) (fun b : Fin 1 => noisePart D ρ' Ys₀ Ys t φ ω)) with hG
  set S : Matrix PI PI ℝ := Matrix.of fun i j => match i, j with
      | Sum.inl a, Sum.inl b => crossNoiseCov D D.invβ ρ ρ t t φ φ
      | Sum.inl a, Sum.inr b => crossNoiseCov D D.invβ ρ ρ' t t φ φ
      | Sum.inr a, Sum.inl b => crossNoiseCov D D.invβ ρ' ρ t t φ φ
      | Sum.inr a, Sum.inr b => crossNoiseCov D D.invβ ρ' ρ' t t φ φ with hSdef
  have hlaw' : P.map G = multivariateGaussian 0 S := by
    convert hlaw using 2
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hcontφ := HRS.MC.L2C6Aux.l2c6_eval_continuous m hφ
  have hcont := HRS.MC.L2C6Aux.l2c6_eval_continuous m hψ
  have hcont' := HRS.MC.L2C6Aux.l2c6_eval_continuous m hψ'
  have hGm : AEMeasurable G P := by
    have h1 : AEMeasurable (fun ω => noisePart D ρ Y₀ Y t φ ω) P :=
      ((hcontφ.measurable.comp ((hS t).meas t)).aemeasurable).sub
        (hcont.measurable.comp_aemeasurable hY₀)
    have h2 : AEMeasurable (fun ω => noisePart D ρ' Ys₀ Ys t φ ω) P :=
      ((hcontφ.measurable.comp ((hS' t).meas t)).aemeasurable).sub
        (hcont'.measurable.comp_aemeasurable hYs₀)
    exact (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun i => by rcases i with i | i <;> assumption)
  obtain ⟨hmg, hEg⟩ := l2c6c_gauss_pair S
  rw [← hlaw'] at hmg hEg
  have hMg : MemLp (fun ω => G ω (Sum.inl 0) - G ω (Sum.inr 0)) 2 P := hmg.comp_of_map hGm
  have hEg' : ∫ ω, (G ω (Sum.inl 0) - G ω (Sum.inr 0)) ^ 2 ∂P ≤
      max (crossNoiseCov D D.invβ ρ ρ t t φ φ + crossNoiseCov D D.invβ ρ' ρ' t t φ φ -
        2 * crossNoiseCov D D.invβ ρ ρ' t t φ φ) 0 := by
    have h1 : ∫ ω, (G ω (Sum.inl 0) - G ω (Sum.inr 0)) ^ 2 ∂P =
        ∫ s : EuclideanSpace ℝ PI, (s (Sum.inl 0) - s (Sum.inr 0)) ^ 2 ∂(P.map G) := by
      rw [integral_map hGm (by fun_prop)]
    rw [h1]
    simpa [hSdef] using hEg
  -- decomposition
  set a : Ω → ℝ := fun ω => NegSobolev.eval (Y₀ ω) ψ with ha
  set b : Ω → ℝ := fun ω => NegSobolev.eval (Ys₀ ω) ψ' with hb
  set g : Ω → ℝ := fun ω => G ω (Sum.inl 0) - G ω (Sum.inr 0) with hg
  have hsum : ∀ ω, NegSobolev.eval (Y t ω) φ - NegSobolev.eval (Ys t ω) φ = (a ω - b ω) + g ω :=
    fun ω => by simp [ha, hb, hg, hG, noisePart]; ring
  have hfun : (fun ω => NegSobolev.eval (Y t ω) φ - NegSobolev.eval (Ys t ω) φ) =
      fun ω => (a ω - b ω) + g ω := funext hsum
  have hMA : MemLp (fun ω => a ω - b ω) 2 P := hma.sub hmb
  refine ⟨by rw [hfun]; exact hMA.add hMg, ?_⟩
  simp_rw [hsum]
  have hia := hma.integrable_sq
  have hib := hmb.integrable_sq
  have hig := hMg.integrable_sq
  have hiA := hMA.integrable_sq
  have step1 : ∫ ω, (a ω - b ω + g ω) ^ 2 ∂P ≤ 2 * ∫ ω, (a ω - b ω) ^ 2 ∂P + 2 * ∫ ω, g ω ^ 2 ∂P := by
    calc ∫ ω, (a ω - b ω + g ω) ^ 2 ∂P ≤ ∫ ω, (2 * (a ω - b ω) ^ 2 + 2 * g ω ^ 2) ∂P := by
          refine integral_mono ((hMA.add hMg).integrable_sq) ((hiA.const_mul 2).add (hig.const_mul 2))
            fun ω => ?_
          nlinarith [sq_nonneg (a ω - b ω - g ω)]
      _ = _ := by
          rw [integral_add (hiA.const_mul 2) (hig.const_mul 2), integral_const_mul, integral_const_mul]
  have step2 : ∫ ω, (a ω - b ω) ^ 2 ∂P ≤ 2 * ∫ ω, a ω ^ 2 ∂P + 2 * ∫ ω, b ω ^ 2 ∂P := by
    calc ∫ ω, (a ω - b ω) ^ 2 ∂P ≤ ∫ ω, (2 * a ω ^ 2 + 2 * b ω ^ 2) ∂P := by
          refine integral_mono hiA ((hia.const_mul 2).add (hib.const_mul 2)) fun ω => ?_
          nlinarith [sq_nonneg (a ω + b ω)]
      _ = _ := by
          rw [integral_add (hia.const_mul 2) (hib.const_mul 2), integral_const_mul, integral_const_mul]
  have hEa' : ∫ ω, a ω ^ 2 ∂P = Cov ψ ψ := hEa
  have hEb' : ∫ ω, b ω ^ 2 ∂P = Cov' ψ' ψ' := hEb
  have hEg'' : ∫ ω, g ω ^ 2 ∂P ≤ _ := hEg'
  linarith

end HRS.MC.L2C6c
