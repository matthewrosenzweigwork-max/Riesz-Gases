import HRS.MS.Fp81S21TimeRep12
import HRS.MS.Fp81S21WeightedMomentsS5

/-! Physical weighted regularity of the two particle fields. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp
open HRS.MS.ProClosureS111

/-- A Gaussian upper bound supplies every polynomial reference moment needed
by the empirical fluctuation admissibility estimate. -/
theorem fp81s21_particle_reference_weight_integrable
    {d : ℕ} {ρ : Euc d → ℝ} {C₀ c₀ Pw : ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hc₀ : 0 < c₀) (hPw : 0 ≤ Pw)
    (hG : HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ) :
    Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC₀, hC⟩ := HRS.MS.R2Poly.s95_moment d C₀ c₀ hc₀
    (Pw := Pw / 2) (by linarith)
  have hpow : ∀ x : Euc d, (jbracket x ^ (Pw / 2)) ^ 2 = jbracket x ^ Pw := by
    intro x
    have hj : 0 < jbracket x := lt_of_lt_of_le zero_lt_one
      (HRS.MS.R2Poly.s95_one_le_jb x)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hj)]
    congr 1
    ring
  have hbound :
      (∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw)
        ∂(HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((jbracket x ^ (Pw / 2)) ^ 2)
          ∂(HRS.Whole.withDensityReal ρ) := by
            refine lintegral_congr fun x => ?_
            rw [hpow]
      _ ≤ ENNReal.ofReal C := hC ρ hρ hG.2
  have hjb : Continuous (fun x : Euc d => jbracket x) := by
    unfold jbracket
    fun_prop
  have hmeas : Measurable (fun x : Euc d => jbracket x ^ Pw) :=
    (hjb.rpow_const fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne').measurable
  have hnonneg : ∀ x : Euc d, 0 ≤ jbracket x ^ Pw := fun x =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc
    ∫⁻ x, ‖jbracket x ^ Pw‖ₑ ∂(HRS.Whole.withDensityReal ρ) =
        ∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw)
          ∂(HRS.Whole.withDensityReal ρ) := by
            refine lintegral_congr fun x => ?_
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    _ ≤ ENNReal.ofReal C := hbound
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Every nonnegative-time empirical and actual-law-centered quadratic
particle field is a physical `S102Z` functional. The hypotheses come from
the public uniform-density and actual-density producer for `p`. -/
theorem fp81s21_particle_fields_S102Z (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
        ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ u : ℝ, 0 ≤ u →
          ∀ ω : A.Ω,
            S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
              (fun f => fp81s21_particleEmpField R N A u ω f) ∧
            S102Z (2 * p.d + 8) ((p.d : ℝ) + 2)
              (fun f => fp81s21_particleQuadField R N A u ω f) := by
  obtain ⟨δ₀, hδ₀, hδ₀half, hUniform⟩ :=
    fp81s21_uniform_density_moments p
  refine ⟨δ₀, hδ₀, hδ₀half, ?_⟩
  intro δ hδ hδle R N hN A u hu
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀,
    hGaussian, hRound2, hReferenceMoment, hParticle⟩ :=
      hUniform δ hδ hδle R
  have hPw : 0 ≤ (p.d : ℝ) + 2 := by positivity
  have hd1 : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  have hrEmp : (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
  have hrQuad : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
  obtain ⟨c₁, hc₁, hker⟩ :=
    s102_comm_poly hd1 p.hs0 hPw (2 * p.d + 8) hrQuad
  obtain ⟨Agk, hAgk₀, hAgk⟩ :=
    s102_gk_int hd1 p.hs0 p.hs M C₀ c₀ hc₀ hPw
  obtain ⟨CE, hCE₀, henvelope⟩ :=
    s102_Env_bound p.hd p.hs0 p.hs M L C₀ c₀ p.β pinf K hc₀ p.hβ hpinf hPw
  let t : NNReal := u.toNNReal
  let μ : Measure (Euc p.d) := r26t3_mu R u
  have hRound := hRound2 u hu
  have hGauss := hGaussian u hu
  letI : IsProbabilityMeasure μ :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hRound.prob
  have hRef : Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2)) μ := by
    simpa [μ, r26t3_mu] using
      fp81s21_particle_reference_weight_integrable
        hRound.prob hc₀ hPw hGauss
  have hactual := (hParticle N hN A u hu).1
  change HRS.Whole.HasR2ActualDensity p.s p.β pinf K μ
    (A.P.map (fun ω => A.X t ω)) at hactual
  have hXmeas : Measurable (fun ω => A.X t ω) :=
    (A.strong (1 : ℝ)).adapted t
  obtain ⟨hgi, hgH, -⟩ := hAgk (R.ρ u) hRound.prob hRound.bdd hGauss.2
  obtain ⟨hEi, -⟩ := henvelope hRound hGauss.2 hN A.P
    (fun ω => A.X t ω) hXmeas hactual
  intro ω
  have hZη := s102_Z_fluct hd1 hPw (2 * p.d + 8) hrEmp
    (show 0 < N by omega) (A.X t ω) μ hRef (Real.sqrt N)
  have hZB := (s102_Z_quad (d := p.d) (s := p.s)
    (Pw := (p.d : ℝ) + 2) (μ := μ) (2 * p.d + 8) hrQuad hc₁ hker
    hgi hgH A.P (fun ω => A.X t ω) hXmeas hEi ω).1
  refine ⟨?_, ?_⟩
  · simpa [fp81s21_particleEmpField, r26t3_mu, HRS.Whole.r2EmpDistr, μ, t] using hZη
  · simpa [fp81s21_particleQuadField, r26t3_mu, HRS.Whole.r2QuadField,
      HRS.MS.R2Interp.s102_fld, μ, t] using hZB

#print axioms HRS.Fp81.S21.fp81s21_particle_reference_weight_integrable
#print axioms HRS.Fp81.S21.fp81s21_particle_fields_S102Z

end HRS.Fp81.S21
