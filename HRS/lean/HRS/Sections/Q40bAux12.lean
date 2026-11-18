import HRS.Sections.Sec5
import HRS.Equilibrium.Parametrix.PXFIDAuxD
import HRS.Sections.Q40bAux10
import HRS.Sections.Q40bAux11

/-!
# Packet Q40b, part 12: Proposition 5.14 (`criterion_comparison`)

Relocated proof (`Sec5.lean` cannot import the helper files): `criterion_comparison_proof` has the
verbatim statement of `HRS.criterion_comparison`, and the `example` at the end checks that the two
types agree.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS

variable {d : ℕ}

namespace Q40b

variable {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem q40b_adjoint_all (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {ρβ : Torus d → ℝ} (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hρS : Torus.IsSmooth ρβ) (hρpos : ∀ x, 0 < ρβ x) {j : ℕ} (hj : Even j)
    (hjd : (d : ℝ) / 2 + 4 < j) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ (Ca : Fin p → ℝ) (m : ℝ), (∀ a, 0 ≤ Ca a) ∧ 0 < m ∧
      (∀ a, ∀ τ : ℝ, 0 ≤ τ → ∃ F : ℝ → Torus d → ℝ,
        IsClassicalAdjointSolution htr.dyn ρ τ (φ a) F ∧
          ∀ r ∈ Set.Icc 0 τ, propagator htr.dyn ρ r τ (φ a) = F r) ∧
      (∀ a, ∀ τ : ℝ, 0 ≤ τ → ∀ r ∈ Set.Icc 0 τ, ∀ x,
        ‖Torus.grad (propagator htr.dyn ρ r τ (φ a)) x‖ ≤ Ca a * Real.exp (-m * (τ - r))) := by
  have H := fun a => q40b_adjoint hd htr hρβ hρS hρpos hj hjd (hφ a)
  choose C m0 hC0 hm0 hbd using fun a => (H a).2
  choose B hB using fun a => Parx.PXFID.exists_norm_grad_le_of_smooth (hφ a)
  have hS0 : 0 ≤ ∑ a, 1 / m0 a := Finset.sum_nonneg fun a _ => (one_div_pos.2 (hm0 a)).le
  set m : ℝ := 1 / (1 + ∑ a, 1 / m0 a) with hm
  have hmpos : 0 < m := one_div_pos.2 (by linarith)
  have hmle : ∀ a, m ≤ m0 a := by
    intro a
    have hS : 1 / m0 a ≤ ∑ b, 1 / m0 b :=
      Finset.single_le_sum (f := fun b => 1 / m0 b) (fun b _ => (one_div_pos.2 (hm0 b)).le)
        (Finset.mem_univ a)
    have h1 : 1 / (1 + ∑ b, 1 / m0 b) ≤ 1 / (1 / m0 a) :=
      one_div_le_one_div_of_le (one_div_pos.2 (hm0 a)) (by linarith)
    rwa [one_div_one_div] at h1
  refine ⟨fun a => max (C a) (B a), m, fun a => (hC0 a).trans (le_max_left _ _), hmpos,
    fun a τ hτ => (H a).1 τ hτ, ?_⟩
  intro a τ hτ r hr x
  rcases hτ.eq_or_lt with h0 | hpos
  · subst h0
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    subst hr0
    obtain ⟨F, hF, hFp⟩ := (H a).1 0 le_rfl
    have : propagator htr.dyn ρ 0 0 (φ a) = φ a := by
      rw [hFp 0 ⟨le_rfl, le_rfl⟩]; exact hF.terminal
    rw [this]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    exact (hB a x).trans (le_max_right _ _)
  · refine (hbd a τ hpos r hr x).trans ?_
    have h1 : Real.exp (-m0 a * (τ - r)) ≤ Real.exp (-m * (τ - r)) :=
      Real.exp_le_exp.2 (by nlinarith [hmle a, hr.2])
    exact mul_le_mul (le_max_left _ _) h1 (Real.exp_pos _).le ((hC0 a).trans (le_max_left _ _))

end Q40b

theorem criterion_comparison_proof_aem (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (j : ℕ) (hj : Even j) (hjd : (d : ℝ) / 2 + 4 < j) (p : ℕ)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) (C₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : ParticleSeq d,
      (∀ T : ℝ, 0 ≤ T → S.IsSolutionOn htr.dyn T) →
      (∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
          (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
        IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n)) →
      (∀ n, relEntropy ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤) →
      (∀ n, ∀ t : ℝ, 0 ≤ t →
        relEntropy ((S.P n).map (S.X n t.toNNReal))
              (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ t))) +
            relEntropy ((S.P n).map (S.X n t.toNNReal))
              (Measure.pi fun _ => withDensityReal (ρ t)) ≤
          ENNReal.ofReal (C₁ * entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
            (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))))) →
      Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) / ((n + 2 : ℕ) : ℝ))
        atTop (𝓝 0) →
      Tendsto (fun n : ℕ => criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n)) atTop (𝓝 0) →
      ∀ n : ℕ, ∀ t : Fin p → ℝ, (∀ a, 0 ≤ t a) →
        ∀ G : S.Ω n → EuclideanSpace ℝ (Fin p),
          law (S.P n) G = ProbabilityTheory.multivariateGaussian 0
            (noiseCovMatrix htr.dyn ρ β⁻¹ t φ) →
          AEMeasurable G (S.P n) →
          ProbabilityTheory.IndepFun (S.X₀ n) G (S.P n) →
          ENNReal.ofReal (smoothDist 2
              (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                zetaStat (S.P n) (S.X n) (t a) (φ a) ω : EuclideanSpace ℝ (Fin p)))
              (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
                zetaStat (S.P n) (S.X n) 0 (propagator htr.dyn ρ 0 (t a) (φ a)) ω + G ω a :
                  EuclideanSpace ℝ (Fin p)))) ≤
            ENNReal.ofReal C * (criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n) +
              ENNReal.ofReal (Real.sqrt (entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
                (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
                  ((n + 2 : ℕ) : ℝ)))) := by
  classical
  obtain ⟨Ca, m, hCa0, hm, hclass, hgrad⟩ :=
    Q40b.q40b_adjoint_all hd htr hρβ hρS hρpos hj hjd hφ
  set L : Fin p → ℝ := fun a => sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) (φ a)) with hL
  have hL0 : ∀ a, 0 ≤ L a := fun a => Real.sqrt_nonneg _
  have hβ : 0 < β := htr.hβ
  set K : ℝ := ∑ a, ∑ b, 2 * β⁻¹ * Ca a * Ca b / (2 * m) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    have := hCa0 a; have := hCa0 b; positivity
  set c₁ : ℝ := max C₁ 0 with hc₁
  have hc₁0 : 0 ≤ c₁ := le_max_right _ _
  set K' : ℝ := (1 / 2) * K * Real.sqrt (2 * (c₁ + 1)) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hLs : 0 ≤ ∑ a, (L a + 1) := Finset.sum_nonneg fun a _ => by linarith [hL0 a]
  refine ⟨∑ a, (L a + 1) + K' + 1, by linarith, ?_⟩
  intro S hsol hfilt hfin hent _ _ n t ht G hG hGae hind
  -- a measurable version of `G`
  set G' : S.Ω n → EuclideanSpace ℝ (Fin p) := hGae.mk G with hG'def
  have hGm : Measurable G' := hGae.measurable_mk
  have hGG : G =ᵐ[S.P n] G' := hGae.ae_eq_mk
  have hG' : law (S.P n) G' = ProbabilityTheory.multivariateGaussian 0
      (noiseCovMatrix htr.dyn ρ β⁻¹ t φ) := by
    rw [← hG]; exact (Measure.map_congr hGG).symm
  have hinit : ∀ᵐ ω ∂(S.P n), S.X n 0 ω = S.X₀ n ω := (hsol 0 le_rfl n).sol.init
  have hind' : ProbabilityTheory.IndepFun (S.X n 0) G' (S.P n) :=
    hind.congr (hinit.mono fun ω h => h.symm) hGG
  have hlawC : law (S.P n) (fun ω => (WithLp.toLp 2 fun a =>
      zetaStat (S.P n) (S.X n) 0 (propagator htr.dyn ρ 0 (t a) (φ a)) ω + G ω a :
        EuclideanSpace ℝ (Fin p))) =
      law (S.P n) (fun ω => (WithLp.toLp 2 fun a =>
      zetaStat (S.P n) (S.X n) 0 (propagator htr.dyn ρ 0 (t a) (φ a)) ω + G' ω a :
        EuclideanSpace ℝ (Fin p))) := by
    refine Measure.map_congr ?_
    filter_upwards [hGG] with ω hω
    simp only [hω]
  rw [hlawC]
  obtain ⟨ℱ, W', hfl⟩ := hfilt n
  -- the entropy bounds
  set Bn : ℝ := entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
    (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) with hBn
  have hB2 : 2 ≤ Bn := by
    have h1 : 1 ≤ ((n + 2 : ℕ) : ℝ) * deltaN d s (n + 2) :=
      one_le_mul_deltaN htr.hs0 (n + 2) (by omega)
    have h2 := ENNReal.toReal_nonneg (a := relEntropy ((S.P n).map (S.X₀ n))
      (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))))
    rw [hBn]; unfold entropyScale; linarith
  have hBn0 : 0 ≤ Bn := by linarith
  have hH₁ : 0 ≤ c₁ * Bn := mul_nonneg hc₁0 hBn0
  have hentB : ∀ r : ℝ, 0 ≤ r → relEntropy ((S.P n).map (S.X n r.toNNReal))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ r))) +
      relEntropy ((S.P n).map (S.X n r.toNNReal))
        (Measure.pi fun _ => withDensityReal (ρ r)) ≤ ENNReal.ofReal (c₁ * Bn) := by
    intro r hr
    refine (hent n r hr).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hBn0
  have hM := Q40b.q40b_master (P := S.P n) hd htr (by omega : 2 ≤ n + 2)
    (fun T hT => (hsol T hT n).sol) hfl hH₁ (fun r hr => le_trans le_self_add (hentB r hr))
    (fun r hr => le_trans le_add_self (hentB r hr)) t ht φ hφ Ca m hCa0 hm hclass hgrad
    G' hGm hG' hind'
  refine hM.trans ?_
  set r := criterionRemainder htr.dyn ρ ρβ j (S.P n) (S.X n) with hr
  set y := ENNReal.ofReal (Real.sqrt (Bn / ((n + 2 : ℕ) : ℝ))) with hy
  have h1 : ∑ a, ∫⁻ ω, ENNReal.ofReal |integratedRemainder htr.dyn ρ (S.P n) (S.X n) (t a) (φ a) ω|
      ∂(S.P n) ≤ ENNReal.ofReal (∑ a, (L a + 1)) * r := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by linarith [hL0 a]), Finset.sum_mul]
    exact Finset.sum_le_sum fun a _ =>
      Q40b.q40b_R_le hd htr (S.P n) (S.X n) hρβ hρS hρpos j (hφ a) (ht a)
  have h2 : ENNReal.ofReal ((1 / 2) * K * Real.sqrt (2 * (c₁ * Bn + Real.log 2) /
      ((n + 2 : ℕ) : ℝ))) ≤ ENNReal.ofReal K' * y := by
    rw [hy, ← ENNReal.ofReal_mul hK'0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hN0 : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    have hin : 2 * (c₁ * Bn + Real.log 2) / ((n + 2 : ℕ) : ℝ) ≤
        (2 * (c₁ + 1)) * (Bn / ((n + 2 : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hN0.le
      nlinarith
    have hsq := Real.sqrt_le_sqrt hin
    rw [Real.sqrt_mul (by positivity)] at hsq
    calc (1 / 2) * K * Real.sqrt (2 * (c₁ * Bn + Real.log 2) / ((n + 2 : ℕ) : ℝ))
        ≤ (1 / 2) * K * (Real.sqrt (2 * (c₁ + 1)) * Real.sqrt (Bn / ((n + 2 : ℕ) : ℝ))) := by
          gcongr
      _ = K' * Real.sqrt (Bn / ((n + 2 : ℕ) : ℝ)) := by rw [hK']; ring
  have hC1 : ENNReal.ofReal (∑ a, (L a + 1)) ≤ ENNReal.ofReal (∑ a, (L a + 1) + K' + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hC2 : ENNReal.ofReal K' ≤ ENNReal.ofReal (∑ a, (L a + 1) + K' + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  calc _ ≤ ENNReal.ofReal (∑ a, (L a + 1)) * r + ENNReal.ofReal K' * y := add_le_add h1 h2
    _ ≤ ENNReal.ofReal (∑ a, (L a + 1) + K' + 1) * r +
        ENNReal.ofReal (∑ a, (L a + 1) + K' + 1) * y := by gcongr
    _ = _ := (mul_add _ _ _).symm

end HRS
