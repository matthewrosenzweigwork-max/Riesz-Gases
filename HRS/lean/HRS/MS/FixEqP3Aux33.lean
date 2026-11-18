import HRS.MS.FixEqP3Aux32
import HRS.Main.A33Aux1

/-!
# S5.7 `fixed_equation` (worker S57P), part 45: the coupling of the two linear fluctuation solutions and the cost bound

`s57p_core`: on `Ω × Ω₀` (`Ω₀` the probability space of an isonormal process on `L²([0,T]×ℝ^d;ℝ^d)`) the two solutions
`Y^N_t = I^N_t(η₀) + X^N_t`, `Y_t = I_t(η₀) + X_t` (same `η₀`, same `W`) satisfy
`‖sup_t ‖Y^N_t - Y_t‖‖_{L^p} ≤ 2 (E_init ‖η₀‖_{L^p(F₀)} + N^{1/4})`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau HRS.MS.U10

variable {d : ℕ} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν νN : ℝ}
  {c cN : ℝ → Euc d → Euc d} {ρ ρN : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ}
  {Ca CaN Cd CdN Cp1 Cp2 Dt : ℝ}

theorem s57p_core (hθ : IsUlCutoff θ) (hd : 1 ≤ d) (hT : 0 < T) (hP : (d : ℝ) < 2 * (((d : ℝ) + 3) / 2))
    (Pb : S57pPairBd θ T n K K s M Q ν νN c cN ρ ρN A Λc νbar m J Ca CaN Cd CdN Cp1 Cp2 Dt)
    {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hjets : ∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
      ‖iteratedFDeriv ℝ l (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (hJ : 3 * (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J) (hm : (J : ℝ) + d < m)
    {q qN τ aN a : ℝ} (hq : 0 ≤ q) (hqN : 0 ≤ qN) (hτ0 : 0 ≤ τ)
    (hτ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x : Euc d, ENNReal.ofReal |ρN r x - ρ r x| ≤ ENNReal.ofReal τ)
    {Mg : ℝ} (hM0 : 0 ≤ Mg)
    (hM : ∀ v : ℝ, 0 ≤ v → ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (Mg * v ^ 2))
    {p : ℝ} (hp : p = 1 ∨ p = 2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (η₀ : Ω → (Euc d → ℝ) → ℝ)
    (hη₀m : Measurable η₀) (hη₀ : ∀ᵐ ζ ∂P, IsBoundedLinearOnE n (((d : ℝ) + 3) / 2) (η₀ ζ))
    (hdual : ∀ᵐ ζ ∂P, dualNormE n (((d : ℝ) + 3) / 2) (η₀ ζ) < ⊤) :
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂) (h₂ : IsProbabilityMeasure P₂)
      (YN Y : ℝ → Ω × Ω₂ → OscDual d m),
      haveI := h₂
      IsLinearFluctuationSolutionW (P.prod P₂) (fixedEqCoeff s M Q νN cN ρN) m qN T (fun ζ f => aN * η₀ ζ.1 f) YN ∧
      IsLinearFluctuationSolutionW (P.prod P₂) (fixedEqCoeff s M Q ν c ρ) m q T (fun ζ f => a * η₀ ζ.1 f) Y ∧
      (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖YN t ζ - Y t ζ‖) ^ p ∂(P.prod P₂)) ^ (1 / p) ≤
        2 * (ENNReal.ofReal (((|aN - a| * CaN + |a| * (Cp1 * Dt)) *
            Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m))) * s57pC d n (((d : ℝ) + 3) / 2)) *
            (∫⁻ ζ, dualNormE n (((d : ℝ) + 3) / 2) (η₀ ζ) ^ p ∂P) ^ (1 / p) +
          (ENNReal.ofReal (s57pC0 T * (Mg * ((3 * s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt *
            ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m)) ^ 2)))) ^ (1 / (4 : ℝ))) := by
  have hT0 : 0 ≤ T := hT.le
  have hsum := s57p_summable_J hd hm
  obtain ⟨Ω₀, mΩ, Qm, hQ, W, hm1, h2, hl, hf, hi, hs1, hg⟩ := HRS.A33.a33_isonormal (Lp (Euc d) 2 (s57pμ d T))
  haveI := hQ
  have hI : Sb7Iso Qm W := ⟨hm1, h2, hl, hi⟩
  have hjoint : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (h : κ → Lp (Euc d) 2 (s57pμ d T)),
      Qm.map (fun w => (WithLp.toLp 2 (fun a => W (h a) w) : EuclideanSpace ℝ κ)) =
        multivariateGaussian 0 (Matrix.of fun a b => inner ℝ (h a) (h b)) := fun κ _ _ h => hg κ h
  obtain ⟨XN, hXNm, hXNc, hXNa, hXNlaw⟩ := s57p_fam_noise hθ hd Pb.FxN Pb.hbdN Pb.hCaN Pb.hCdN hCj hjets hJ hm hqN hT
    hI hs1 hjoint
  obtain ⟨X, hXm, hXc, hXa, hXlaw⟩ := s57p_fam_noise hθ hd Pb.Fx Pb.hbd Pb.hCa Pb.hCd hCj hjets hJ hm hq hT
    hI hs1 hjoint
  refine ⟨Ω₀, mΩ, Qm, hQ, fun t ζ => s57pI (fixedEqCoeff s M Q νN cN ρN) m aN (η₀ ζ.1) t + XN t ζ.2,
    fun t ζ => s57pI (fixedEqCoeff s M Q ν c ρ) m a (η₀ ζ.1) t + X t ζ.2, ?_, ?_, ?_⟩
  · exact s57p_fam_solution hθ hd hP Pb.FxN Pb.hbdN Pb.hCaN Pb.hCdN hCj hjets hJ hm aN qN P η₀ hη₀m hη₀ hdual Qm
      hXNm hXNc hXNlaw
  · exact s57p_fam_solution hθ hd hP Pb.Fx Pb.hbd Pb.hCa Pb.hCd hCj hjets hJ hm a q P η₀ hη₀m hη₀ hdual Qm
      hXm hXc hXlaw
  · set P' : ℝ := ((d : ℝ) + 3) / 2 with hP'
    have hgood : ∀ᵐ ζ ∂P, IsBoundedLinearOnE n P' (η₀ ζ) ∧ dualNormE n P' (η₀ ζ) < ⊤ := by
      filter_upwards [hη₀, hdual] with ζ h1 h2; exact ⟨h1, h2⟩
    have hgood2 : ∀ᵐ ζ ∂(P.prod Qm), IsBoundedLinearOnE n P' (η₀ ζ.1) ∧ dualNormE n P' (η₀ ζ.1) < ⊤ :=
      Measure.quasiMeasurePreserving_fst.ae hgood
    set E : ℝ≥0∞ := ENNReal.ofReal (((|aN - a| * CaN + |a| * (Cp1 * Dt)) *
      Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m))) * s57pC d n P') with hE
    set B : Ω₀ → ℝ≥0∞ := fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖XN t w - X t w‖ₑ with hB
    have hBm : Measurable B := s57p_sup_meas (fun t => (hXNm t).sub (hXm t)) (fun w => (hXNc w).sub (hXc w))
    have hBN := Pb.noise_sup hT hq hqN hτ0 hτ hsum hI hs1 hM0 hM hXNm hXm hXNc hXc hXNa hXa
    have e4 : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ 4 := fun x => by rw [← ENNReal.rpow_natCast]; norm_num
    have hBN' : ∫⁻ w, B w ^ (4 : ℝ) ∂Qm ≤ ENNReal.ofReal (s57pC0 T * (Mg * ((3 * s57pCz T q qN τ CaN CdN Cp1 Cp2 Dt *
        ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m)) ^ 2))) := by
      simp_rw [e4]; exact hBN
    have hF : ∀ᵐ ζ ∂(P.prod Qm), (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖(s57pI (fixedEqCoeff s M Q νN cN ρN) m aN (η₀ ζ.1) t + XN t ζ.2) -
        (s57pI (fixedEqCoeff s M Q ν c ρ) m a (η₀ ζ.1) t + X t ζ.2)‖) ≤
        E * dualNormE n P' (η₀ ζ.1) + B ζ.2 := by
      filter_upwards [hgood2] with ζ hζ
      refine iSup_le fun t => ?_
      have ht : (t : ℝ) ∈ Set.Icc (0 : ℝ) T := t.2
      have hi := s57p_init_diff hP hζ.1 hζ.2 Pb.hbd Pb.hbdN Pb.hCa Pb.hCaN Pb.hCp1 Pb.hDt Pb.hb hsum aN a ht Pb.hCd Pb.hCdN
      rw [add_sub_add_comm]
      refine (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans ?_
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      refine add_le_add ?_ ?_
      · refine (ENNReal.ofReal_le_ofReal hi).trans (le_of_eq ?_)
        have h0 : 0 ≤ ((|aN - a| * CaN + |a| * (Cp1 * Dt)) *
            Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m))) * s57pC d n P' :=
          mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) Pb.hCaN)
            (mul_nonneg (abs_nonneg _) (mul_nonneg Pb.hCp1 Pb.hDt))) (Real.sqrt_nonneg _)) (s57pC_nonneg d n P')
        rw [hE, ← ENNReal.ofReal_toReal hζ.2.ne, ← ENNReal.ofReal_mul h0]
        congr 1
        unfold s57pD
        ring
      · rw [ofReal_norm]
        exact le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖XN t ζ.2 - X t ζ.2‖ₑ) t
    exact s57p_lp_combine P Qm hp _ (fun x => dualNormE n P' (η₀ x)) B hBm ENNReal.ofReal_ne_top hBN' hF

end HRS.MS.FixEq
