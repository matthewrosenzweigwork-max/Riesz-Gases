import HRS.Main.A34Aux18

/-!
# Packet A34, helper 19: coupling of the two Gaussian noise fields through one isonormal process
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_coord_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := by
  unfold NegSobolev.coord
  exact lp.coeFn_sub (F : lp (fun _ : NonzeroLattice d => ℝ) 2) G ▸ rfl

theorem a34_field_couple (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (hJ2 : mStar d + d ≤ J)
    (Rg : Regime) (MB Λ VB ν₀ T : ℝ) (D₁ D₂ : DynData d) (ρ₁ ρ₂ : ℝ → Torus d → ℝ) (q₁ q₂ : ℝ)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hA₁ : AdjointData D₁.s J Rg MB Λ VB D₁ ν₀ T ρ₁)
    (hA₂ : AdjointData D₂.s J Rg MB Λ VB D₂ ν₀ T ρ₂) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G₁ G₂ : Ω → NegSobolev d (J : ℝ)),
      Measurable G₁ ∧ Measurable G₂ ∧ IsCenteredGaussian (P.map G₁) ∧
      IsCenteredGaussian (P.map G₂) ∧
      (∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
        ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂(P.map G₁) =
          noiseCovariance D₁ ρ₁ q₁ t φ ψ) ∧
      (∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
        ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂(P.map G₂) =
          noiseCovariance D₂ ρ₂ q₂ t φ ψ) ∧
      ∀ c : NonzeroLattice d → ℝ, Summable c →
        (∀ k : NonzeroLattice d, (Lattice.jp k.1 ^ (-(J : ℝ))) ^ 2 *
          ∫ p, ‖a34_h D₁ ρ₁ q₁ t (Torus.realMode k) p - a34_h D₂ ρ₂ q₂ t (Torus.realMode k) p‖ ^ 2
            ∂(a33_mu0 d T) ≤ c k) →
        Integrable (fun ω => ‖G₁ ω - G₂ ω‖ ^ 2) P ∧ ∫ ω, ‖G₁ ω - G₂ ω‖ ^ 2 ∂P ≤ ∑' k, c k := by
  classical
  obtain ⟨e⟩ := a33_exists_equiv hd
  set S₁ : A33Setup d := ⟨J, hJ, hJ2, hd, Rg, MB, Λ, VB, ν₀, D₁, T, ρ₁, hA₁⟩ with hS₁
  set S₂ : A33Setup d := ⟨J, hJ, hJ2, hd, Rg, MB, Λ, VB, ν₀, D₂, T, ρ₂, hA₂⟩ with hS₂
  obtain ⟨Ω, mΩ, P, hP, W, hm, h2, hl, hf, hi, hs1, hg⟩ :=
    a33_isonormal (Lp (Euc d) 2 (a33_mu0 d T))
  have hI : A33Iso P W := ⟨hm, h2, hl, hf, hi, hs1, hg⟩
  haveI := hP
  have hρ₁ : A33Rho T ρ₁ := S₁.rho
  have hρ₂ : A33Rho T ρ₂ := S₂.rho
  set Φ₁ := a34_Phi hρ₁ with hΦ₁
  set Φ₂ := a34_Phi hρ₂ with hΦ₂
  have hI₁ : A33Iso P (fun h : Lp (Euc d) 2 (a33_nu d S₁.T S₁.ρ) => W (Φ₁ h)) := a34_iso_comp hI Φ₁
  have hI₂ : A33Iso P (fun h : Lp (Euc d) 2 (a33_nu d S₂.T S₂.ρ) => W (Φ₂ h)) := a34_iso_comp hI Φ₂
  have ht₁ : t ∈ Set.Icc 0 S₁.T := ht
  have ht₂ : t ∈ Set.Icc 0 S₂.T := ht
  obtain ⟨hp₁, hc₁, hcov₁⟩ := a34_Gfield_law S₁ q₁ hq₁ _ hI₁ e ht₁
  obtain ⟨hp₂, hc₂, hcov₂⟩ := a34_Gfield_law S₂ q₂ hq₂ _ hI₂ e ht₂
  have hGm₁ := a33_Gfield_meas S₁ q₁ _ e hI₁ t
  have hGm₂ := a33_Gfield_meas S₂ q₂ _ e hI₂ t
  refine ⟨Ω, mΩ, P, hP, a33_Gfield S₁ q₁ _ t, a33_Gfield S₂ q₂ _ t, hGm₁, hGm₂, hc₁, hc₂,
    hcov₁, hcov₂, ?_⟩
  intro c hc hbd
  set W₁ : Lp (Euc d) 2 (a33_nu d S₁.T S₁.ρ) → Ω → ℝ := fun h => W (Φ₁ h) with hW₁
  set W₂ : Lp (Euc d) 2 (a33_nu d S₂.T S₂.ρ) → Ω → ℝ := fun h => W (Φ₂ h) with hW₂
  set X₁ : NonzeroLattice d → Ω → ℝ := fun k ω => a33_X S₁ q₁ W₁ t k ω with hX₁
  set X₂ : NonzeroLattice d → Ω → ℝ := fun k ω => a33_X S₂ q₂ W₂ t k ω with hX₂
  have hsmooth := fun k : NonzeroLattice d => HRS.FieldSingAux.isSmooth_realMode (d := d) k
  have hX1m : ∀ k, Measurable (X₁ k) := fun k => hI.meas _
  have hX2m : ∀ k, Measurable (X₂ k) := fun k => hI.meas _
  -- second moment of the difference of the coordinates
  have hsq : ∀ k, ∫ ω, (X₁ k ω - X₂ k ω) ^ 2 ∂P =
      ∫ p, ‖a34_h D₁ ρ₁ q₁ t (Torus.realMode k) p - a34_h D₂ ρ₂ q₂ t (Torus.realMode k) p‖ ^ 2
        ∂(a33_mu0 d T) := by
    intro k
    have h1 := A33Iso.sq_sub hI (Φ₁ (a33_vec S₁ q₁ t (Torus.realMode k)))
      (Φ₂ (a33_vec S₂ q₂ t (Torus.realMode k)))
    refine h1.trans ?_
    rw [a34_lp_norm_sq]
    refine integral_congr_ae ?_
    have e1 := a34_Phi_coe hρ₁ (a33_vec S₁ q₁ t (Torus.realMode k))
    have e2 := a34_Phi_coe hρ₂ (a33_vec S₂ q₂ t (Torus.realMode k))
    have v1 := S₁.vec_ae q₁ ht₁ (hsmooth k)
    have v2 := S₂.vec_ae q₂ ht₂ (hsmooth k)
    have w1 := a34_smul_ae hρ₁ v1
    have w2 := a34_smul_ae hρ₂ v2
    filter_upwards [Lp.coeFn_sub (Φ₁ (a33_vec S₁ q₁ t (Torus.realMode k)))
      (Φ₂ (a33_vec S₂ q₂ t (Torus.realMode k))), e1, e2, w1, w2] with p hs e1 e2 w1 w2
    rw [hs]
    simp only [Pi.sub_apply]
    rw [e1, e2, w1, w2]
    rfl
  have hs₁ := a33_ae_summable S₁ q₁ W₁ hI₁ ht₁
  have hs₂ := a33_ae_summable S₂ q₂ W₂ hI₂ ht₂
  set f : NonzeroLattice d → Ω → ℝ := fun k ω =>
    (Lattice.jp k.1 ^ (-(J : ℝ))) ^ 2 * (X₁ k ω - X₂ k ω) ^ 2 with hf
  have hpt : ∀ᵐ ω ∂P, ‖a33_Gfield S₁ q₁ W₁ t ω - a33_Gfield S₂ q₂ W₂ t ω‖ ^ 2 =
      ∑' k, f k ω ∧ Summable fun k => f k ω := by
    filter_upwards [hs₁, hs₂] with ω h1 h2
    have hmem1 : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(J : ℝ)) * X₁ k ω) 2 :=
      (Torus.memℓp_two_iff _).2 h1
    have hmem2 : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(J : ℝ)) * X₂ k ω) 2 :=
      (Torus.memℓp_two_iff _).2 h2
    have hc1 : ∀ k, NegSobolev.coord (a33_Gfield S₁ q₁ W₁ t ω) k =
        Lattice.jp k.1 ^ (-(J : ℝ)) * X₁ k ω := fun k =>
      HRS.Q41.q41_coord_ofSeq (m := (J : ℝ)) hmem1 k
    have hc2 : ∀ k, NegSobolev.coord (a33_Gfield S₂ q₂ W₂ t ω) k =
        Lattice.jp k.1 ^ (-(J : ℝ)) * X₂ k ω := fun k =>
      HRS.Q41.q41_coord_ofSeq (m := (J : ℝ)) hmem2 k
    obtain ⟨hsum, hn⟩ := NegSobolev.coord_sq (a33_Gfield S₁ q₁ W₁ t ω - a33_Gfield S₂ q₂ W₂ t ω)
    have hfe : ∀ k, f k ω = NegSobolev.coord (a33_Gfield S₁ q₁ W₁ t ω - a33_Gfield S₂ q₂ W₂ t ω) k ^ 2 := by
      intro k
      rw [a34_coord_sub, hc1, hc2]
      simp only [hf]
      ring
    simp_rw [hfe]
    exact ⟨hn, hsum⟩
  have hfm : ∀ k, Measurable (f k) := fun k =>
    measurable_const.mul (((hX1m k).sub (hX2m k)).pow_const 2)
  have hfi : ∀ k, Integrable (f k) P := fun k => by
    have := ((hI.memLp (Φ₁ (a33_vec S₁ q₁ t (Torus.realMode k)))).sub
      (hI.memLp (Φ₂ (a33_vec S₂ q₂ t (Torus.realMode k))))).integrable_sq
    exact this.const_mul _
  have hfnn : ∀ k ω, 0 ≤ f k ω := fun k ω => by positivity
  have hfk : ∀ k, ∫ ω, f k ω ∂P ≤ c k := fun k => by
    simp only [hf]
    rw [integral_const_mul, hsq k]
    exact hbd k
  have hcnn : ∀ k, 0 ≤ c k := fun k => le_trans (integral_nonneg (hfnn k)) (hfk k)
  have hg : Measurable fun ω => ‖a33_Gfield S₁ q₁ W₁ t ω - a33_Gfield S₂ q₂ W₂ t ω‖ ^ 2 :=
    ((hGm₁.sub hGm₂).norm).pow_const 2
  have hlint : ∫⁻ ω, ENNReal.ofReal (‖a33_Gfield S₁ q₁ W₁ t ω - a33_Gfield S₂ q₂ W₂ t ω‖ ^ 2) ∂P ≤
      ENNReal.ofReal (∑' k, c k) := by
    calc ∫⁻ ω, ENNReal.ofReal (‖a33_Gfield S₁ q₁ W₁ t ω - a33_Gfield S₂ q₂ W₂ t ω‖ ^ 2) ∂P
        = ∫⁻ ω, ∑' k, ENNReal.ofReal (f k ω) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hpt] with ω h
          rw [h.1, ENNReal.ofReal_tsum_of_nonneg (fun k => hfnn k ω) h.2]
      _ = ∑' k, ∫⁻ ω, ENNReal.ofReal (f k ω) ∂P :=
          lintegral_tsum fun k => (ENNReal.measurable_ofReal.comp (hfm k)).aemeasurable
      _ = ∑' k, ENNReal.ofReal (∫ ω, f k ω ∂P) := tsum_congr fun k =>
          (ofReal_integral_eq_lintegral_ofReal (hfi k) (Eventually.of_forall (hfnn k))).symm
      _ ≤ ∑' k, ENNReal.ofReal (c k) := ENNReal.tsum_le_tsum fun k =>
          ENNReal.ofReal_le_ofReal (hfk k)
      _ = ENNReal.ofReal (∑' k, c k) := (ENNReal.ofReal_tsum_of_nonneg hcnn hc).symm
  refine ⟨?_, ?_⟩
  · refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
      hg.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (tsum_nonneg hcnn) hlint

end HRS.A34
