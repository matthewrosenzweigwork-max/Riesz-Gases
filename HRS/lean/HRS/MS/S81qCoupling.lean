import HRS.MS.S81pSpectral

/-!
# S8.1 (worker S81Q): the old-block producer with the polar data exported

`S81QCouplingClaim` is `S81PCouplingClaim` with the index type and Hilbert basis fixed to `ℕ` and `S45.s45_seqBasis`, and with the extra conclusions
(from `s81p_polar_ext`): progressive measurability of `(r,ω') ↦ ⟨S_r(π ω') x, y⟩` for `ℱ'`, `IsHSIntegrand` of the killed polar integrand, independence of the
driving Brownian path from `ℱ 0`, and measurability of `r ↦ ⟨Sb_r x, y⟩`.  The proof is the proof of `s81p_coupling_claim` (copied; it only destructures more
of the output of `s81p_polar_ext`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.S81Q

open HRS HRS.Whole HRS.MS.Spec

/-- The coupling conjuncts of `HRS.Whole.spectral_space` for a fixed `τ` (verbatim). -/
def S81QCouplingClaim (d : ℕ) (a β : ℝ) (ρβ : Euc d → ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (τ : ℝ) :
    Prop :=
      ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ ℱ : Filtration ℝ mΩ,
        IsCylindricalBrownian P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) →
        (∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) →
        let Φ : ℝ → Ω → (Fin N × Fin d) → SeqL2 := fun r z ia =>
          Real.sqrt (2 / (N * β)) • SeqL2.ofSeq (fun l =>
            Real.exp (-(τ * om l) / 2) * gradient (e l) (X (Real.toNNReal r) z ia.1) ia.2)
        (∀ᵐ x ∂(withDensityReal ρβ), ∀ i : Fin d, Memℓp (fun l => Real.exp (-(τ * om l) / 2) *
          gradient (e l) x i) 2) ∧
        (∀ T : ℝ, IsHSIntegrand P ℱ T Φ) ∧
        ∀ T : ℝ, 0 ≤ T → ∀ M : ℝ → Ω → SeqL2,
          IsHilbertItoIntegral P ℱ (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) Φ M →
          ∃ (Cdet : ℝ → SeqL2 →L[ℝ] SeqL2 →L[ℝ] ℝ),
            (∀ r ∈ Set.Icc 0 T, ∀ u v, Cdet r u v =
              ∑' l, 2 * β⁻¹ * om l * Real.exp (-τ * om l) * SeqL2.coord u l * SeqL2.coord v l) ∧
            ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
              (ℱ' : Filtration ℝ mΩ') (B : ℝ≥0 → Ω' → ℕ → ℝ) (S : ℝ → Ω → SeqL2 →L[ℝ] SeqL2)
              (Sb : ℝ → SeqL2 →L[ℝ] SeqL2) (G : ℝ → Ω' → SeqL2),
              IsAdaptedGaussianCoupling P ℱ Φ M T Cdet P' π ℱ' S45.s45_seqBasis B S Sb G ∧
              (∀ r ∈ Set.Icc 0 T, ∫⁻ w, ∑' j, ‖(S r (π w) - Sb r) (S45.s45_seqBasis j)‖ₑ ^ 2 ∂P' ≤
                ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2))) ∧
              (∀ t ∈ Set.Icc 0 T, ∀ D : ℝ → Ω' → SeqL2,
                IsHilbertItoIntegral P' ℱ' B (fun r w j =>
                  if r ≤ t then semiDiag om (t - r) ((S r (π w) - Sb r) (S45.s45_seqBasis j)) else 0) D →
                ∫⁻ w, ‖D t w‖ₑ ^ 2 ∂P' ≤
                  ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2))) ∧
              IsCylindricalBrownian P' ℱ' (fun t w (ia : Fin N × Fin d) => W t (π w) ia.1 ia.2) ∧
              (∀ x y, IsProgressive ℱ' (fun r w => inner ℝ (S r (π w) x) y)) ∧
              (∀ T' : ℝ, IsHSIntegrand P' ℱ' T'
                (fun r w (j : ℕ) => if r ≤ T then S r (π w) (S45.s45_seqBasis j) else 0)) ∧
              Indep ((ℱ 0).comap π) (cylindricalPathSigma B) P' ∧
              (∀ x y, Measurable fun σ => inner ℝ (Sb σ x) y)

set_option maxHeartbeats 1600000 in
theorem s81q_coupling_claim {d : ℕ} (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ} (hdata : IsSpectralData d β ρβ e om) {t₀ C4 : ℝ} (ht₀ : 0 < t₀)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (HRS.Whole.withDensityReal ρβ) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l))) {τ : ℝ} (hτ : 4 * t₀ < τ) :
    S81QCouplingClaim d a β ρβ e om τ := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hτ0 : 0 < τ := by linarith
  obtain ⟨Cs, hCs0, hStat⟩ := S45.s45_static_all hd hs0.le hsd ha hβ
  have hρeq : ρβ = thermalDensity d ((d : ℝ) / 2) a β :=
    HRS.Whole.S78.s78_eq_thermalDensity hd hs0 hsd ha hβ hρ
  have hμ : HRS.Whole.withDensityReal ρβ = thermalMeasure d ((d : ℝ) / 2) a β := by rw [hρeq]; rfl
  haveI hprob : IsProbabilityMeasure (thermalMeasure d ((d : ℝ) / 2) a β) := by
    rw [← hμ]; exact HRS.Whole.Q34.isProbabilityMeasure_nu hρ.1.1
  set C4' : ℝ := max C4 0 with hC4'
  have hC40 : 0 ≤ C4' := le_max_right _ _
  have hL4' : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (thermalMeasure d ((d : ℝ) / 2) a β) ≤
      ENNReal.ofReal (C4' * Real.exp (t₀ * om l)) := by
    intro l
    rw [← hμ]
    refine (hL4 l).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  obtain ⟨c, hc, hgrowth⟩ := hdata.growth
  have hom : ∀ l, 0 < om l := hdata.pos
  have hmono : Monotone om := hdata.mono
  have he : ∀ l, ContDiff ℝ ∞ (e l) := hdata.smooth
  have hgrad : ∀ i j, ∫ x, s8p_f e i j x ∂(thermalMeasure d ((d : ℝ) / 2) a β) =
      if i = j then om i else 0 := by
    intro i j; rw [← hμ]; exact hdata.grad_orth i j
  have hint : ∀ l, Integrable (s8p_f e l l) (thermalMeasure d ((d : ℝ) / 2) a β) := by
    intro l; rw [← hμ]; exact hdata.grad_int l l
  have hgrowth' : ∀ l : ℕ, c * ((l : ℝ) + 1) ^ (1 / (d : ℝ)) ≤ om l := hgrowth
  have hmul := s8p_summable_mul_exp_growth hd1 hc hgrowth' (fun l => (hom l).le) hτ0
  have hdv : Summable (s8p_dv β om τ) := by
    refine (hmul.mul_left (2 * β⁻¹)).congr fun l => ?_
    unfold s8p_dv; ring
  have hFfin : ∑' l, ENNReal.ofReal (Real.exp (-τ * om l) * om l) < ⊤ := by
    have : Summable fun l => Real.exp (-τ * om l) * om l := hmul.congr fun l => mul_comm _ _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => mul_nonneg (Real.exp_pos _).le (hom l).le) this]
    exact ENNReal.ofReal_lt_top
  have hgood : ∀ᵐ x ∂(thermalMeasure d ((d : ℝ) / 2) a β), s8p_good om e τ x :=
    s8p_good_ae he τ hint (fun l => by simpa using hgrad l l) hFfin
  set κ : ℝ := τ / 2 - 2 * t₀ with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hsκ := s8p_summable_exp_growth hd1 hc hgrowth' hκ0
  set T0r : ℝ := ∑' l, Real.exp (-κ * om l) with hT0r
  set K0 : ℝ := C4' ^ 4 / (β * om 0) with hK0
  have hK00 : 0 ≤ K0 := by have := hom 0; positivity
  set M0 : ℝ := max Cs (Cs ^ 2) with hM0
  have hM00 : 0 ≤ M0 := hCs0.trans (le_max_left _ _)
  have hom0 : 0 < om 0 := hom 0
  refine ⟨4 * K0 * M0 * T0r ^ 2 * (1 + 1 / om 0), ?_⟩
  intro N hN Ω _ P _ X₀ W X hR ℱ hW hprog Φ
  have hN0 : 0 < N := by omega
  have hSN := hStat N hN
  have hlaw : ∀ t : ℝ≥0, P.map (X t) = s8p_QN d ((d : ℝ) / 2) a β N := fun t =>
    HRS.Whole.S79.s79_law_X_eq hR t
  have hJ : ∫⁻ x, s8p_Fq om e τ x ∂(thermalMeasure d ((d : ℝ) / 2) a β) < ⊤ := by
    rw [s8p_lintegral_Fq he τ hint (fun l => by simpa using hgrad l l)]; exact hFfin
  have hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ := fun T =>
    s8p_isHSIntegrand hN0 hSN hβ he hJ X hlaw ℱ hprog T
  refine ⟨by rw [hμ]; exact hgood, hΦ, ?_⟩
  intro T hT M hM
  set Cdet0 := s8p_Cdet hβ hom hτ0 with hC0
  have hsb := s8p_isDetCovDensity_Cdet hβ hom hτ0 hdv T
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', B, S, Sb, G, hfil, hBr, hind, hsqrtS, hemp, hsqrtSb, hgauss,
      hmeasG, hindG, hcent, hcov, hL2, hHSS, hHSSb, hprog0, hSbm, hprogS, hWb⟩ :=
    HRS.Whole.S81P.s81p_polar_ext P (S45.s45_seqBasis) ℱ T hT ⟨ℱ 0, le_rfl⟩
      (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) hW Φ hΦ M hM (fun _ => Cdet0) hsb
  -- arithmetic
  set q : ℝ := (N : ℝ)⁻¹ + HRS.deltaN d ((d : ℝ) / 2) N ^ 2 with hq
  set cN : ℝ := Cs / N + Cs ^ 2 * HRS.deltaN d ((d : ℝ) / 2) N ^ 2 with hcN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq0 : 0 ≤ q := by positivity
  have hcN0 : 0 ≤ cN := by positivity
  have hcNq : cN ≤ M0 * q := by
    rw [hcN, hq]
    have h1 : Cs / N ≤ M0 * (N : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have h2 : Cs ^ 2 * HRS.deltaN d ((d : ℝ) / 2) N ^ 2 ≤ M0 * HRS.deltaN d ((d : ℝ) / 2) N ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    nlinarith
  set Zr : ℝ := 4 * K0 * cN * T0r ^ 2 with hZr
  have hZr0 : 0 ≤ Zr := by positivity
  have hZrq : Zr ≤ 4 * K0 * M0 * T0r ^ 2 * q := by
    rw [hZr]
    have : 4 * K0 * cN * T0r ^ 2 = (4 * K0 * T0r ^ 2) * cN := by ring
    rw [this]
    calc (4 * K0 * T0r ^ 2) * cN ≤ (4 * K0 * T0r ^ 2) * (M0 * q) := by gcongr
      _ = _ := by ring
  have hC1 : 0 ≤ 4 * K0 * M0 * T0r ^ 2 := by positivity
  have hb1 : ENNReal.ofReal Zr ≤ ENNReal.ofReal (4 * K0 * M0 * T0r ^ 2 * (1 + 1 / om 0) * q) := by
    refine ENNReal.ofReal_le_ofReal (hZrq.trans ?_)
    have : 0 ≤ 4 * K0 * M0 * T0r ^ 2 * q := by positivity
    have h1 : (0 : ℝ) ≤ 1 / om 0 := by positivity
    nlinarith
  have hb2 : 2 * (ENNReal.ofReal Zr * ENNReal.ofReal (1 / (2 * om 0))) ≤
      ENNReal.ofReal (4 * K0 * M0 * T0r ^ 2 * (1 + 1 / om 0) * q) := by
    have e2 : 2 * (ENNReal.ofReal Zr * ENNReal.ofReal (1 / (2 * om 0))) =
        ENNReal.ofReal (Zr / om 0) := by
      rw [← ENNReal.ofReal_mul hZr0, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      field_simp
    rw [e2]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (0 : ℝ) ≤ 1 / om 0 := by positivity
    have h2 : 0 ≤ 4 * K0 * M0 * T0r ^ 2 * q := by positivity
    calc Zr / om 0 = Zr * (1 / om 0) := by ring
      _ ≤ (4 * K0 * M0 * T0r ^ 2 * q) * (1 / om 0) := by gcongr
      _ ≤ _ := by nlinarith
  -- the trace bound
  have hbound : ∀ r ∈ Set.Icc 0 T, ∫⁻ w, ∑' j, ‖(S r (π w) - Sb r) (S45.s45_seqBasis j)‖ₑ ^ 2 ∂P' ≤
      ENNReal.ofReal Zr := by
    intro r hr
    have h := s8p_trace_realization hπ hN hCs0 hSN hβ hom hmono hτ0 hdv hC40 e he hgrad hL4'
      (Y := X (Real.toNNReal r)) (s8p_measurable_config hprog r) (hlaw _) hgood
      (S := S r) (Sb := Sb r) (fun z => hsqrtS r z) (hsqrtSb r hr)
    rw [s8p_Z_eq (K0 := K0) (cN := cN) (T0r := T0r) (κ := κ) (om := om) (by positivity) hT0r hsκ] at h
    exact h
  refine ⟨fun _ => Cdet0, fun r hr u v => ?_, Ω', mΩ', P', π, ℱ', B, S, Sb, G,
    ⟨hP', hπ, hfil, hBr, hind, fun r hr z => hsqrtS r z, hemp,
      hsqrtSb, hgauss⟩, fun r hr => (hbound r hr).trans hb1, ?_⟩
  · exact s8p_Cdet_apply hβ hom hτ0 u v
  · refine ⟨fun t ht D hD => ?_, hWb, hprogS, hHSS, hind, hSbm⟩
    exact (s8p_conv_bound hBr hβ hom hmono hτ0 hprogS hsqrtSb ENNReal.ofReal_ne_top hbound ht hD).trans hb2



end HRS.Whole.S81Q
