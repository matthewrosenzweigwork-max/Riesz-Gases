import HRS.MD.EQRemInt13

/-!
# EQ-MILD, part 2: Hilbert-space bookkeeping

* `eqmild_fc`: the Fourier coefficient `F ↦ F̂(k)` as a continuous linear functional on `E_M`.
* `eqmild_eta_eq`: `η_N = ζ_N + c` with the deterministic `c = √N (m_N - μ)` (for the centre `m_N = meanEmpirical G`).
* `eqmild_zeta_integral`: `E ℓ(ζ_N(Y)) = 0` for every continuous linear functional `ℓ` when `Y ~ G`.
* `eqmild_conv_mean`: a stochastic convolution `Z_t = ∫_0^t V(t,u) dM_u` has `E ℓ(Z_t) = 0` (Riemann sums of a martingale).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQMild

open HRS HRS.MD.EQ29 HRS.MD.EQRem HRS.Quad HRS.Uniform

variable {d : ℕ}

/-- The Fourier coefficient functional. -/
def eqmild_fc (M : ℝ) (k : NonzeroLattice d) : NegSobolev d M →L[ℝ] ℝ :=
  (Lattice.jp k.1 ^ M) • (negCoordCLM (m := M) k)

theorem eqmild_fc_apply (M : ℝ) (k : NonzeroLattice d) (F : NegSobolev d M) :
    eqmild_fc M k F = NegSobolev.fourierCoeff F k := by
  unfold eqmild_fc
  simp [negCoordCLM_apply, NegSobolev.fourierCoeff]

theorem eqmild_ofMeasureDiff_self {M : ℝ} (hM : (d : ℝ) < 2 * M) (a : Measure (Torus d))
    [IsFiniteMeasure a] : NegSobolev.ofMeasureDiff M a a = 0 := by
  have h := NegSobolev.ofMeasureDiff_add hM a a a
  have h2 : NegSobolev.ofMeasureDiff M a a + NegSobolev.ofMeasureDiff M a a =
      NegSobolev.ofMeasureDiff M a a + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- `η_N = ζ_N + c`, `c = √N (m - μ)`. -/
theorem eqmild_eta_eq {M : ℝ} (hM : (d : ℝ) < 2 * M) {N : ℕ} (hN : 1 ≤ N) (G : Measure (Config d N))
    [IsProbabilityMeasure G] (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (Y : Config d N) :
    etaE M Y μ = zetaE M G Y + Real.sqrt N • NegSobolev.ofMeasureDiff M (meanEmpirical G) μ := by
  haveI := empirical_isProbabilityMeasure hN Y
  haveI := isProbabilityMeasure_meanEmpirical G hN
  unfold etaE zetaE flucE
  rw [NegSobolev.ofMeasureDiff_add hM (empirical Y) (meanEmpirical G) μ, smul_add]

theorem eqmild_zeta_integral {M : ℝ} (hM : (d : ℝ) < 2 * M) {N : ℕ} (hN : 1 ≤ N)
    (G : Measure (Config d N)) [IsProbabilityMeasure G]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Config d N) (hY : AEMeasurable Y P) (hYG : P.map Y = G) (ℓ : NegSobolev d M →L[ℝ] ℝ) :
    Integrable (fun ω => ℓ (zetaE M G (Y ω))) P ∧ ∫ ω, ℓ (zetaE M G (Y ω)) ∂P = 0 := by
  haveI := isProbabilityMeasure_meanEmpirical G hN
  set mm := meanEmpirical G with hmm
  set F : Config d N → NegSobolev d M := fun Y' => NegSobolev.ofMeasureDiff M (empirical Y') mm with hF
  have hFm : Measurable F := measurable_ofMeasureDiff_empirical hM mm hN
  have hFb : ∀ Y', ‖F Y'‖ ≤ Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M))) := by
    intro Y'
    haveI := empirical_isProbabilityMeasure hN Y'
    exact norm_ofMeasureDiff_le hM (empirical Y') mm
  have hFi : Integrable F G :=
    Integrable.of_bound hFm.aestronglyMeasurable _ (ae_of_all _ hFb)
  have hz : ∀ Y', zetaE M G Y' = Real.sqrt N • F Y' := fun Y' => rfl
  have hint : Integrable (fun Y' => ℓ (zetaE M G Y')) G := by
    have : (fun Y' => ℓ (zetaE M G Y')) = fun Y' => (Real.sqrt N • ℓ) (F Y') := by
      funext Y'; rw [hz]; simp
    rw [this]
    exact ((Real.sqrt N • ℓ).integrable_comp hFi)
  have hmeas : Measurable (fun Y' => ℓ (zetaE M G Y')) := by
    have : (fun Y' => ℓ (zetaE M G Y')) = fun Y' => (Real.sqrt N • ℓ) (F Y') := by
      funext Y'; rw [hz]; simp
    rw [this]
    exact (Real.sqrt N • ℓ).continuous.measurable.comp hFm
  have hmap : Integrable (fun Y' => ℓ (zetaE M G Y')) (P.map Y) := by rw [hYG]; exact hint
  refine ⟨hmap.comp_aemeasurable hY, ?_⟩
  have e1 : ∫ ω, ℓ (zetaE M G (Y ω)) ∂P = ∫ Y', ℓ (zetaE M G Y') ∂G := by
    have := integral_map hY hmeas.aestronglyMeasurable
    rw [hYG] at this
    exact this.symm
  rw [e1]
  have e2 : (fun Y' => ℓ (zetaE M G Y')) = fun Y' => (Real.sqrt N • ℓ) (F Y') := by
    funext Y'; rw [hz]; simp
  rw [e2, ContinuousLinearMap.integral_comp_comm _ hFi]
  have e3 : ∫ Y', F Y' ∂G = NegSobolev.ofMeasureDiff M (meanEmpirical G) mm :=
    integral_ofMeasureDiff_empirical hM G mm hN hFm.aemeasurable
  rw [e3, ← hmm, eqmild_ofMeasureDiff_self hM mm]
  simp

/-- The mean of a stochastic convolution against a Hilbert martingale vanishes. -/
theorem eqmild_conv_mean {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ℱ : Filtration ℝ mΩ) (T : ℝ) (Mart : ℝ → Ω → E)
    (Sg : ℝ → Ω → (E →L[ℝ] E →L[ℝ] ℝ)) (hM : IsHilbertMartingaleWithCovariation P ℱ T Mart Sg)
    (Vev : ℝ → ℝ → E →L[ℝ] E) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (Z : Ω → E)
    (hZ : IsStochConv P Vev (ContinuousLinearMap.id ℝ E) Mart 0 t Z) (hZm : AEMeasurable Z P)
    (ℓ : E →L[ℝ] ℝ) :
    Integrable (fun ω => ℓ (Z ω)) P ∧ ∫ ω, ℓ (Z ω) ∂P = 0 := by
  classical
  -- one partition: bound
  have key : ∀ η : ℝ, 0 < η → Integrable (fun ω => ℓ (Z ω)) P ∧ |∫ ω, ℓ (Z ω) ∂P| ≤ ‖ℓ‖ * η := by
    intro η hη
    obtain ⟨δ, hδ, hpart⟩ := hZ (η ^ 2) (by positivity)
    obtain ⟨n0, hn0⟩ := exists_nat_gt (t / δ)
    set n : ℕ := n0 + 1 with hn
    have hnpos : (0 : ℝ) < n := by rw [hn]; positivity
    set r : Fin (n + 1) → ℝ := fun i => t * (i : ℝ) / n with hr
    have hr0 : r 0 = 0 := by simp [hr]
    have hrl : r (Fin.last n) = t := by
      simp only [hr, Fin.val_last]
      field_simp
    have hmono : Monotone r := by
      intro i j hij
      simp only [hr]
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this ht) hnpos.le
    have hmesh : ∀ i : Fin n, r i.succ - r i.castSucc < δ := by
      intro i
      simp only [hr, Fin.val_succ, Fin.val_castSucc]
      push_cast
      have : t * ((i : ℝ) + 1) / n - t * (i : ℝ) / n = t / n := by field_simp; ring
      rw [this]
      rw [div_lt_iff₀ hnpos]
      have h1 : t / δ < n := by
        have : (n0 : ℝ) < n := by rw [hn]; push_cast; linarith
        linarith
      rw [div_lt_iff₀ hδ] at h1
      linarith
    have hL2 := hpart n r hr0 hrl hmono hmesh
    set R : Ω → E := fun ω => riemannSum Vev (ContinuousLinearMap.id ℝ E) Mart t r ω with hR
    -- the Riemann sum is a.e. strongly measurable and ℓ ∘ R has mean zero
    have hMasm : ∀ τ ∈ Set.Icc (0 : ℝ) T, AEStronglyMeasurable (Mart τ) P :=
      fun τ hτ => (hM.sq_int τ hτ).aestronglyMeasurable
    have hrIcc : ∀ i : Fin (n + 1), r i ∈ Set.Icc (0 : ℝ) T := by
      intro i
      constructor
      · simp only [hr]; positivity
      · calc r i ≤ r (Fin.last n) := hmono (Fin.le_last i)
          _ = t := hrl
          _ ≤ T := htT
    have hRm : AEStronglyMeasurable R P := by
      simp only [hR, riemannSum]
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (Vev t (r i.castSucc)).continuous.comp_aestronglyMeasurable
        (((hMasm _ (hrIcc _)).sub (hMasm _ (hrIcc _))))
    have hZRm : AEStronglyMeasurable (fun ω => Z ω - R ω) P := hZm.aestronglyMeasurable.sub hRm
    -- ℓ ∘ R
    have hterm : ∀ i : Fin n, Integrable (fun ω => ℓ (Vev t (r i.castSucc)
        (ContinuousLinearMap.id ℝ E (Mart (r i.succ) ω - Mart (r i.castSucc) ω)))) P ∧
        ∫ ω, ℓ (Vev t (r i.castSucc)
          (ContinuousLinearMap.id ℝ E (Mart (r i.succ) ω - Mart (r i.castSucc) ω))) ∂P = 0 := by
      intro i
      set w : E := (InnerProductSpace.toDual ℝ E).symm (ℓ.comp (Vev t (r i.castSucc))) with hw
      have hwx : ∀ x : E, ℓ (Vev t (r i.castSucc) x) = inner ℝ x w := by
        intro x
        have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := x) (y := ℓ.comp (Vev t (r i.castSucc)))
        rw [real_inner_comm] at this
        simpa using this.symm
      have hmg := hM.martingale w
      have hi1 := hmg.integrable (r i.succ)
      have hi2 := hmg.integrable (r i.castSucc)
      have e : (fun ω => ℓ (Vev t (r i.castSucc)
          (ContinuousLinearMap.id ℝ E (Mart (r i.succ) ω - Mart (r i.castSucc) ω)))) =
          fun ω => inner ℝ (Mart (r i.succ) ω) w - inner ℝ (Mart (r i.castSucc) ω) w := by
        funext ω
        simp only [ContinuousLinearMap.id_apply]
        rw [hwx, inner_sub_left]
      rw [e]
      refine ⟨hi1.sub hi2, ?_⟩
      rw [integral_sub hi1 hi2]
      have hle : r i.castSucc ≤ r i.succ := hmono (Fin.castSucc_le_succ i)
      have := hmg.setIntegral_eq hle MeasurableSet.univ
      simp only [Measure.restrict_univ] at this
      rw [this]; ring
    have hRint : Integrable (fun ω => ℓ (R ω)) P := by
      have : (fun ω => ℓ (R ω)) = fun ω => ∑ i : Fin n, ℓ (Vev t (r i.castSucc)
          (ContinuousLinearMap.id ℝ E (Mart (r i.succ) ω - Mart (r i.castSucc) ω))) := by
        funext ω; simp only [hR, riemannSum, map_sum]
      rw [this]
      exact integrable_finset_sum _ fun i _ => (hterm i).1
    have hRmean : ∫ ω, ℓ (R ω) ∂P = 0 := by
      have : (fun ω => ℓ (R ω)) = fun ω => ∑ i : Fin n, ℓ (Vev t (r i.castSucc)
          (ContinuousLinearMap.id ℝ E (Mart (r i.succ) ω - Mart (r i.castSucc) ω))) := by
        funext ω; simp only [hR, riemannSum, map_sum]
      rw [this, integral_finset_sum _ fun i _ => (hterm i).1]
      exact Finset.sum_eq_zero fun i _ => (hterm i).2
    -- L² to L¹
    have hcs := eqrem_cs P (fun ω => ‖Z ω - R ω‖ₑ) hZRm.enorm
    rw [measure_univ, one_mul] at hcs
    have hsq : (∫⁻ ω, ‖Z ω - R ω‖ₑ ∂P) ^ 2 ≤ ENNReal.ofReal η ^ 2 := by
      refine hcs.trans ?_
      refine le_trans (le_of_lt hL2) ?_
      rw [← ENNReal.ofReal_pow hη.le]
    have hL1 : ∫⁻ ω, ‖Z ω - R ω‖ₑ ∂P ≤ ENNReal.ofReal η := eqrem_ennreal_le_of_sq_le hsq
    have hZRint : Integrable (fun ω => Z ω - R ω) P :=
      ⟨hZRm, lt_of_le_of_lt hL1 ENNReal.ofReal_lt_top⟩
    have hdiffint : Integrable (fun ω => ℓ (Z ω - R ω)) P := ℓ.integrable_comp hZRint
    have hZint : Integrable (fun ω => ℓ (Z ω)) P := by
      have : (fun ω => ℓ (Z ω)) = fun ω => ℓ (Z ω - R ω) + ℓ (R ω) := by
        funext ω; simp
      rw [this]; exact hdiffint.add hRint
    refine ⟨hZint, ?_⟩
    have e1 : ∫ ω, ℓ (Z ω) ∂P = ∫ ω, ℓ (Z ω - R ω) ∂P := by
      have : (fun ω => ℓ (Z ω)) = fun ω => ℓ (Z ω - R ω) + ℓ (R ω) := by
        funext ω; simp
      rw [this, integral_add hdiffint hRint, hRmean, add_zero]
    rw [e1]
    have h2 : |∫ ω, ℓ (Z ω - R ω) ∂P| ≤ ‖ℓ‖ * ∫ ω, ‖Z ω - R ω‖ ∂P := by
      have := norm_integral_le_of_norm_le (hZRint.norm.const_mul ‖ℓ‖)
        (ae_of_all _ fun ω => ℓ.le_opNorm (Z ω - R ω)) (f := fun ω => ℓ (Z ω - R ω))
      rw [Real.norm_eq_abs] at this
      refine this.trans (le_of_eq ?_)
      rw [integral_const_mul]
    refine h2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hn1 : ∫ ω, ‖Z ω - R ω‖ ∂P = (∫⁻ ω, ‖Z ω - R ω‖ₑ ∂P).toReal := by
      rw [integral_norm_eq_lintegral_enorm hZRm]
    rw [hn1]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hL1
    rwa [ENNReal.toReal_ofReal hη.le] at this
  have hint := (key 1 one_pos).1
  refine ⟨hint, ?_⟩
  have hzero : ∀ ε : ℝ, 0 < ε → |∫ ω, ℓ (Z ω) ∂P| ≤ 0 + ε := by
    intro ε hε
    have := (key (ε / (‖ℓ‖ + 1)) (by positivity)).2
    refine this.trans ?_
    have h0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
    rw [zero_add, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := le_of_forall_pos_le_add hzero
  exact abs_nonpos_iff.mp this

end HRS.MD.EQMild

end
