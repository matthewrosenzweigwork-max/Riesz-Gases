import HRS.MS.Fp81S21CenteredAdapter2
import HRS.MS.S111BDAux4
import HRS.MS.R2InterpAux91
import HRS.MS.CritWholeFinal
import HRS.MS.S21E_Zeta
import HRS.MS.Fp81S21LeadingAdapter2

/-!
# S2.1(iii), centered adapter: Gaussian barycenters and recent restrictions

The Gaussian window is a centered Gaussian in the path Banach space, hence
Bochner integrable with zero mean. The final lemma records the exact
restriction transfer once the particle path-centering identity is available.
It does not assume a quantitative mean estimate: the generic factor-two
centering result applies directly to the raw Wasserstein envelope.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- At each fixed time, every Hermite coordinate of the exactly centered field is
integrable and has expectation zero.  This is the scalar input for the path
barycenter identity. -/
private theorem fp81s21_zetaField_coord_integral_zero
    {d N : ℕ} {m : ℝ} (hm : (d : ℝ) < m) (hN : 0 < N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (u : ℝ) (α : MultiIndex d) :
    Integrable
      (fun ω => OscDual.coord (zetaB m (P.map (X (Real.toNNReal u)))
        (X (Real.toNNReal u) ω)) α) P ∧
      (∫ ω, OscDual.coord (zetaB m (P.map (X (Real.toNNReal u)))
        (X (Real.toNNReal u) ω)) α ∂P) = 0 := by
  have hN1 : 1 ≤ N := by omega
  have hXu : Measurable (X (Real.toNNReal u)) := hXm _
  let f : Euc d → ℝ := oscTestFun m α
  obtain ⟨C, hC0, hCf⟩ := HRS.MS.GenPath.s56_oscTestFun_bound (d := d) m
  have hfmeas : Measurable f := HRS.MS.GenPath.s56_oscTestFun_cont m α |>.measurable
  have hPairInt : Integrable
      (fun ω => HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal u) ω)) f) P := by
    have hsum : Integrable (fun ω => ∑ i : Fin N,
        f (X (Real.toNNReal u) ω i)) P := by
      refine integrable_finset_sum _ fun i hi => ?_
      refine Integrable.of_bound
        ((hfmeas.comp ((measurable_pi_apply i).comp hXu)).aestronglyMeasurable)
        (C * oscEigenvalue d α ^ (-(m / 2))) ?_
      filter_upwards [] with ω
      rw [Real.norm_eq_abs]
      exact hCf α (X (Real.toNNReal u) ω i)
    have hscaled : Integrable (fun ω => (N : ℝ)⁻¹ *
        ∑ i : Fin N, f (X (Real.toNNReal u) ω i)) P := hsum.const_mul _
    refine hscaled.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (HRS.Whole.pair_empirical hN (X (Real.toNNReal u) ω) f).symm
  have hPairMean := HRS.MS.S21.s21_E_pair_emp hN1 P
    (X (Real.toNNReal u)) hXu (P.map (X (Real.toNNReal u))) rfl hfmeas
    (fun x => hCf α x)
  have hCoord : ∀ ω, OscDual.coord (zetaB m (P.map (X (Real.toNNReal u)))
      (X (Real.toNNReal u) ω)) α = Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal u) ω)) f -
          HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X (Real.toNNReal u)))) f) := by
    intro ω
    rw [HRS.MS.R2Interp.s102_coord_zetaB (m := m) hm hN P X hXm u ω α]
    rfl
  have hScalarInt : Integrable (fun ω => Real.sqrt N *
      (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal u) ω)) f -
        HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X (Real.toNNReal u)))) f)) P :=
    (hPairInt.sub (integrable_const _)).const_mul _
  have hScalarMean : (∫ ω, Real.sqrt N *
      (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal u) ω)) f -
        HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X (Real.toNNReal u)))) f) ∂P) = 0 := by
    rw [integral_const_mul, integral_sub hPairInt (integrable_const _), hPairMean]
    simp
  refine ⟨hScalarInt.congr (Filter.Eventually.of_forall fun ω => (hCoord ω).symm), ?_⟩
  calc
    (∫ ω, OscDual.coord (zetaB m (P.map (X (Real.toNNReal u)))
        (X (Real.toNNReal u) ω)) α ∂P) =
        ∫ ω, Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal u) ω)) f -
          HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X (Real.toNNReal u)))) f) ∂P := by
            exact integral_congr_ae (Filter.Eventually.of_forall hCoord)
    _ = 0 := hScalarMean

/-- The moving particle window is centered by its own Bochner barycenter.
Weak continuity of the trajectory makes the raw window a.e. measurable and
continuous on the window; the scalar field coordinates have mean zero, so
continuous evaluations identify the full path barycenter. -/
theorem fp81s21_particle_window_centered
    (p : Parameters) {δ H b : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N) (hH : 0 < H) (hb : 0 ≤ b) :
    Integrable
        (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b (Real.sqrt N) A.X R.ρ) A.P ∧
      zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b A.P A.X =ᵐ[A.P]
        (fun ω => flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b
          (Real.sqrt N) A.X R.ρ ω -
          ∫ ω', flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b
            (Real.sqrt N) A.X R.ρ ω' ∂A.P) := by
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let η : A.Ω → OscPath p.d m H := flucPathW m H b (Real.sqrt N) A.X R.ρ
  let ζ : A.Ω → OscPath p.d m H := zetaPathW m H b A.P A.X
  let etaField : ℝ → A.Ω → OscDual p.d m := fun t ω =>
    HRS.Whole.etaB m (A.X (Real.toNNReal t) ω) (HRS.Whole.withDensityReal (R.ρ t))
  let zetaField : ℝ → A.Ω → OscDual p.d m := fun t ω =>
    HRS.Whole.zetaB m (A.P.map (A.X (Real.toNNReal t))) (A.X (Real.toNNReal t) ω)
  let biasField : ℝ → OscDual p.d m := fun t =>
    Real.sqrt N • OscDual.ofMeasureDiff m
      (HRS.Whole.meanEmpirical (A.P.map (A.X (Real.toNNReal t))))
      (HRS.Whole.withDensityReal (R.ρ t))
  have hNpos : 0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide : 1 ≤ 2) p.hd
  have hm : (p.d : ℝ) < m := by
    dsimp [m, wholeSpaceIndex]
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    push_cast
    linarith
  have hstrong := A.strong (b + H)
  have hXm : ∀ t, Measurable (A.X t) := hstrong.adapted
  have hXc : ∀ᵐ ω ∂A.P, ∀ i, Continuous fun t : ℝ≥0 => A.X t ω i := hstrong.cont
  have hprob : ∀ t ∈ Set.Icc (0 : ℝ) (b + H), HRS.Whole.IsProbDensity (R.ρ t) := by
    intro t ht
    exact (R.resulting.global (b + H)).density t ht
  have hweak : ∀ ψ : Euc p.d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * R.ρ r x) (Set.Icc (0 : ℝ) (b + H)) := by
    intro ψ hψ hbd
    have hβprob : HRS.Whole.IsProbDensity R.ρβ := R.thermal.2.1
    have hβpos : ∀ x, 0 < R.ρβ x := HRS.Whole.S78.s78_thermal_pos R.thermal.2
    exact (HRS.Whole.s21p_rho_weak_cont hβprob hβpos R.resulting ψ hψ hbd).mono
      (fun t ht => ht.1)
  have hηae : AEMeasurable η A.P := by
    exact HRS.Whole.s21p_fluc_window_aemeas hd1 hNpos hm hb hH.le A.P A.X R.ρ
      (Real.sqrt N) hXm hXc hprob hweak
  obtain ⟨Kb, hKb0, hKb⟩ := HRS.Whole.BreakdownS81.s81bd_norm_ofMeasureDiff_le
    (d := p.d) hm
  have hρprob : ∀ t : ℝ, 0 ≤ t → IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ t)) := by
    intro t ht
    exact HRS.MS.Thm.cb_withDensityReal_isProb
      ((R.resulting.global t).density t ⟨ht, le_rfl⟩)
  have hmapprob : ∀ t : ℝ,
      IsProbabilityMeasure (A.P.map (A.X (Real.toNNReal t))) := by
    intro t
    exact (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  have hηbound : ∀ ω, ‖η ω‖ ≤ Real.sqrt N * Kb := by
    intro ω
    let f : ℝ → OscDual p.d m := fun t => Real.sqrt N •
      OscDual.ofMeasureDiff m (HRS.Whole.empirical (A.X (Real.toNNReal t) ω))
        (HRS.Whole.withDensityReal (R.ρ t))
    change ‖windowPathOf m H b f‖ ≤ Real.sqrt N * Kb
    by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) H => f (b + t)
    · have hpath : windowPathOf m H b f =
          (⟨fun t : Set.Icc (0 : ℝ) H => f (b + t), hc⟩ : OscPath p.d m H) := by
        unfold windowPathOf
        exact dif_pos hc
      rw [hpath]
      apply (ContinuousMap.norm_le _
        (mul_nonneg (Real.sqrt_nonneg _) hKb0)).2
      intro t
      let u : ℝ := b + (t : ℝ)
      have hu : 0 ≤ u := by dsimp [u]; linarith [hb, t.2.1]
      letI : IsProbabilityMeasure (HRS.Whole.empirical (A.X (Real.toNNReal u) ω)) :=
        HRS.Whole.empirical_isProbabilityMeasure hNpos _
      letI : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ u)) := hρprob u hu
      dsimp [f]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (hKb _ _ inferInstance inferInstance) (Real.sqrt_nonneg _)
    · have hpath : windowPathOf m H b f = 0 := by
        unfold windowPathOf
        exact dif_neg hc
      rw [hpath, norm_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) hKb0
  have hηint : Integrable η A.P :=
    Integrable.of_bound hηae.aestronglyMeasurable (Real.sqrt N * Kb)
      (Filter.Eventually.of_forall fun ω => hηbound ω)
  have hηcont : ∀ᵐ ω ∂A.P,
      ContinuousOn (fun t : ℝ => Real.sqrt N • OscDual.ofMeasureDiff m
        (HRS.Whole.empirical (A.X (Real.toNNReal t) ω)) (HRS.Whole.withDensityReal (R.ρ t)))
        (Set.Icc (0 : ℝ) (b + H)) := by
    filter_upwards [hXc] with ω hω
    exact HRS.MS.GenPath.s56_xi_cont_time hd1 hm (Real.sqrt N) hNpos R.ρ hprob hweak
      (fun t => A.X (Real.toNNReal t) ω)
      (fun i => (hω i).comp continuous_real_toNNReal)
  have hζcont : ∀ᵐ ω ∂A.P, Continuous fun t : ℝ => zetaField t ω :=
    HRS.Whole.s21e_zeta_cont_time hd1 hNpos hm A.P A.X hXm hXc
  have hηeval (τ : Set.Icc (0 : ℝ) H) :
      (fun ω => OscPath.at' (η ω) τ) =ᵐ[A.P]
        (fun ω => etaField (b + (τ : ℝ)) ω) := by
    filter_upwards [hηcont] with ω hω
    have hmem : ∀ t : Set.Icc (0 : ℝ) H, b + (t : ℝ) ∈ Set.Icc (0 : ℝ) (b + H) := by
      intro t
      constructor
      · linarith [hb, t.2.1]
      · linarith [t.2.2]
    have hc : Continuous fun t : Set.Icc (0 : ℝ) H => etaField (b + (t : ℝ)) ω := by
      exact hω.comp_continuous (continuous_const.add continuous_subtype_val) hmem
    have hpath : η ω =
        (⟨fun t : Set.Icc (0 : ℝ) H => etaField (b + (t : ℝ)) ω, hc⟩ : OscPath p.d m H) := by
      change windowPathOf m H b (fun t => etaField t ω) = _
      unfold windowPathOf
      exact dif_pos hc
    rw [hpath]
    rfl
  have hMeanCoord (τ : Set.Icc (0 : ℝ) H) (α : MultiIndex p.d) :
      OscDual.coord (OscPath.at' (∫ ω, η ω ∂A.P) τ) α =
        OscDual.coord (biasField (b + (τ : ℝ))) α := by
    let u : ℝ := b + (τ : ℝ)
    have hu : 0 ≤ u := by dsimp [u]; linarith [hb, τ.2.1]
    letI : IsProbabilityMeasure (A.P.map (A.X (Real.toNNReal u))) := hmapprob u
    letI : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ u)) := hρprob u hu
    have hfield (ω : A.Ω) : etaField u ω = zetaField u ω + biasField u := by
      change HRS.Whole.etaB m (A.X (Real.toNNReal u) ω)
        (HRS.Whole.withDensityReal (R.ρ u)) = _
      exact fp81s21_etaField_eq_zeta_add_mean hm
        (A.P.map (A.X (Real.toNNReal u))) (A.X (Real.toNNReal u) ω)
        (HRS.Whole.withDensityReal (R.ρ u)) hN1
    obtain ⟨hζcoordInt, hζcoordMean⟩ :=
      fp81s21_zetaField_coord_integral_zero hm hNpos A.P A.X hXm u α
    have hEvalIntegral := fp81s21_pathIntegral_eval η
      (HRS.MS.R2Interp.s102_ell τ α) hηint
    have hEvalIntegral' :
        OscDual.coord (OscPath.at' (∫ ω, η ω ∂A.P) τ) α =
          ∫ ω, OscDual.coord (OscPath.at' (η ω) τ) α ∂A.P := by
      simpa only [HRS.MS.R2Interp.s102_ell_apply] using hEvalIntegral
    calc
      OscDual.coord (OscPath.at' (∫ ω, η ω ∂A.P) τ) α =
          ∫ ω, OscDual.coord (OscPath.at' (η ω) τ) α ∂A.P := hEvalIntegral'
      _ = ∫ ω, OscDual.coord (etaField u ω) α ∂A.P := by
        exact integral_congr_ae ((hηeval τ).mono fun ω hω => congrArg (fun z => OscDual.coord z α) hω)
      _ = ∫ ω, (OscDual.coord (zetaField u ω) α + OscDual.coord (biasField u) α) ∂A.P := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          congrArg (fun z => OscDual.coord z α) (hfield ω))
      _ = OscDual.coord (biasField u) α := by
        rw [integral_add hζcoordInt (integrable_const _), hζcoordMean]
        simp
  have hCenter : ζ =ᵐ[A.P] fun ω => η ω - ∫ ω', η ω' ∂A.P := by
    filter_upwards [hηcont, hζcont] with ω hωη hωζ
    have hmem : ∀ t : Set.Icc (0 : ℝ) H, b + (t : ℝ) ∈ Set.Icc (0 : ℝ) (b + H) := by
      intro t
      constructor
      · linarith [hb, t.2.1]
      · linarith [t.2.2]
    have hcη : Continuous fun t : Set.Icc (0 : ℝ) H => etaField (b + (t : ℝ)) ω :=
      hωη.comp_continuous (continuous_const.add continuous_subtype_val) hmem
    have hcζ : Continuous fun t : Set.Icc (0 : ℝ) H => zetaField (b + (t : ℝ)) ω :=
      hωζ.comp (continuous_const.add continuous_subtype_val)
    have hpathη : η ω =
        (⟨fun t : Set.Icc (0 : ℝ) H => etaField (b + (t : ℝ)) ω, hcη⟩ : OscPath p.d m H) := by
      change windowPathOf m H b (fun t => etaField t ω) = _
      unfold windowPathOf
      exact dif_pos hcη
    have hpathζ : ζ ω =
        (⟨fun t : Set.Icc (0 : ℝ) H => zetaField (b + (t : ℝ)) ω, hcζ⟩ : OscPath p.d m H) := by
      change windowPathOf m H b (fun t => zetaField t ω) = _
      unfold windowPathOf
      exact dif_pos hcζ
    apply ContinuousMap.ext
    intro τ
    apply OscDual.ext_hermiteCoeff
    intro α
    let u : ℝ := b + (τ : ℝ)
    have hu : 0 ≤ u := by dsimp [u]; linarith [hb, τ.2.1]
    letI : IsProbabilityMeasure (A.P.map (A.X (Real.toNNReal u))) := hmapprob u
    letI : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ u)) := hρprob u hu
    have hfield := congrArg (fun z => OscDual.coord z α)
      (fp81s21_etaField_eq_zeta_add_mean hm
        (A.P.map (A.X (Real.toNNReal u))) (A.X (Real.toNNReal u) ω)
        (HRS.Whole.withDensityReal (R.ρ u)) hN1)
    have hcoordMean := hMeanCoord τ α
    have hcoord : OscDual.coord (OscPath.at' (ζ ω) τ) α =
        OscDual.coord (OscPath.at' (η ω - ∫ ω', η ω' ∂A.P) τ) α := by
      rw [hpathζ, hpathη]
      change OscDual.coord (zetaField u ω) α =
        OscDual.coord (etaField u ω) α -
          OscDual.coord (OscPath.at' (∫ ω', η ω' ∂A.P) τ) α
      rw [hfield, OscDual.coord_add, hcoordMean]
      ring
    rw [OscDual.coord_eq_mul, OscDual.coord_eq_mul] at hcoord
    exact mul_left_cancel₀ (Real.rpow_pos_of_pos (HRS.Whole.oscEv_pos α) _).ne' hcoord
  exact ⟨hηint, by simpa [η, ζ] using hCenter⟩

/-- A Gaussian realization has a Bochner-integrable, zero-mean shifted window. -/
theorem fp81s21_gaussian_window_integral_zero
    (p : Parameters) {δ H b : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) (hH : 0 < H) (hb : 0 ≤ b) :
    Integrable
        (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) H b G.Z) G.P ∧
      (∫ ω, processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) H b G.Z ω ∂G.P) = 0 := by
  let C := r26t3_coeff R
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let C₀ := HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
  have hZ := G.evolution (b + H)
  obtain ⟨hWmeas, hWcenter, hWmem⟩ := HRS.MS.S111BD.s111_shifted_window_gaussian
    p.d G.P C m p.β⁻¹ H b (b + H) C₀ G.Z hZ hH hb le_rfl
  let W : G.Ω → OscPath p.d m H := processWindow m H b G.Z
  have hWint : Integrable W G.P := hWmem.integrable (by norm_num)
  have hzero : ∀ L : StrongDual ℝ (OscPath p.d m H),
      L (∫ ω, W ω ∂G.P) = 0 := by
    intro L
    calc L (∫ ω, W ω ∂G.P)
        = ∫ ω, L (W ω) ∂G.P := (ContinuousLinearMap.integral_comp_comm L hWint).symm
      _ = ∫ z, L z ∂(law G.P W) := by
        symm
        exact integral_map hWmeas L.continuous.aestronglyMeasurable
      _ = 0 := hWcenter.2 L
  have hmean : (∫ ω, W ω ∂G.P) = 0 := by
    by_contra hv
    obtain ⟨L, -, hL⟩ := exists_dual_vector'' ℝ (∫ ω, W ω ∂G.P)
    have hL' : L (∫ ω, W ω ∂G.P) = ‖∫ ω, W ω ∂G.P‖ := by simpa using hL
    have hz := hzero L
    rw [hL'] at hz
    have hpos : 0 < ‖∫ ω, W ω ∂G.P‖ := norm_pos_iff.mpr hv
    exact (ne_of_gt hpos) hz
  exact ⟨hWint, by simpa [W] using hmean⟩

/-- Conditional recent-window transfer: if the physical particle window is the
Bochner centering of its raw fluctuation path, restriction to any subwindow
preserves the factor-two raw `W₁` envelope. -/
theorem fp81s21_centered_restrict_of_path_identity
    {d : ℕ} {m H T u : ℝ} (hu : 0 ≤ u) (hU : u + T ≤ H)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (Y : Ω → OscPath d m H) (ζ : Ω → OscPath d m H)
    (Z : Ω' → OscPath d m H)
    (hY : Integrable Y P) (hZ : Integrable Z Q)
    (hZ0 : ∫ ω, Z ω ∂Q = 0)
    (hCenter : ζ =ᵐ[P] fun ω => Y ω - ∫ ω', Y ω' ∂P) :
    wassersteinE 1
      (law P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction hu hU (ζ ω)))
      (law Q (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction hu hU (Z ω))) ≤
      2 * wassersteinE 1 (law P Y) (law Q Z) := by
  have hYae : AEMeasurable Y P := hY.aemeasurable
  have hZae : AEMeasurable Z Q := hZ.aemeasurable
  have hζae : AEMeasurable ζ P := by
    have hcenterae : AEMeasurable (fun ω => Y ω - ∫ ω', Y ω' ∂P) P :=
      hYae.sub_const _
    exact hcenterae.congr hCenter.symm
  have hcentered := fp81s21_wasserstein_center_bounded Y Z hY hZ hZ0
  have hpathlaw : law P ζ =
      law P (fun ω => Y ω - ∫ ω', Y ω' ∂P) := by
    exact Measure.map_congr hCenter
  have hraw : wassersteinE 1 (law P ζ) (law Q Z) ≤
      2 * wassersteinE 1 (law P Y) (law Q Z) := by
    rw [hpathlaw]
    exact hcentered
  exact (fp81s21_law_restrict_wasserstein hu hU ζ Z hζae hZae).trans hraw

theorem fp81s21_recent_geometry {a₀ L T : ℝ}
    (ha₀ : 0 ≤ a₀) (hL : 0 < L) (hT : 0 < T) :
    0 ≤ a₀ - max (a₀ - L) 0 ∧
      a₀ - max (a₀ - L) 0 + T ≤ L + T := by
  obtain ⟨hu, hwindow⟩ := fp81s21_recentWindowRestriction ha₀ hL hT
  have hTmem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hend := (hwindow T hTmem).1
  exact ⟨hu, hend.2⟩

/-- The fixed-radius leading envelope transfers to the exactly centered particle
window, then to its recent restriction. The common radius is selected before
`L`, and all subsequent constants retain wR16's quantifier order. -/
theorem fp81s21_centered_recentWindow (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
      ∀ R : Trajectory p δ, ∀ L : ℝ, (hL : 0 < L) →
        ∃ C₀ C : ℝ, 0 ≤ C ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ G : GaussianRealization R,
            ∀ a₀ : ℝ, (ha₀ : 0 ≤ a₀) →
              wassersteinE 1
                (law A.P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
                  (fp81s21_recent_geometry ha₀ hL p.hT).1
                  (fp81s21_recent_geometry ha₀ hL p.hT).2
                  (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T)
                    (max (a₀ - L) 0) A.P A.X ω)))
                (law G.P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
                  (fp81s21_recent_geometry ha₀ hL p.hT).1
                  (fp81s21_recent_geometry ha₀ hL p.hT).2
                  (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T)
                    (max (a₀ - L) 0) G.Z ω))) ≤
                2 * ENNReal.ofReal (C * (Real.sqrt N * deltaN p.d p.s N +
                  Real.sqrt (localizationRate p.d p.s C₀ N) + jN p.d p.s p.γ N)) := by
  obtain ⟨δ0, hδ0, hraw⟩ := fp81s21_leadingAdapter2 p
  refine ⟨δ0, hδ0, ?_⟩
  intro δ hδ hδle R L hL
  obtain ⟨C₀, C, hC, hraw⟩ := hraw δ hδ hδle R L hL
  refine ⟨C₀, C, hC, ?_⟩
  intro N hN A G a₀ ha₀
  let b : ℝ := max (a₀ - L) 0
  have hb : 0 ≤ b := by dsimp [b]; exact le_max_right _ _
  have hH : 0 < L + p.T := by linarith [hL, p.hT]
  have hgeo := fp81s21_recent_geometry ha₀ hL p.hT
  have hparticle := fp81s21_particle_window_centered p R hN A hH hb
  have hgaussian := fp81s21_gaussian_window_integral_zero p R G hH hb
  have hcenter := fp81s21_centered_restrict_of_path_identity
    hgeo.1 hgeo.2
    (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) b
      (Real.sqrt N) A.X R.ρ)
    (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) b A.P A.X)
    (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) b G.Z)
    hparticle.1 hgaussian.1 hgaussian.2 hparticle.2
  have hrawbound := hraw N hN A G b hb
  calc
    wassersteinE 1
        (law A.P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
          hgeo.1 hgeo.2
          (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) b A.P A.X ω)))
        (law G.P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction
          hgeo.1 hgeo.2
          (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) b G.Z ω)))
        ≤ 2 * wassersteinE 1
          (law A.P (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) b
            (Real.sqrt N) A.X R.ρ))
          (law G.P (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) b G.Z)) := hcenter
    _ ≤ 2 * ENNReal.ofReal (C * (Real.sqrt N * deltaN p.d p.s N +
          Real.sqrt (localizationRate p.d p.s C₀ N) + jN p.d p.s p.γ N)) := by
      gcongr

#print axioms fp81s21_gaussian_window_integral_zero
#print axioms fp81s21_centered_restrict_of_path_identity
#print axioms fp81s21_recent_geometry
#print axioms fp81s21_centered_recentWindow
#print axioms fp81s21_zetaField_coord_integral_zero
#print axioms fp81s21_particle_window_centered

end HRS.Fp81.S21

end
