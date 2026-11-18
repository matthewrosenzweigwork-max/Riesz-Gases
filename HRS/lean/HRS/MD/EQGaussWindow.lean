import HRS.Energy.StaticLimitTiltedGauss
import HRS.Main.GFB1Aux1
import HRS.Sections.Sec3
import HRS.Main.Headline

/-!
# EQ-GAUSS (b): `eq_gauss_window_law`

The window law of a stationary Gaussian field does not depend on the realisation or on the window start: the finite-dimensional
laws against smooth tests (`multivariateGaussian 0 (stationaryLagCov ..)`, depending only on the time lags) determine the law on
`C([0,T];E_M)` (coordinates `NegSobolev.eval · (realMode k)` generate the Borel σ-algebra; cylinder sets form a π-system).
The cylinder lemmas `eqgw_*` are copies of `HRS.AdjK.adjkd_*` (`HRS/Sections/AdjKDAux2.lean`), reproved here to avoid importing the
sorried `AdjKSpec`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQGaussWindow

open HRS.Uniform

variable {d : ℕ}

/-- A function into `E_m` with measurable coordinates is measurable. -/
theorem eqgw_measurable_of_coord {α : Type*} {mα : MeasurableSpace α} {m : ℝ}
    (F : α → NegSobolev d m) (hc : ∀ k, Measurable fun a => NegSobolev.coord (F a) k) :
    Measurable F := by
  have hlim : ∀ X : α, Tendsto
      (fun s : Finset (NonzeroLattice d) => (∑ k ∈ s,
        (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
          (NegSobolev.coord (F X) k))))
      atTop (𝓝 (F X)) := by
    intro X
    exact lp.hasSum_single (p := 2) (by simp) (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F X)
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (NonzeroLattice d)))
    (f := fun (s : Finset (NonzeroLattice d)) (X : α) =>
      (∑ k ∈ s, (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
        (NegSobolev.coord (F X) k)))) (fun s => ?_) (tendsto_pi_nhds.2 hlim)
  refine Finset.measurable_sum _ fun k _ => ?_
  have hcont : Continuous (fun a : ℝ => (show NegSobolev d m from
      lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k a)) :=
    (lp.isometry_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) k).continuous
  exact hcont.measurable.comp (hc k)

theorem eqgw_isSmooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) :=
  StaticLimitAux.isSmooth_realMode' k

/-- Pairing with the real mode `e_k` is the Fourier coefficient. -/
theorem eqgw_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · have : Torus.funRealCoeff (Torus.realMode k) k = 1 := by
      unfold Torus.funRealCoeff
      simpa using Torus.realMode_orthonormal k k
    rw [this, mul_one]
  · intro l hl
    have : Torus.funRealCoeff (Torus.realMode k) l = 0 := by
      unfold Torus.funRealCoeff
      have := Torus.realMode_orthonormal l k
      rw [if_neg hl] at this
      exact this
    rw [this, mul_zero]

theorem eqgw_eval_continuous {m : ℝ} {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous fun F : NegSobolev d m => NegSobolev.eval F φ := by
  have hs := GF.gfb1_smooth_sq hφ m
  set C : ℝ := Real.sqrt (∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) with hC
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal C) fun F G => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, ← GF.gf_eval_sub_proof F G hφ]
  refine (NegSobolev.abs_eval_le (F - G) φ hs).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)

/-- The finite-dimensional functional: pairings with smooth tests at given times. -/
def eqgwG {m T : ℝ} {p : ℕ} (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ)
    (w : PathSpace d m T) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => NegSobolev.eval (w.at' (ts a)) (φ a)

theorem eqgw_at_continuous {m T : ℝ} (t : Set.Icc (0 : ℝ) T) :
    Continuous fun w : PathSpace d m T => w.at' t := by
  have : Continuous fun w : C(Set.Icc (0 : ℝ) T, NegSobolev d m) => w t :=
    continuous_eval_const t
  exact this

theorem eqgwG_continuous {m T : ℝ} {p : ℕ} (ts : Fin p → Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    Continuous (eqgwG (m := m) ts φ) := by
  unfold eqgwG
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a => ?_)
  exact (eqgw_eval_continuous (hφ a)).comp (eqgw_at_continuous (ts a))


/-- Cylinder sets of `PathSpace`: preimages of Borel sets under finite-dimensional pairings with smooth tests. -/
def eqgwCyl (d : ℕ) (m T : ℝ) : Set (Set (PathSpace d m T)) :=
  {S | ∃ (p : ℕ) (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ)
      (B : Set (EuclideanSpace ℝ (Fin p))),
    (∀ a, Torus.IsSmooth (φ a)) ∧ MeasurableSet B ∧ S = eqgwG ts φ ⁻¹' B}

theorem eqgw_proj_continuous {n : ℕ} (p : ℕ) (f : Fin p → Fin n) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) =>
      (WithLp.toLp 2 fun a => x (f a) : EuclideanSpace ℝ (Fin p)) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a => ?_)
  exact (EuclideanSpace.proj (f a)).continuous

theorem eqgwCyl_isPiSystem {m T : ℝ} : IsPiSystem (eqgwCyl d m T) := by
  rintro S1 ⟨p, ts, φ, B, hφ, hB, rfl⟩ S2 ⟨q, ts', φ', B', hφ', hB', rfl⟩ -
  let π1 : EuclideanSpace ℝ (Fin (p + q)) → EuclideanSpace ℝ (Fin p) :=
    fun x => WithLp.toLp 2 fun a => x (Fin.castAdd q a)
  let π2 : EuclideanSpace ℝ (Fin (p + q)) → EuclideanSpace ℝ (Fin q) :=
    fun x => WithLp.toLp 2 fun a => x (Fin.natAdd p a)
  have h1 : Measurable π1 := (eqgw_proj_continuous p (Fin.castAdd q)).measurable
  have h2 : Measurable π2 := (eqgw_proj_continuous q (Fin.natAdd p)).measurable
  refine ⟨p + q, Fin.append ts ts', Fin.append φ φ', π1 ⁻¹' B ∩ π2 ⁻¹' B', ?_, ?_, ?_⟩
  · intro a
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a
    · simpa using hφ i
    · simpa using hφ' i
  · exact (h1 hB).inter (h2 hB')
  · ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, π1, π2, eqgwG]
    simp [Fin.append_left, Fin.append_right]

/-- Type synonym carrying the σ-algebra generated by the cylinder sets. -/
def EqgwCylSpace (d : ℕ) (m T : ℝ) : Type := PathSpace d m T

instance eqgwCylSpace_ms {m T : ℝ} : MeasurableSpace (EqgwCylSpace d m T) :=
  MeasurableSpace.generateFrom (eqgwCyl d m T)

theorem eqgw_cyl_measurable {m T : ℝ} {p : ℕ} (ts : Fin p → Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    Measurable (fun w : EqgwCylSpace d m T => eqgwG (m := m) ts φ (show PathSpace d m T from w)) := by
  intro B hB
  exact MeasurableSpace.measurableSet_generateFrom ⟨p, ts, φ, B, hφ, hB, rfl⟩

theorem eqgw_borel_eq_generateFrom {m T : ℝ} :
    (inferInstance : MeasurableSpace (PathSpace d m T)) =
      MeasurableSpace.generateFrom (eqgwCyl d m T) := by
  refine le_antisymm ?_ ?_
  · -- Borel ≤ σ(cylinders)
    have hid : Measurable (fun w : EqgwCylSpace d m T => (show PathSpace d m T from w)) := by
      refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
      refine eqgw_measurable_of_coord _ fun k => ?_
      have hk : ∀ w : EqgwCylSpace d m T,
          NegSobolev.coord ((show PathSpace d m T from w).at' t) k =
            (Lattice.jp k.1 ^ m)⁻¹ * (eqgwG (m := m) (fun _ : Fin 1 => t)
              (fun _ => Torus.realMode k) (show PathSpace d m T from w)) 0 := by
        intro w
        have e : (eqgwG (m := m) (fun _ : Fin 1 => t) (fun _ => Torus.realMode k)
            (show PathSpace d m T from w)) 0 =
            NegSobolev.fourierCoeff ((show PathSpace d m T from w).at' t) k := by
          simp [eqgwG, eqgw_eval_realMode]
        rw [e]
        unfold NegSobolev.fourierCoeff
        have hp : Lattice.jp k.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos (Torus.jp_pos _) _).ne'
        field_simp
      have hmeas : Measurable fun w : EqgwCylSpace d m T => (Lattice.jp k.1 ^ m)⁻¹ *
          (eqgwG (m := m) (fun _ : Fin 1 => t) (fun _ => Torus.realMode k)
            (show PathSpace d m T from w)) 0 := by
        refine Measurable.const_mul ?_ _
        have := eqgw_cyl_measurable (m := m) (fun _ : Fin 1 => t) (fun _ => Torus.realMode k)
          (fun _ => eqgw_isSmooth_realMode k)
        exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.measurable.comp this
      convert hmeas using 1
      funext w
      exact hk w
    intro s hs
    exact hid hs
  · refine MeasurableSpace.generateFrom_le ?_
    rintro S ⟨p, ts, φ, B, hφ, hB, rfl⟩
    exact (eqgwG_continuous ts φ hφ).measurable hB

theorem eqgw_ext_of_fidi {m T : ℝ} (μ ν : Measure (PathSpace d m T)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ (p : ℕ) (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ),
      (∀ a, Torus.IsSmooth (φ a)) → μ.map (eqgwG ts φ) = ν.map (eqgwG ts φ)) : μ = ν := by
  refine ext_of_generate_finite (eqgwCyl d m T) eqgw_borel_eq_generateFrom eqgwCyl_isPiSystem ?_
    (by simp)
  rintro S ⟨p, ts, φ, B, hφ, hB, rfl⟩
  have hm := (eqgwG_continuous (m := m) ts φ hφ).measurable
  have := congrArg (fun κ => κ B) (h p ts φ hφ)
  simpa [Measure.map_apply hm hB] using this


/-- `stationaryLagCov` only depends on the time lags. -/
theorem eqgw_lagCov_shift (s β : ℝ) (D : DynData d) (ρβ : Torus d → ℝ) {p : ℕ}
    (τ : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (a : ℝ) :
    PDE.stationaryLagCov d s β D ρβ (fun i => a + τ i) φ = PDE.stationaryLagCov d s β D ρβ τ φ := by
  unfold PDE.stationaryLagCov
  ext i j
  simp only [Matrix.of_apply, add_le_add_iff_left, add_sub_add_left_eq_sub]

/-- On a trajectory continuous on `[0,∞)` the window path is the honest path. -/
theorem eqgw_windowPath_at {M : ℝ} (T a : ℝ) (ha : 0 ≤ a) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d M)
    (ω : Ω) (hc : ContinuousOn (fun t => Z t ω) (Set.Ici 0)) (t : Set.Icc (0 : ℝ) T) :
    (Main.windowPath M T a Z ω).at' t = Z (a + t) ω := by
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => Z (a + (t : ℝ)) ω := by
    refine hc.comp_continuous (by fun_prop) (fun t => ?_)
    exact Set.mem_Ici.2 (add_nonneg ha t.2.1)
  have h : Main.windowPath M T a Z ω = (⟨fun t : Set.Icc (0 : ℝ) T => Z (a + (t : ℝ)) ω, hcont⟩ :
      C(Set.Icc (0 : ℝ) T, NegSobolev d M)) := by
    unfold Main.windowPath toPath
    exact dif_pos hcont
  rw [h]
  rfl

/-- Finite-dimensional marginals and a.e.-measurability of the window path of a stationary Gaussian field. -/
theorem eqgw_fidi (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ) (M T : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d M)
    (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ M Z) (a : ℝ) (ha : 0 ≤ a) :
    AEMeasurable (Main.windowPath M T a Z) P ∧
    ∀ (p : ℕ) (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ),
      (∀ i, Torus.IsSmooth (φ i)) →
      (P.map (Main.windowPath M T a Z)).map (eqgwG ts φ) =
        ProbabilityTheory.multivariateGaussian 0
          (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ (fun i => a + (ts i : ℝ)) φ) := by
  classical
  have hnull : P {ω | ¬ ContinuousOn (fun t => Z t ω) (Set.Ici 0)} = 0 := ae_iff.1 hZ.cont
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  set f : Ω → PathSpace d M T := Main.windowPath M T a Z with hf
  set f' : Ω → PathSpace d M T := fun ω => if ω ∈ Nᶜ then f ω else 0 with hf'
  have hgood : ∀ ω ∈ Nᶜ, ContinuousOn (fun t => Z t ω) (Set.Ici 0) := by
    intro ω hω
    by_contra h
    exact hω (hNsub h)
  have hae : f =ᵐ[P] f' := by
    have : ∀ᵐ ω ∂P, ω ∈ Nᶜ := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [this] with ω hω
    show f ω = f' ω
    simp only [hf']
    exact (if_pos hω).symm
  -- the cylinder functionals along `f'`
  have hG' : ∀ (p : ℕ) (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ),
      (∀ i, Torus.IsSmooth (φ i)) →
      Measurable fun ω => eqgwG ts φ (f' ω) := by
    intro p ts φ hφ
    have hm : Measurable fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (Z (a + (ts i : ℝ)) ω) (φ i) :
        EuclideanSpace ℝ (Fin p)) := by
      refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i => ?_)
      exact (eqgw_eval_continuous (hφ i)).measurable.comp (hZ.meas _)
    have : (fun ω => eqgwG ts φ (f' ω)) = fun ω => if ω ∈ Nᶜ then
        (WithLp.toLp 2 fun i => NegSobolev.eval (Z (a + (ts i : ℝ)) ω) (φ i) :
          EuclideanSpace ℝ (Fin p)) else eqgwG ts φ (0 : PathSpace d M T) := by
      funext ω
      by_cases hω : ω ∈ Nᶜ
      · simp only [hf', if_pos hω]
        unfold eqgwG
        simp only [hf]
        congr 1
        funext i
        rw [eqgw_windowPath_at T a ha Z ω (hgood ω hω)]
      · simp only [hf', if_neg hω]
    rw [this]
    exact Measurable.ite hNm.compl hm measurable_const
  have hmeas' : Measurable f' := by
    have h1 : @Measurable _ _ _ (MeasurableSpace.generateFrom (eqgwCyl d M T)) f' := by
      refine measurable_generateFrom ?_
      rintro S ⟨p, ts, φ, B, hφ, hB, rfl⟩
      exact hG' p ts φ hφ hB
    exact h1.mono le_rfl (by rw [← eqgw_borel_eq_generateFrom])
  have hfm : AEMeasurable f P := hmeas'.aemeasurable.congr hae.symm
  refine ⟨hfm, ?_⟩
  intro p ts φ hφ
  have hGc := (eqgwG_continuous (m := M) ts φ hφ).measurable
  rw [AEMeasurable.map_map_of_aemeasurable hGc.aemeasurable hfm]
  have hrw : P.map (eqgwG ts φ ∘ f) = P.map (fun ω => (WithLp.toLp 2 fun i =>
      NegSobolev.eval (Z (a + (ts i : ℝ)) ω) (φ i) : EuclideanSpace ℝ (Fin p))) := by
    refine Measure.map_congr ?_
    have : ∀ᵐ ω ∂P, ω ∈ Nᶜ := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [this] with ω hω
    unfold eqgwG
    simp only [Function.comp_apply, hf]
    congr 1
    funext i
    rw [eqgw_windowPath_at T a ha Z ω (hgood ω hω)]
  rw [hrw]
  exact hZ.gaussian p (fun i => a + (ts i : ℝ)) φ (fun i => add_nonneg ha (ts i).2.1) hφ

theorem eq_gauss_window_law_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ) (M T : ℝ) (hT : 0 ≤ T)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → Ω → NegSobolev d M) (Z' : ℝ → Ω' → NegSobolev d M)
    (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ M Z)
    (hZ' : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ M Z')
    (a a' : ℝ) (ha : 0 ≤ a) (ha' : 0 ≤ a') :
    law P (Main.windowPath M T a Z) = law P' (Main.windowPath M T a' Z') := by
  obtain ⟨hm1, hf1⟩ := eqgw_fidi hd hs0 hsd V hβ ρβ M T P Z hZ a ha
  obtain ⟨hm2, hf2⟩ := eqgw_fidi hd hs0 hsd V hβ ρβ M T P' Z' hZ' a' ha'
  haveI : IsProbabilityMeasure (P.map (Main.windowPath M T a Z)) := (Measure.isProbabilityMeasure_map_iff hm1).2 inferInstance
  haveI : IsProbabilityMeasure (P'.map (Main.windowPath M T a' Z')) := (Measure.isProbabilityMeasure_map_iff hm2).2 inferInstance
  refine eqgw_ext_of_fidi _ _ fun p ts φ hφ => ?_
  rw [hf1 p ts φ hφ, hf2 p ts φ hφ, eqgw_lagCov_shift, eqgw_lagCov_shift]

end HRS.MD.EQGaussWindow
