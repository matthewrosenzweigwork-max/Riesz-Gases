import HRS.MS.Fp81S21GaussG5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.S111X2 HRS.MS.ProClosureS111

theorem fp81s21_g5_observation_increment_second
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (G : GaussianRealization R) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    Integrable
        (fun ω => |OscDual.eval (G.Z u ω) φ - OscDual.eval (G.Z v ω) φ| ^ 2) G.P ∧
      (∫ ω, |OscDual.eval (G.Z u ω) φ - OscDual.eval (G.Z v ω) φ| ^ 2 ∂G.P) =
        HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ +
          HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ v v φ φ -
            2 * HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u v φ φ := by
  let T : ℝ := max u v + 1
  let times : Fin 2 → ℝ := fun i => if i = 0 then u else v
  let X : G.Ω → ℝ := fun ω => OscDual.eval (G.Z u ω) φ
  let Y : G.Ω → ℝ := fun ω => OscDual.eval (G.Z v ω) φ
  let V : G.Ω → EuclideanSpace ℝ (Fin 2) := fun ω =>
    WithLp.toLp 2 (fun i => OscDual.eval (G.Z (times i) ω) φ)
  let S : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j =>
    HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ
      (times i) (times j) φ φ
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S
  have hT : 0 < T := by
    dsimp [T]
    linarith [le_max_left u v]
  have hTu : u ≤ T := by
    dsimp [T]
    linarith [le_max_left u v]
  have hTv : v ≤ T := by
    dsimp [T]
    linarith [le_max_right u v]
  have htimes : ∀ i : Fin 2, times i ∈ Icc (0 : ℝ) T := by
    intro i
    fin_cases i
    · simpa [times] using (show u ∈ Icc (0 : ℝ) T from ⟨hu, hTu⟩)
    · simpa [times] using (show v ∈ Icc (0 : ℝ) T from ⟨hv, hTv⟩)
  have hφs : ∀ i : Fin 2, IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    fun _ => hφ
  have hZU := G.evolution T
  have hLaw : G.P.map V = μ := by
    simpa [V, μ, S, times, HRS.MS.S21E.s21eCov,
      HRS.Whole.linearGaussianCov, r26t3_coeff, r26t3_mu] using
        hZU.gaussian 2 times (fun _ => φ) htimes hφs
  have htime0 : ∀ i : Fin 2, 0 ≤ times i := by
    intro i
    fin_cases i <;> simp [times, hu, hv]
  have hgram : ∀ i j : Fin 2,
      inner ℝ (fp81s21_combinedFeature p R hK (times i) φ)
        (fp81s21_combinedFeature p R hK (times j) φ) = S i j := by
    intro i j
    simpa [S] using
      (fp81s21_combinedFeature_gram p hδ hδhalf R hK
        (htime0 i) (htime0 j) hφ hφ)
  have hS : S.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      rw [Matrix.transpose_apply]
      calc
        S j i = inner ℝ
            (fp81s21_combinedFeature p R hK (times j) φ)
            (fp81s21_combinedFeature p R hK (times i) φ) := (hgram j i).symm
        _ = inner ℝ
            (fp81s21_combinedFeature p R hK (times i) φ)
            (fp81s21_combinedFeature p R hK (times j) φ) := real_inner_comm _ _
        _ = S i j := hgram i j
    · intro x
      let F₀ := fp81s21_combinedFeature p R hK (times 0) φ
      let F₁ := fp81s21_combinedFeature p R hK (times 1) φ
      have h00 : S 0 0 = inner ℝ F₀ F₀ := (hgram 0 0).symm
      have h01 : S 0 1 = inner ℝ F₀ F₁ := (hgram 0 1).symm
      have h10 : S 1 0 = inner ℝ F₁ F₀ := (hgram 1 0).symm
      have h11 : S 1 1 = inner ℝ F₁ F₁ := (hgram 1 1).symm
      have hq : dotProduct x (S.mulVec x) =
          inner ℝ ((x 0) • F₀ + (x 1) • F₁)
            ((x 0) • F₀ + (x 1) • F₁) := by
        calc
          dotProduct x (S.mulVec x) =
              x 0 * (S 0 0 * x 0 + S 0 1 * x 1) +
                x 1 * (S 1 0 * x 0 + S 1 1 * x 1) := by
            simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
          _ = inner ℝ ((x 0) • F₀ + (x 1) • F₁)
                ((x 0) • F₀ + (x 1) • F₁) := by
            rw [h00, h01, h10, h11]
            simp only [inner_add_left, inner_add_right,
              real_inner_smul_left, real_inner_smul_right]
            ring
      have hx : star x = x := by
        ext i
        simp
      change 0 ≤ dotProduct (star x) (S.mulVec x)
      rw [hx, hq]
      exact real_inner_self_nonneg
  have hSsymm : S 1 0 = S 0 1 := by
    calc
      S 1 0 = inner ℝ
          (fp81s21_combinedFeature p R hK (times 1) φ)
          (fp81s21_combinedFeature p R hK (times 0) φ) := (hgram 1 0).symm
      _ = inner ℝ
          (fp81s21_combinedFeature p R hK (times 0) φ)
          (fp81s21_combinedFeature p R hK (times 1) φ) := real_inner_comm _ _
      _ = S 0 1 := hgram 0 1
  have hGμ : HRS.IsCenteredGaussian μ := by
    dsimp [μ]
    exact HRS.MS.S111BD.s111_isCenteredGaussian_mvg 2 S
  letI : IsGaussian μ := hGμ.1
  have hcoord0 : MemLp (fun z : EuclideanSpace ℝ (Fin 2) => z 0) 2 μ :=
    HRS.MS.R26T3.s21k2_p07_coord_memLp μ 0
  have hcoord1 : MemLp (fun z : EuclideanSpace ℝ (Fin 2) => z 1) 2 μ :=
    HRS.MS.R26T3.s21k2_p07_coord_memLp μ 1
  have h00 : Integrable
      (fun z : EuclideanSpace ℝ (Fin 2) => z 0 * z 0) μ :=
    hcoord0.integrable_mul hcoord0
  have h11 : Integrable
      (fun z : EuclideanSpace ℝ (Fin 2) => z 1 * z 1) μ :=
    hcoord1.integrable_mul hcoord1
  have h01 : Integrable
      (fun z : EuclideanSpace ℝ (Fin 2) => z 0 * z 1) μ :=
    hcoord0.integrable_mul hcoord1
  have h10 : Integrable
      (fun z : EuclideanSpace ℝ (Fin 2) => z 1 * z 0) μ :=
    hcoord1.integrable_mul hcoord0
  let q00 : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => z 0 * z 0
  let q11 : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => z 1 * z 1
  let q01 : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => z 0 * z 1
  let q10 : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => z 1 * z 0
  have hq00 : Integrable q00 μ := by simpa [q00] using h00
  have hq11 : Integrable q11 μ := by simpa [q11] using h11
  have hq01 : Integrable q01 μ := by simpa [q01] using h01
  have hq10 : Integrable q10 μ := by simpa [q10] using h10
  have hmix (i j : Fin 2) :
      ∫ z : EuclideanSpace ℝ (Fin 2), z i * z j ∂μ = S i j := by
    dsimp [μ]
    exact HRS.MS.S111X2.s111x2_gauss_mixed S hS i j
  have hquad :
      ∫ z : EuclideanSpace ℝ (Fin 2), (z 0 - z 1) ^ 2 ∂μ =
        S 0 0 + S 1 1 - S 0 1 - S 1 0 := by
    calc
      _ = ∫ z : EuclideanSpace ℝ (Fin 2),
          ((q00 + q11) z - (q01 + q10) z) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp [q00, q11, q01, q10]
          ring
      _ = _ := by
        rw [integral_sub (hq00.add hq11) (hq01.add hq10)]
        change (∫ z, q00 z + q11 z ∂μ) -
          (∫ z, q01 z + q10 z ∂μ) = _
        rw [integral_add hq00 hq11, integral_add hq01 hq10,
          hmix 0 0, hmix 1 1, hmix 0 1, hmix 1 0]
        ring
  have hVm : Measurable V := by
    apply (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
    exact measurable_pi_iff.2 fun i => by
      fin_cases i
      · have hX : Measurable X := by
          have heq : X = fun ω => HRS.MS.ProClosureS111.gaussianOscEval
              (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d
                (wholeSpaceIndex p.d : ℝ)) (G.Z u ω) := by
            funext ω
            exact (HRS.MS.ProClosureS111.gaussianOscEval_apply ⟨φ, hφ⟩ _).symm
          rw [heq]
          exact (HRS.MS.ProClosureS111.gaussianOscEval ⟨φ, hφ⟩).continuous.measurable.comp
            (hZU.meas u)
        simpa [V, X, times] using hX
      · have hY : Measurable Y := by
          have heq : Y = fun ω => HRS.MS.ProClosureS111.gaussianOscEval
              (⟨φ, hφ⟩ : HRS.MS.S111X1.oscSub p.d
                (wholeSpaceIndex p.d : ℝ)) (G.Z v ω) := by
            funext ω
            exact (HRS.MS.ProClosureS111.gaussianOscEval_apply ⟨φ, hφ⟩ _).symm
          rw [heq]
          exact (HRS.MS.ProClosureS111.gaussianOscEval ⟨φ, hφ⟩).continuous.measurable.comp
            (hZU.meas v)
        simpa [V, Y, times] using hY
  have hGvec : HRS.IsCenteredGaussian (G.P.map V) := by
    rw [hLaw]
    exact hGμ
  letI : IsGaussian (G.P.map V) := hGvec.1
  have hVmemMap : MemLp (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      2 (G.P.map V) := IsGaussian.memLp_two_id
  have hVmem : MemLp V 2 G.P :=
    (memLp_map_measure_iff aestronglyMeasurable_id hVm.aemeasurable).1 hVmemMap
  have hXmem : MemLp X 2 G.P := by
    have hmap : MemLp (fun z : EuclideanSpace ℝ (Fin 2) => z 0) 2
        (G.P.map V) := HRS.MS.R26T3.s21k2_p07_coord_memLp (G.P.map V) 0
    have hf : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 2) => z 0) (G.P.map V) := by
      exact Measurable.aestronglyMeasurable
        ((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.measurable)
    have h := (memLp_map_measure_iff hf
      hVm.aemeasurable).1 hmap
    have heq : (fun ω => (V ω).ofLp 0) = X := by
      funext ω
      simp [X, V, times]
    change MemLp (fun ω => (V ω).ofLp 0) 2 G.P at h
    rw [← heq]
    exact h
  have hYmem : MemLp Y 2 G.P := by
    have hmap : MemLp (fun z : EuclideanSpace ℝ (Fin 2) => z 1) 2
        (G.P.map V) := HRS.MS.R26T3.s21k2_p07_coord_memLp (G.P.map V) 1
    have hf : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 2) => z 1) (G.P.map V) := by
      exact Measurable.aestronglyMeasurable
        ((EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.measurable)
    have h := (memLp_map_measure_iff hf
      hVm.aemeasurable).1 hmap
    have heq : (fun ω => (V ω).ofLp 1) = Y := by
      funext ω
      simp [Y, V, times]
    change MemLp (fun ω => (V ω).ofLp 1) 2 G.P at h
    rw [← heq]
    exact h
  have hDmem : MemLp (fun ω => X ω - Y ω) 2 G.P := hXmem.sub hYmem
  have hDint : Integrable
      (fun ω => |X ω - Y ω| ^ 2) G.P := by
    simpa only [Real.norm_eq_abs] using
      hDmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hMapMoment :
      ∫ z : EuclideanSpace ℝ (Fin 2), (z 0 - z 1) ^ 2 ∂μ =
        ∫ ω, |X ω - Y ω| ^ 2 ∂G.P := by
    have hfcont : Continuous
        (fun z : EuclideanSpace ℝ (Fin 2) => (z 0 - z 1) ^ 2) := by fun_prop
    rw [← hLaw, integral_map hVm.aemeasurable
      (show AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 2) => (z 0 - z 1) ^ 2)
        (G.P.map V) from hfcont.aestronglyMeasurable)]
    simp [V, X, Y, times, sq_abs]
  refine ⟨?_, ?_⟩
  · simpa [X, Y] using hDint
  · rw [← hMapMoment, hquad, hSsymm]
    simp [S, times]
    ring

/-- The variance of the representative's actual two-time coordinate
increment is the squared combined-feature increment. -/
theorem fp81s21_g5_coord_increment_second
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    (E : HRS.MS.R26T6.r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (G : GaussianRealization R) (q : ℝ → G.Ω → HRS.MS.R26T6.r26t6_Coeff)
    (M : ℝ) (hq : fp81s21_MomentRep E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) q M)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (j : ℕ) :
    Integrable (fun ω => (q u ω j - q v ω j)^2) G.P ∧
    (∫ ω, (q u ω j - q v ω j)^2 ∂G.P) =
      ‖fp81s21_combinedFeature p R hK u (E.test j) -
        fp81s21_combinedFeature p R hK v (E.test j)‖^2 := by
  let φ : Euc p.d → ℝ := E.test j
  have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
    r2Test_isOscTest _ (E.test_smooth j)
  have hmom := fp81s21_g5_observation_increment_second p hδ hδhalf R hK G u v hu hv φ hφ
  have hgram :
      ‖fp81s21_combinedFeature p R hK u φ -
          fp81s21_combinedFeature p R hK v φ‖ ^ 2 =
        HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u u φ φ +
          HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ v v φ φ -
            2 * HRS.MS.S21E.s21eCov p.d p.s p.a p.β p.γ R.ρ u v φ φ := by
    rw [norm_sub_sq_real,
      ← real_inner_self_eq_norm_sq (fp81s21_combinedFeature p R hK u φ),
      ← real_inner_self_eq_norm_sq (fp81s21_combinedFeature p R hK v φ),
      fp81s21_combinedFeature_gram p hδ hδhalf R hK hu hu hφ hφ,
      fp81s21_combinedFeature_gram p hδ hδhalf R hK hv hv hφ hφ,
      fp81s21_combinedFeature_gram p hδ hδhalf R hK hu hv hφ hφ]
    ring
  have hcoord (w : ℝ) (hw : 0 ≤ w) :
      ∀ᵐ ω ∂G.P, q w ω j = OscDual.eval (G.Z w ω) φ := by
    filter_upwards [(hq.2 w hw).2.2] with ω hω
    rw [← fp81s21_chartAction_test_coordinate E (q w ω) j]
    exact hω.1 (E.test j) (E.test_smooth j)
  have hae : (fun ω => (q u ω j - q v ω j)^2) =ᵐ[G.P]
      (fun ω => |OscDual.eval (G.Z u ω) φ - OscDual.eval (G.Z v ω) φ|^2) := by
    filter_upwards [hcoord u hu, hcoord v hv] with ω hu' hv'
    rw [hu', hv', sq_abs]
  refine ⟨hmom.1.congr hae.symm, ?_⟩
  calc
    _ = ∫ ω, |OscDual.eval (G.Z u ω) φ - OscDual.eval (G.Z v ω) φ|^2 ∂G.P :=
      integral_congr_ae hae
    _ = _ := hmom.2.trans hgram.symm

#print axioms fp81s21_g5_observation_increment_second
#print axioms fp81s21_g5_coord_increment_second
end HRS.Fp81.S21
end
