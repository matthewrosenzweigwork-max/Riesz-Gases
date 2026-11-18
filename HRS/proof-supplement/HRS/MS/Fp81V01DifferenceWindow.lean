import HRS.MS.Fp81V01DifferenceMoments
import HRS.MS.ProClosureS111WindowRestriction
import HRS.MS.ProClosureS111GaussianSpace
import HRS.MS.ProClosureS111PathMoments
import HRS.MS.S111X2Aux38
import HRS.MS.S111X2Aux35
import HRS.Sections.IIDAux3

/-! The fourth moment of the actual moving-window difference, with its
sharp exponential decay in the window start. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.S111T HRS.MS.R26T6
open HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.S111X2
open HRS.MC.QRSpec.Wick

private theorem fp81v01_difference_qrpw_hilbert_fourth
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {m : ℝ} (G : Submodule ℝ (Ω → ℝ)) (hG : QrpwG4 P G)
    (X : Ω → OscDual d m) (hcoord : ∀ α : MultiIndex d,
      (fun w => OscDual.coord (X w) α) ∈ G)
    (hcoordMeas : ∀ α : MultiIndex d, Measurable (fun w => OscDual.coord (X w) α))
    (R : ℝ) (hR : 0 ≤ R)
    (henergy : Summable (fun α : MultiIndex d =>
      ∫ w, OscDual.coord (X w) α ^ 2 ∂P))
    (hbound : (∑' α : MultiIndex d,
      ∫ w, OscDual.coord (X w) α ^ 2 ∂P) ≤ R) :
    ∫⁻ w, ‖X w‖ₑ ^ (4 : ℝ) ∂P ≤ ENNReal.ofReal (3 * R ^ 2) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (MultiIndex d)
  let A : ℕ → Finset (MultiIndex d) := fun n => (Finset.range n).image f
  have hmono : Monotone A := fun n n' h => Finset.image_subset_image (Finset.range_mono h)
  have hcover : ∀ x : MultiIndex d, ∃ n, x ∈ A n := by
    intro x
    obtain ⟨k, rfl⟩ := hf x
    exact ⟨k + 1, Finset.mem_image.2 ⟨k, by simp, rfl⟩⟩
  have hvar0 : ∀ α : MultiIndex d, 0 ≤ ∫ w, OscDual.coord (X w) α ^ 2 ∂P :=
    fun α => integral_nonneg fun _ => sq_nonneg _
  have hfour : ∀ α : MultiIndex d,
      MemLp (fun w => OscDual.coord (X w) α) 4 P ∧
        ∫ w, OscDual.coord (X w) α ^ 4 ∂P =
          3 * (∫ w, OscDual.coord (X w) α ^ 2 ∂P) ^ 2 := by
    intro α
    exact hG _ (hcoord α)
  have hcross : ∀ α β : MultiIndex d,
      Integrable (fun w => OscDual.coord (X w) α ^ 2 * OscDual.coord (X w) β ^ 2) P ∧
      (∫ w, OscDual.coord (X w) α ^ 2 * OscDual.coord (X w) β ^ 2 ∂P) ≤
        3 * (∫ w, OscDual.coord (X w) α ^ 2 ∂P) *
          (∫ w, OscDual.coord (X w) β ^ 2 ∂P) := by
    intro α β
    have hα4 := qrpw_int4 (hfour α).1
    have hβ4 := qrpw_int4 (hfour β).1
    have hαa : AEStronglyMeasurable (fun w => OscDual.coord (X w) α ^ 2) P :=
      ((hcoordMeas α).pow_const 2).aestronglyMeasurable
    have hβa : AEStronglyMeasurable (fun w => OscDual.coord (X w) β ^ 2) P :=
      ((hcoordMeas β).pow_const 2).aestronglyMeasurable
    have hαsq : Integrable (fun w => (OscDual.coord (X w) α ^ 2) ^ 2) P := by
      simpa only [show ∀ w, (OscDual.coord (X w) α ^ 2) ^ 2 =
        OscDual.coord (X w) α ^ 4 from fun w => by ring] using hα4
    have hβsq : Integrable (fun w => (OscDual.coord (X w) β ^ 2) ^ 2) P := by
      simpa only [show ∀ w, (OscDual.coord (X w) β ^ 2) ^ 2 =
        OscDual.coord (X w) β ^ 4 from fun w => by ring] using hβ4
    have hcs := HRS.IID.integral_mul_le_sqrt
      (μ := P) (f := fun w => OscDual.coord (X w) α ^ 2)
      (g := fun w => OscDual.coord (X w) β ^ 2)
      (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) hαa hβa hαsq hβsq
    have hI : Integrable
        (fun w => OscDual.coord (X w) α ^ 2 * OscDual.coord (X w) β ^ 2) P := by
      exact qrpw_int_sqsq (hfour α).1 (hfour β).1
    refine ⟨hI, ?_⟩
    have hsa : Real.sqrt (∫ w, OscDual.coord (X w) α ^ 4 ∂P) =
        Real.sqrt 3 * (∫ w, OscDual.coord (X w) α ^ 2 ∂P) := by
      rw [(hfour α).2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (hvar0 α)]
    have hsb : Real.sqrt (∫ w, OscDual.coord (X w) β ^ 4 ∂P) =
        Real.sqrt 3 * (∫ w, OscDual.coord (X w) β ^ 2 ∂P) := by
      rw [(hfour β).2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (hvar0 β)]
    rw [show (fun w => (OscDual.coord (X w) α ^ 2) ^ 2) =
      fun w => OscDual.coord (X w) α ^ 4 from funext fun w => by ring,
      show (fun w => (OscDual.coord (X w) β ^ 2) ^ 2) =
      fun w => OscDual.coord (X w) β ^ 4 from funext fun w => by ring] at hcs
    rw [hsa, hsb] at hcs
    calc
      _ ≤ (Real.sqrt 3 * (∫ w, OscDual.coord (X w) α ^ 2 ∂P)) *
          (Real.sqrt 3 * (∫ w, OscDual.coord (X w) β ^ 2 ∂P)) := hcs
      _ = _ := by
        have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := by
          calc
            _ = (Real.sqrt 3) ^ 2 := by ring
            _ = 3 := Real.sq_sqrt (by norm_num)
        calc
          _ = ((Real.sqrt 3 * Real.sqrt 3) *
              (∫ w, OscDual.coord (X w) α ^ 2 ∂P)) *
              (∫ w, OscDual.coord (X w) β ^ 2 ∂P) := by ring
          _ = _ := by rw [hs3]
  have hfinite : ∀ n : ℕ,
      ∫ w, (∑ α ∈ A n, OscDual.coord (X w) α ^ 2) ^ 2 ∂P ≤ 3 * R ^ 2 := by
    intro n
    have hterm : ∀ α ∈ A n, Integrable (fun w => OscDual.coord (X w) α ^ 2) P :=
      fun α _ => qrpw_int_sq (hfour α).1
    have hcrossInt : ∀ α ∈ A n, ∀ β ∈ A n,
        Integrable (fun w => OscDual.coord (X w) α ^ 2 * OscDual.coord (X w) β ^ 2) P :=
      fun α _ β _ => (hcross α β).1
    have hpoint : (fun w => (∑ α ∈ A n, OscDual.coord (X w) α ^ 2) ^ 2) =
        fun w => ∑ α ∈ A n, ∑ β ∈ A n,
          OscDual.coord (X w) α ^ 2 * OscDual.coord (X w) β ^ 2 := by
      funext w
      rw [pow_two, Finset.sum_mul_sum]
    rw [hpoint, integral_finsetSum _ fun α hα =>
      integrable_finsetSum _ fun β hβ => hcrossInt α hα β hβ]
    have hrows : ∀ α ∈ A n,
        ∫ w, ∑ β ∈ A n, OscDual.coord (X w) α ^ 2 * OscDual.coord (X w) β ^ 2 ∂P =
          ∑ β ∈ A n, ∫ w, OscDual.coord (X w) α ^ 2 * OscDual.coord (X w) β ^ 2 ∂P := by
      intro α hα
      exact integral_finsetSum _ fun β hβ => hcrossInt α hα β hβ
    rw [Finset.sum_congr rfl hrows]
    calc
      _ ≤ ∑ α ∈ A n, ∑ β ∈ A n,
          3 * (∫ w, OscDual.coord (X w) α ^ 2 ∂P) *
            (∫ w, OscDual.coord (X w) β ^ 2 ∂P) := by
        apply Finset.sum_le_sum
        intro α hα
        apply Finset.sum_le_sum
        intro β hβ
        exact (hcross α β).2
      _ = 3 * (∑ α ∈ A n, ∫ w, OscDual.coord (X w) α ^ 2 ∂P) ^ 2 := by
        let v : MultiIndex d → ℝ := fun α => ∫ w, OscDual.coord (X w) α ^ 2 ∂P
        have hsquare : (∑ α ∈ A n, v α) ^ 2 =
            ∑ α ∈ A n, ∑ β ∈ A n, v α * v β := by
          rw [pow_two, Finset.sum_mul_sum]
        calc
          _ = 3 * (∑ α ∈ A n, ∑ β ∈ A n, v α * v β) := by
            calc
              _ = ∑ α ∈ A n, ∑ β ∈ A n, 3 * (v α * v β) := by
                apply Finset.sum_congr rfl
                intro α hα
                apply Finset.sum_congr rfl
                intro β hβ
                ring
              _ = _ := by simp_rw [← Finset.mul_sum]
          _ = _ := by rw [← hsquare]
      _ ≤ 3 * R ^ 2 := by
        have hpart : (∑ α ∈ A n, ∫ w, OscDual.coord (X w) α ^ 2 ∂P) ≤ R := by
          calc
            _ = ∑ α ∈ A n, (fun α =>
                ∫ w, OscDual.coord (X w) α ^ 2 ∂P) α := by rfl
            _ ≤ ∑' α, ∫ w, OscDual.coord (X w) α ^ 2 ∂P :=
              Summable.sum_le_tsum (A n) (fun α _ => hvar0 α) henergy
            _ ≤ R := hbound
        have hpart0 : 0 ≤ ∑ α ∈ A n, ∫ w, OscDual.coord (X w) α ^ 2 ∂P :=
          Finset.sum_nonneg fun α _ => hvar0 α
        nlinarith [sq_nonneg (R - ∑ α ∈ A n,
          ∫ w, OscDual.coord (X w) α ^ 2 ∂P)]
  have htermMeas : ∀ α, AEMeasurable
      (fun w => ENNReal.ofReal (OscDual.coord (X w) α ^ 2)) P :=
    fun α => (ENNReal.measurable_ofReal.comp ((hcoordMeas α).pow_const 2)).aemeasurable
  have hlim : ∀ w, Tendsto
      (fun n => ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (X w) α ^ 2) ^ 2))
      atTop (𝓝 (‖X w‖ₑ ^ (4 : ℝ))) := by
    intro w
    have hsum := lp_two_summable
      (show lp (fun _ : MultiIndex d => ℝ) 2 from X w)
    have hsection : Tendsto
        (fun n => ∑ α ∈ A n, OscDual.coord (X w) α ^ 2)
        atTop (𝓝 (‖X w‖ ^ 2)) := by
      have h := hsum.hasSum.comp (tendsto_atTop_finset_of_monotone hmono hcover)
      have hn : ‖X w‖ ^ 2 = ∑' α, (OscDual.coord (X w) α) ^ 2 :=
        lp_two_norm_sq (ι := MultiIndex d)
          (show lp (fun _ : MultiIndex d => ℝ) 2 from X w)
      rw [hn]
      exact h
    have h2 := ENNReal.tendsto_ofReal (hsection.pow 2)
    have he : ENNReal.ofReal ((‖X w‖ ^ 2) ^ 2) = ‖X w‖ₑ ^ (4 : ℝ) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (X w)) (by norm_num)]
      congr 1
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    simpa only [he] using h2
  have hmeas : ∀ n, AEMeasurable
      (fun w => ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (X w) α ^ 2) ^ 2)) P := by
    intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((Finset.measurable_sum _ fun α _ => (hcoordMeas α).pow_const 2).pow_const 2).aemeasurable)
  calc
    _ = ∫⁻ w, liminf
        (fun n => ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (X w) α ^ 2) ^ 2)) atTop ∂P := by
      refine lintegral_congr fun w => ?_
      exact ((hlim w).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ w,
        ENNReal.ofReal ((∑ α ∈ A n, OscDual.coord (X w) α ^ 2) ^ 2) ∂P) atTop :=
      lintegral_liminf_le' hmeas
    _ ≤ ENNReal.ofReal (3 * R ^ 2) :=
      liminf_le_of_frequently_le' (Filter.Eventually.of_forall fun n => by
        have hI : Integrable (fun w => (∑ α ∈ A n,
            OscDual.coord (X w) α ^ 2) ^ 2) P := by
          have hcrossInt : ∀ α ∈ A n, ∀ β ∈ A n,
              Integrable (fun w => OscDual.coord (X w) α ^ 2 *
                OscDual.coord (X w) β ^ 2) P := fun α _ β _ => (hcross α β).1
          have hpt : (fun w => (∑ α ∈ A n, OscDual.coord (X w) α ^ 2) ^ 2) =
              fun w => ∑ α ∈ A n, ∑ β ∈ A n,
                OscDual.coord (X w) α ^ 2 * OscDual.coord (X w) β ^ 2 := by
            funext w
            rw [pow_two, Finset.sum_mul_sum]
          rw [hpt]
          exact integrable_finsetSum _ fun α hα =>
            integrable_finsetSum _ fun β hβ => hcrossInt α hα β hβ
        rw [← ofReal_integral_eq_lintegral_ofReal hI
          (ae_of_all _ fun _ => by positivity)]
        exact ENNReal.ofReal_le_ofReal (hfinite n)).frequently

/-- Uniform decaying fourth moments of the difference of the two canonical
moving windows under any realization of the shared thermal law. -/
theorem fp81v01_difference_canonical_window_L4
    {d : ℕ} (hd : 2 ≤ d) {s a β γ T lam : ℝ}
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hT : 0 < T) (hlam : 0 < lam) :
    ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      IsR2Poincare (HRS.Whole.withDensityReal ρ) lam →
      ∃ M : ℝ, 0 < M ∧
        ∀ u : ℝ, ∀ hu : 0 ≤ u,
          ∀ (P : Measure (PathPair d (wholeSpaceIndex d) (u + T)))
            [IsProbabilityMeasure P],
            r26t6_SharedThermalLaw P s a β γ (u + T) ρ
              (pairedProcess d (wholeSpaceIndex d) (u + T) (add_nonneg hu hT.le)) →
            let W := physicalPairedWindow (d := d) (m := wholeSpaceIndex d)
              (T := T) (H := u + T) hu le_rfl
            MemLp (fun w => W 0 w - W 1 w) 4 P ∧
              eLpNorm (fun w => W 0 w - W 1 w) 4 P ≤
                ENNReal.ofReal (M * Real.exp (-(lam / β) * u)) := by
  intro ρ hρ hP
  let μ := HRS.Whole.withDensityReal ρ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hρ.2.1
  have hsd : s < (d : ℝ) := by
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨Adec, hAdec, hdec⟩ :=
    HRS.MS.ProClosureS111.physical_initial_difference_variance_decay
      hd s a β lam hs0 hs ha hβ hlam
  obtain ⟨Binc, hBinc, hmemU, hH01⟩ :=
    s111x2_H01 hd s a β lam hs0 hs ha hβ hlam hρ hP
  obtain ⟨Mtd, Td⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := s111x2_init_sum (by omega) Td
  obtain ⟨r, q, hr0, hr1, hq0, hq1, hqr⟩ :=
    HRS.MP.KC.mkc_consts (β := 1) (p := 4) one_pos (by norm_num)
  have hr : 1 < 2 * r ^ 4 := by
    have hqr' : 1 ≤ q * (2 * r ^ 4) := by
      simpa [pow_one, mul_assoc] using hqr
    have hpos : 0 < 2 * r ^ 4 := mul_pos (by norm_num) (pow_pos hr0 4)
    have hstrict : q * (2 * r ^ 4) < 2 * r ^ 4 := by
      simpa only [one_mul] using (mul_lt_mul_of_pos_right hq1 hpos)
    calc
      1 ≤ q * (2 * r ^ 4) := hqr'
      _ < 2 * r ^ 4 := hstrict
  have hqden : 1 / (2 * r ^ 4) < 1 := (div_lt_one (by positivity)).2 hr
  let C0 : ℝ := 12 * Binc ^ 2 * T ^ 2
  let Bwin : ℝ := 8 * (3 * (Adec * Λ) ^ 2 +
    (HRS.MP.KC.mkc_c r) ^ 4 * (C0 * T ^ 2 / (1 - 1 / (2 * r ^ 4))))
  have hBwin : 0 ≤ Bwin := by dsimp [Bwin]; positivity
  let M : ℝ := Bwin ^ (1 / 4 : ℝ) + 1
  have hM : 0 < M := by
    dsimp [M]
    have hnonneg : 0 ≤ Bwin ^ (1 / 4 : ℝ) := Real.rpow_nonneg hBwin _
    linarith
  let κ : ℝ := lam / β
  have hκ0 : 0 < κ := by dsimp [κ]; positivity
  have hcsSum : ∀ S : Finset (MultiIndex d),
      (∑ α ∈ S, s111x2_centeredSquare μ
        (oscTestFun (wholeSpaceIndex d : ℝ) α)) ≤ Λ := by
    intro S
    calc
      _ ≤ ∑ α ∈ S, (s111x2_centeredSquare μ
          (oscTestFun (wholeSpaceIndex d : ℝ) α) +
        s111x2_centeredSquare μ
          (generatorW (r26t6_thermalCoeff d s a β ρ) 0
            (oscTestFun (wholeSpaceIndex d : ℝ) α))) := by
        apply Finset.sum_le_sum
        intro α hα
        have hnonneg := s111x2_cs_nonneg μ
          (generatorW (r26t6_thermalCoeff d s a β ρ) 0
            (oscTestFun (wholeSpaceIndex d : ℝ) α))
        linarith
      _ ≤ Λ := by
        have hC : r26t6_thermalCoeff d s a β ρ =
            (quadraticGradientDyn d s a β).coeff (fun _ => ρ) := by rfl
        simpa [μ, hC] using hΛ S
  have hcsSummable : Summable (fun α : MultiIndex d =>
      s111x2_centeredSquare μ (oscTestFun (wholeSpaceIndex d : ℝ) α)) :=
    summable_of_sum_le (fun α => s111x2_cs_nonneg μ
      (oscTestFun (wholeSpaceIndex d : ℝ) α)) hcsSum
  refine ⟨M, hM, ?_⟩
  intro u hu P _ hZ
  let H : ℝ := u + T
  have hHpos : 0 < H := by dsimp [H]; linarith
  have hHle : u + T ≤ H := le_rfl
  let Z : Fin 2 → ℝ → PathPair d (wholeSpaceIndex d) H → OscDual d (wholeSpaceIndex d) :=
    pairedProcess d (wholeSpaceIndex d) H hHpos.le
  have hZ' : r26t6_SharedThermalLaw P s a β γ H ρ Z := by
    simpa [H, Z] using hZ
  obtain ⟨G, hG, hobs⟩ := physical_observation_gaussian_space Z hZ'
  let X : ℝ → PathPair d (wholeSpaceIndex d) H → OscDual d (wholeSpaceIndex d) :=
    fun t w => Z 0 (u + t) w - Z 1 (u + t) w
  have hXm : ∀ t, Measurable (X t) := by
    intro t
    exact ((hZ'.evolution 0).meas (u + t)).sub ((hZ'.evolution 1).meas (u + t))
  have htime : ∀ t, t ∈ Set.Icc (0 : ℝ) T → u + t ∈ Set.Icc (0 : ℝ) H := by
    intro t ht
    exact ⟨add_nonneg hu ht.1, by dsimp [H]; linarith [ht.2]⟩
  have hcoordG : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ alpha : MultiIndex d,
      (fun w => OscDual.coord (X t w) alpha) ∈ G := by
    intro t ht alpha
    let phi := oscTestFun (wholeSpaceIndex d : ℝ) alpha
    have hphi : IsOscTest (wholeSpaceIndex d) phi :=
      HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex d) alpha
    have h0 := hobs 0 (u + t) (htime t ht) phi hphi
    have h1 := hobs 1 (u + t) (htime t ht) phi hphi
    have hsub := G.sub_mem h0 h1
    convert hsub using 1
    funext w
    simpa [X, phi, OscDual.eval_oscTestFun] using
      (HRS.MS.GenPath.s56_coord_sub (Z 0 (u + t) w) (Z 1 (u + t) w) alpha)
  have hcoordMeas : ∀ t alpha,
      Measurable (fun w => OscDual.coord (X t w) alpha) := by
    intro t alpha
    exact (HRS.MS.S111T.s111t_coordCLM d (wholeSpaceIndex d) alpha).continuous.measurable.comp
      (hXm t)
  let cs : MultiIndex d → ℝ := fun alpha =>
    s111x2_centeredSquare μ (oscTestFun (wholeSpaceIndex d : ℝ) alpha)
  have hcsSum' : ∀ S : Finset (MultiIndex d), (∑ alpha ∈ S, cs alpha) ≤ Λ := by
    intro S
    exact hcsSum S
  have hcsSummable' : Summable cs := by
    exact hcsSummable
  have hcsTsum : (∑' alpha : MultiIndex d, cs alpha) ≤ Λ :=
    Real.tsum_le_of_sum_le (fun alpha => s111x2_cs_nonneg μ
      (oscTestFun (wholeSpaceIndex d : ℝ) alpha)) hcsSum'
  let X0 : PathPair d (wholeSpaceIndex d) H → OscDual d (wholeSpaceIndex d) := X 0
  let R0 : ℝ := Adec * Λ * Real.exp (-2 * κ * u)
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  have hinitCoord : ∀ alpha : MultiIndex d,
      (∫ w, OscDual.coord (X0 w) alpha ^ 2 ∂P) ≤
        Adec * Real.exp (-2 * κ * u) * cs alpha := by
    intro alpha
    let phi := oscTestFun (wholeSpaceIndex d : ℝ) alpha
    have hphi : IsOscTest (wholeSpaceIndex d) phi :=
      HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex d) alpha
    have htime0 : u ∈ Set.Icc (0 : ℝ) H := by
      constructor
      · exact hu
      · dsimp [H]
        linarith [hT]
    obtain ⟨_, hsecond, _⟩ := HRS.MS.ProClosureS111.physical_shared_difference_moments
      hd hs0 hs ha hβ hγ hρ hZ' htime0 hphi
    have hdecay := hdec ρ hρ hP γ hγ u hu phi hphi
    have heq : (fun w => OscDual.coord (X0 w) alpha) = fun w =>
        OscDual.eval (Z 0 u w) phi - OscDual.eval (Z 1 u w) phi := by
      funext w
      simpa [X0, X, phi, OscDual.eval_oscTestFun] using
        (HRS.MS.GenPath.s56_coord_sub (Z 0 u w) (Z 1 u w) alpha)
    have heqSq : (fun w => OscDual.coord (X0 w) alpha ^ 2) = fun w =>
        (OscDual.eval (Z 0 u w) phi - OscDual.eval (Z 1 u w) phi) ^ 2 := by
      funext w
      rw [congrFun heq w]
    rw [heqSq]
    rw [hsecond]
    simpa [cs, phi, μ, s111x2_centeredSquare] using hdecay
  have hmajor0 : Summable (fun alpha : MultiIndex d =>
      (Adec * Real.exp (-2 * κ * u)) * cs alpha) :=
    hcsSummable'.mul_left _
  have henergy0 : Summable (fun alpha : MultiIndex d =>
      ∫ w, OscDual.coord (X0 w) alpha ^ 2 ∂P) :=
    Summable.of_nonneg_of_le (fun alpha => integral_nonneg fun w => sq_nonneg _)
      hinitCoord hmajor0
  have hbound0 : (∑' alpha : MultiIndex d,
      ∫ w, OscDual.coord (X0 w) alpha ^ 2 ∂P) ≤ R0 := by
    calc
      _ ≤ ∑' alpha : MultiIndex d, (Adec * Real.exp (-2 * κ * u)) * cs alpha :=
        henergy0.tsum_le_tsum hinitCoord hmajor0
      _ = (Adec * Real.exp (-2 * κ * u)) * ∑' alpha : MultiIndex d, cs alpha :=
        tsum_mul_left
      _ ≤ R0 := by
        dsimp [R0]
        calc
          _ ≤ (Adec * Real.exp (-2 * κ * u)) * Λ :=
            mul_le_mul_of_nonneg_left hcsTsum (by positivity)
          _ = Adec * Λ * Real.exp (-2 * κ * u) := by ring
  have hX0four := fp81v01_difference_qrpw_hilbert_fourth G hG X0
    (fun alpha => hcoordG 0 ⟨le_rfl, hT.le⟩ alpha)
    (fun alpha => hcoordMeas 0 alpha) R0 hR0 henergy0 hbound0
  have hX04 : MemLp X0 4 P := by
    change eLpNorm X0 4 P < ⊤
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
      (hXm 0).aestronglyMeasurable).2
    have hlt : (∫⁻ w, ‖X0 w‖ₑ ^ (4 : ℝ) ∂P) < ⊤ :=
      hX0four.trans_lt ENNReal.ofReal_lt_top
    simpa only [ENNReal.toReal_ofNat] using hlt
  have hX0int : (∫ w, ‖X0 w‖ ^ 4 ∂P) ≤ 3 * R0 ^ 2 := by
    have hI := hX04.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    have he := ofReal_integral_eq_lintegral_ofReal hI
      (ae_of_all _ fun w => pow_nonneg (norm_nonneg (X0 w)) 4)
    have hb : ENNReal.ofReal (∫ w, ‖X0 w‖ ^ 4 ∂P) ≤
        ENNReal.ofReal (3 * R0 ^ 2) := by
      rw [he]
      simpa only [show ∀ y : OscDual d (wholeSpaceIndex d),
        ENNReal.ofReal (‖y‖ ^ 4) = ‖y‖ₑ ^ (4 : ℝ) from fun y => by
          rw [← ofReal_norm_eq_enorm]
          exact (ENNReal.ofReal_pow (norm_nonneg y) 4).trans
            (ENNReal.rpow_natCast (ENNReal.ofReal ‖y‖) 4).symm] using hX0four
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb
  have htraceInc : ∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) T →
      y ∈ Set.Icc (0 : ℝ) T → x ≤ y →
      Summable (fun alpha : MultiIndex d =>
        ∫ w, OscDual.coord (X y w - X x w) alpha ^ 2 ∂P) ∧
      (∑' alpha : MultiIndex d,
        ∫ w, OscDual.coord (X y w - X x w) alpha ^ 2 ∂P) ≤
          2 * Binc * (y - x) ^ 2 * Real.exp (-2 * κ * u) := by
    intro x y hx hy hxy
    let tx := u + x
    let ty := u + y
    have htx : tx ∈ Set.Icc (0 : ℝ) H := htime x hx
    have hty : ty ∈ Set.Icc (0 : ℝ) H := htime y hy
    obtain ⟨_, _, hvar⟩ := fp81v01_difference_observation_increment_variance_le
      hd hs0 hs ha hβ hγ hlam hρ hP hZ' htx hty (by dsimp [tx, ty]; linarith)
    have hfinite : ∀ S : Finset (MultiIndex d),
        (∑ alpha ∈ S, ∫ w, OscDual.coord (X y w - X x w) alpha ^ 2 ∂P) ≤
          2 * Binc * (y - x) ^ 2 * Real.exp (-2 * κ * tx) := by
      intro S
      have hcoordVar : ∀ alpha : MultiIndex d,
          (∫ w, OscDual.coord (X y w - X x w) alpha ^ 2 ∂P) ≤
            2 * s111x2_centeredSquare μ (fun z =>
              propagatorW (r26t6_thermalCoeff d s a β ρ) 0 ty
                (oscTestFun (wholeSpaceIndex d : ℝ) alpha) z -
              propagatorW (r26t6_thermalCoeff d s a β ρ) 0 tx
                (oscTestFun (wholeSpaceIndex d : ℝ) alpha) z) := by
        intro alpha
        let phi := oscTestFun (wholeSpaceIndex d : ℝ) alpha
        have hphi : IsOscTest (wholeSpaceIndex d) phi :=
          HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex d) alpha
        have heq : (fun w => OscDual.coord (X y w - X x w) alpha) = fun w =>
            (OscDual.eval (Z 0 ty w) phi - OscDual.eval (Z 1 ty w) phi) -
            (OscDual.eval (Z 0 tx w) phi - OscDual.eval (Z 1 tx w) phi) := by
          funext w
          simp [X, phi, tx, ty, HRS.MS.GenPath.s56_coord_sub, OscDual.eval_oscTestFun]
        have hsquare : (fun w => OscDual.coord (X y w - X x w) alpha ^ 2) = fun w =>
            ((OscDual.eval (Z 0 tx w) phi - OscDual.eval (Z 1 tx w) phi) -
              (OscDual.eval (Z 0 ty w) phi - OscDual.eval (Z 1 ty w) phi)) ^ 2 := by
          funext w
          rw [congrFun heq w]
          ring
        rw [show (fun w => OscDual.coord (X y w - X x w) alpha ^ 2) = _ from hsquare]
        exact (hvar alpha).1
      calc
        _ ≤ ∑ alpha ∈ S, 2 * s111x2_centeredSquare μ (fun z =>
            propagatorW (r26t6_thermalCoeff d s a β ρ) 0 ty
              (oscTestFun (wholeSpaceIndex d : ℝ) alpha) z -
            propagatorW (r26t6_thermalCoeff d s a β ρ) 0 tx
              (oscTestFun (wholeSpaceIndex d : ℝ) alpha) z) :=
          Finset.sum_le_sum fun alpha _ => hcoordVar alpha
        _ = 2 * ∑ alpha ∈ S, s111x2_centeredSquare μ (fun z =>
            propagatorW (r26t6_thermalCoeff d s a β ρ) 0 ty
              (oscTestFun (wholeSpaceIndex d : ℝ) alpha) z -
            propagatorW (r26t6_thermalCoeff d s a β ρ) 0 tx
              (oscTestFun (wholeSpaceIndex d : ℝ) alpha) z) := by rw [Finset.mul_sum]
        _ ≤ 2 * (Binc * (ty - tx) ^ 2 * Real.exp (-2 * κ * tx)) := by
          have h01 := hH01 S tx ty (htx.1) (by dsimp [tx, ty]; linarith)
          have hsum := h01.2
          have hsum2 := mul_le_mul_of_nonneg_left hsum
            (by norm_num : (0 : ℝ) ≤ 2)
          exact hsum2
        _ = 2 * Binc * (y - x) ^ 2 * Real.exp (-2 * κ * tx) := by
          have hdiff : ty - tx = y - x := by dsimp [ty, tx]; ring
          rw [hdiff]
          ring
    have hnonneg : ∀ alpha : MultiIndex d,
        0 ≤ ∫ w, OscDual.coord (X y w - X x w) alpha ^ 2 ∂P :=
      fun alpha => integral_nonneg fun w => sq_nonneg _
    have hsum : Summable (fun alpha : MultiIndex d =>
        ∫ w, OscDual.coord (X y w - X x w) alpha ^ 2 ∂P) :=
      summable_of_sum_le hnonneg hfinite
    have htsum := Real.tsum_le_of_sum_le hnonneg hfinite
    have hexp : Real.exp (-2 * κ * tx) ≤ Real.exp (-2 * κ * u) := by
      apply Real.exp_le_exp.mpr
      dsimp [tx]
      have hmul : 0 ≤ (2 : ℝ) * κ * x :=
        mul_nonneg (mul_nonneg (by norm_num) hκ0.le) hx.1
      nlinarith
    have hcoef : 0 ≤ 2 * Binc * (y - x) ^ 2 := by positivity
    refine ⟨hsum, ?_⟩
    calc
      _ ≤ 2 * Binc * (y - x) ^ 2 * Real.exp (-2 * κ * tx) := htsum
      _ ≤ 2 * Binc * (y - x) ^ 2 * Real.exp (-2 * κ * u) :=
        mul_le_mul_of_nonneg_left hexp hcoef
  let Cinc : ℝ := 12 * Binc ^ 2 * T ^ 2 * Real.exp (-4 * κ * u)
  have hCinc : 0 ≤ Cinc := by dsimp [Cinc]; positivity
  have habsT : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T →
      |t - s| ≤ T := by
    intro s t hs ht
    apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ‖X t w - X s w‖ₑ ^ (4 : ℝ) ∂P) ≤
        ENNReal.ofReal (Cinc * |t - s| ^ 2) := by
    intro s hs t ht
    let D : PathPair d (wholeSpaceIndex d) H → OscDual d (wholeSpaceIndex d) :=
      fun w => X t w - X s w
    have hcoordD : ∀ alpha : MultiIndex d,
        (fun w => OscDual.coord (D w) alpha) ∈ G := by
      intro alpha
      exact G.sub_mem (hcoordG t ht alpha) (hcoordG s hs alpha)
    have hcoordDMeas : ∀ alpha : MultiIndex d,
        Measurable (fun w => OscDual.coord (D w) alpha) := by
      intro alpha
      exact (HRS.MS.S111T.s111t_coordCLM d (wholeSpaceIndex d) alpha).continuous.measurable.comp
        ((hXm t).sub (hXm s))
    have henergyD : Summable (fun alpha : MultiIndex d =>
        ∫ w, OscDual.coord (D w) alpha ^ 2 ∂P) := by
      by_cases hst : s ≤ t
      · simpa [D] using (htraceInc s t hs ht hst).1
      · have hts : t ≤ s := le_of_not_ge hst
        have hsumm := (htraceInc t s ht hs hts).1
        have heq : (fun alpha : MultiIndex d =>
            ∫ w, OscDual.coord (D w) alpha ^ 2 ∂P) = fun alpha =>
              ∫ w, OscDual.coord (X s w - X t w) alpha ^ 2 ∂P := by
          funext alpha
          apply integral_congr_ae
          filter_upwards [] with w
          change (OscDual.coord (X t w - X s w) alpha) ^ 2 =
            (OscDual.coord (X s w - X t w) alpha) ^ 2
          have hleft := HRS.MS.GenPath.s56_coord_sub (X t w) (X s w) alpha
          have hright := HRS.MS.GenPath.s56_coord_sub (X s w) (X t w) alpha
          rw [hleft, hright]
          ring
        rw [heq]
        exact hsumm
    have hdt : |t - s| ≤ T := habsT s t hs ht
    have hRs : 0 ≤ 2 * Binc * |t - s| ^ 2 * Real.exp (-2 * κ * u) := by positivity
    have hboundD : (∑' alpha : MultiIndex d,
        ∫ w, OscDual.coord (D w) alpha ^ 2 ∂P) ≤
          2 * Binc * |t - s| ^ 2 * Real.exp (-2 * κ * u) := by
      by_cases hst : s ≤ t
      · have h := (htraceInc s t hs ht hst).2
        simpa [D, abs_of_nonneg (sub_nonneg.mpr hst)] using h
      · have hts : t ≤ s := le_of_not_ge hst
        have hsumm := htraceInc t s ht hs hts
        have heq : (fun alpha : MultiIndex d =>
            ∫ w, OscDual.coord (D w) alpha ^ 2 ∂P) = fun alpha =>
              ∫ w, OscDual.coord (X s w - X t w) alpha ^ 2 ∂P := by
          funext alpha
          apply integral_congr_ae
          filter_upwards [] with w
          change (OscDual.coord (X t w - X s w) alpha) ^ 2 =
            (OscDual.coord (X s w - X t w) alpha) ^ 2
          have hleft := HRS.MS.GenPath.s56_coord_sub (X t w) (X s w) alpha
          have hright := HRS.MS.GenPath.s56_coord_sub (X s w) (X t w) alpha
          rw [hleft, hright]
          ring
        rw [heq]
        have h := hsumm.2
        have hpow : (s - t) ^ 2 = (t - s) ^ 2 := by ring
        rw [hpow] at h
        simpa only [sq_abs] using h
    have hDfour := fp81v01_difference_qrpw_hilbert_fourth G hG D
      hcoordD hcoordDMeas (2 * Binc * |t - s| ^ 2 * Real.exp (-2 * κ * u))
      hRs henergyD hboundD
    have hexp : Real.exp (-2 * κ * u) ^ 2 = Real.exp (-4 * κ * u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have htimepow : |t - s| ^ 4 ≤ T ^ 2 * |t - s| ^ 2 := by
      have hsq : |t - s| ^ 2 ≤ T ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hT.le).2 hdt
      calc
        _ = |t - s| ^ 2 * |t - s| ^ 2 := by ring
        _ ≤ T ^ 2 * |t - s| ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    calc
      _ ≤ ENNReal.ofReal
          (3 * (2 * Binc * |t - s| ^ 2 * Real.exp (-2 * κ * u)) ^ 2) := hDfour
      _ ≤ ENNReal.ofReal (Cinc * |t - s| ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [Cinc]
        rw [mul_pow, mul_pow, hexp]
        have hcoef : 0 ≤ 12 * Binc ^ 2 * Real.exp (-4 * κ * u) := by positivity
        calc
          _ = (12 * Binc ^ 2 * Real.exp (-4 * κ * u)) * |t - s| ^ 4 := by ring
          _ ≤ (12 * Binc ^ 2 * Real.exp (-4 * κ * u)) *
              (T ^ 2 * |t - s| ^ 2) := mul_le_mul_of_nonneg_left htimepow hcoef
          _ = _ := by ring
  have henorm (y : OscDual d (wholeSpaceIndex d)) :
      ENNReal.ofReal (‖y‖ ^ 4) = ‖y‖ₑ ^ (4 : ℝ) := by
    rw [← ofReal_norm_eq_enorm]
    exact (ENNReal.ofReal_pow (norm_nonneg y) 4).trans
      (ENNReal.rpow_natCast (ENNReal.ofReal ‖y‖) 4).symm
  have hmomReal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (Cinc * |t - s| ^ 2) := by
    intro s hs t ht
    calc
      _ = ∫⁻ w, ‖X t w - X s w‖ₑ ^ (4 : ℝ) ∂P :=
        lintegral_congr_ae (ae_of_all _ fun w => henorm (X t w - X s w))
      _ ≤ ENNReal.ofReal (Cinc * |t - s| ^ 2) := hmom s hs t ht
  have hpow (x : ℝ) (hx : 0 ≤ x) : x ^ (1 + (1 : ℝ)) = x ^ (2 : ℕ) := by
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    exact Real.rpow_natCast x 2
  have hmomMod : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ‖X t w - X s w‖ₑ ^ (4 : ℝ) ∂P) ≤
        ENNReal.ofReal (Cinc * |t - s| ^ (1 + (1 : ℝ))) := by
    intro s hs t ht
    rw [hpow |t - s| (abs_nonneg _)]
    exact hmom s hs t ht
  let E4 : ℝ := Real.exp (-4 * κ * u)
  have hE4 : 0 ≤ E4 := by dsimp [E4]; positivity
  have hC : 0 ≤ C0 * E4 := by dsimp [C0, E4]; positivity
  have hExp4 : Real.exp (-2 * κ * u) ^ 2 = E4 := by
    dsimp [E4]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hX0intDecay : (∫ w, ‖X0 w‖ ^ 4 ∂P) ≤
      3 * (Adec * Λ) ^ 2 * E4 := by
    calc
      _ ≤ 3 * R0 ^ 2 := hX0int
      _ = 3 * (Adec * Λ) ^ 2 * E4 := by
        rw [show R0 = Adec * Λ * Real.exp (-2 * κ * u) by rfl, mul_pow, hExp4]
        ring
  have hmomInc : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal ((C0 * E4) * |t - s| ^ 2) := by
    intro s hs t ht
    have h := hmomReal s hs t ht
    simpa [Cinc, C0, E4, mul_assoc, mul_left_comm, mul_comm] using h
  have hY4 : MemLp (fun w =>
      (HRS.Whole.AppendixALemmas.contPathOf T
        (fun t => HRS.MP.KC.mkc_Zc X T r t w) : OscPath d (wholeSpaceIndex d) T))
      4 P :=
    HRS.MS.ProClosureS111.continuous_modification_memLp_four_of_fourth_increments
      P X hT hr0 hr1 hr hXm hX04 hC hmomInc
  have hYbound := HRS.MS.ProClosureS111.continuous_modification_fourth_moment_bound
    P X hT hr0 hr1 hr hXm hX04 hC hmomInc
  let W : PathPair d (wholeSpaceIndex d) H → OscPath d (wholeSpaceIndex d) T :=
    fun w => physicalPairedWindow (d := d) (m := wholeSpaceIndex d)
      (T := T) (H := H) hu le_rfl 0 w -
      physicalPairedWindow (d := d) (m := wholeSpaceIndex d)
        (T := T) (H := H) hu le_rfl 1 w
  let Y : PathPair d (wholeSpaceIndex d) H → OscPath d (wholeSpaceIndex d) T :=
    fun w => HRS.Whole.AppendixALemmas.contPathOf T
      (fun t => HRS.MP.KC.mkc_Zc X T r t w)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
  haveI : Countable D := hDc.to_subtype
  have hWae : W =ᵐ[P] Y := by
    have hall : ∀ᵐ w ∂P, ∀ t : D,
        HRS.MP.KC.mkc_Zc X T r t.1 w = X t.1 w := by
      apply ae_all_iff.2
      intro t
      exact HRS.MP.KC.mkc_Zc_ae_eq X T r P hXm (p := 4) (β := 1)
        (C := C0 * E4) (q := q) hT (by norm_num : 0 < (4 : ℝ)) one_pos hmomMod
        hr0 hr1 hq0 hq1 hqr t.1.2
    filter_upwards [hall] with w hw
    have hfun : (fun t : Set.Icc (0 : ℝ) T => OscPath.at' (W w) t) =
        (fun t => OscPath.at' (Y w) t) := by
      apply Continuous.ext_on hDd
        (show Continuous (fun t : Set.Icc (0 : ℝ) T => OscPath.at' (W w) t) from
          (W w).continuous)
        (show Continuous (fun t : Set.Icc (0 : ℝ) T => OscPath.at' (Y w) t) from
          (Y w).continuous)
      intro t ht
      have hwmod := hw ⟨t, ht⟩
      have hWat : OscPath.at' (W w) t = X t.1 w := by
        change OscPath.at' (physicalPairedWindow hu le_rfl 0 w) t -
          OscPath.at' (physicalPairedWindow hu le_rfl 1 w) t = X t.1 w
        rw [physicalPairedWindow_apply hu le_rfl hHpos.le 0 w t,
          physicalPairedWindow_apply hu le_rfl hHpos.le 1 w t]
      have hYat : OscPath.at' (Y w) t = HRS.MP.KC.mkc_Zc X T r t.1 w :=
        HRS.MP.KC.mkc_contPathOf_apply X hT hr0.le hr1 w t
      change OscPath.at' (W w) t = OscPath.at' (Y w) t
      rw [hWat, hYat]
      exact hwmod.symm
    exact ContinuousMap.ext fun t => by
      change OscPath.at' (W w) t = OscPath.at' (Y w) t
      exact congrFun hfun t
  have hW4 : MemLp W 4 P := (memLp_congr_ae hWae).2 hY4
  have hWint : (∫ w, ‖W w‖ ^ 4 ∂P) ≤ Bwin * E4 := by
    have hnormAE : (fun w => ‖W w‖ ^ 4) =ᵐ[P] fun w => ‖Y w‖ ^ 4 :=
      hWae.mono fun w h => by
        change ‖W w‖ ^ 4 = ‖Y w‖ ^ 4
        rw [h]
    rw [integral_congr_ae hnormAE]
    calc
      _ ≤ 8 * ((∫ w, ‖X 0 w‖ ^ 4 ∂P) +
          (HRS.MP.KC.mkc_c r) ^ 4 *
            (C0 * E4 * T ^ 2 / (1 - 1 / (2 * r ^ 4)))) := hYbound
      _ ≤ Bwin * E4 := by
        dsimp [Bwin]
        calc
          _ ≤ 8 * (3 * (Adec * Λ) ^ 2 * E4 +
              (HRS.MP.KC.mkc_c r) ^ 4 *
                (C0 * E4 * T ^ 2 / (1 - 1 / (2 * r ^ 4)))) := by
            apply mul_le_mul_of_nonneg_left
            · exact add_le_add hX0intDecay le_rfl
            · norm_num
          _ = _ := by ring
  have hroot : (∫ w, ‖W w‖ ^ 4 ∂P) ^ (1 / 4 : ℝ) ≤
      Bwin ^ (1 / 4 : ℝ) * Real.exp (-κ * u) := by
    have hmon := Real.rpow_le_rpow
      (integral_nonneg fun w => pow_nonneg (norm_nonneg (W w)) 4) hWint
      (by norm_num : 0 ≤ (1 / 4 : ℝ))
    have hexp4 : E4 = (Real.exp (-κ * u)) ^ 4 := by
      dsimp [E4]
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [κ]
      ring
    have hrootE : E4 ^ (1 / 4 : ℝ) = Real.exp (-κ * u) := by
      rw [hexp4, ← Real.rpow_natCast, ← Real.rpow_mul (Real.exp_pos _).le]
      norm_num
    have hmul : (Bwin * E4) ^ (1 / 4 : ℝ) =
        Bwin ^ (1 / 4 : ℝ) * Real.exp (-κ * u) := by
      rw [Real.mul_rpow hBwin hE4, hrootE]
    exact hmon.trans_eq hmul
  have hMbound : Bwin ^ (1 / 4 : ℝ) * Real.exp (-κ * u) ≤
      M * Real.exp (-κ * u) := by
    apply mul_le_mul_of_nonneg_right
    · dsimp [M]
      linarith
    · exact (Real.exp_nonneg _)
  have heqNorm : eLpNorm W 4 P =
      ENNReal.ofReal ((∫ w, ‖W w‖ ^ 4 ∂P) ^ (1 / 4 : ℝ)) := by
    rw [hW4.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, H]
    norm_num
  have hresult : MemLp W 4 P ∧
      eLpNorm W 4 P ≤ ENNReal.ofReal (M * Real.exp (-κ * u)) := by
    refine ⟨hW4, ?_⟩
    rw [heqNorm]
    apply ENNReal.ofReal_le_ofReal
    exact hroot.trans hMbound
  simpa [W, M, κ] using hresult

#print axioms fp81v01_difference_qrpw_hilbert_fourth
#print axioms fp81v01_difference_canonical_window_L4

end HRS.Fp81.V01
