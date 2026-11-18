import HRS.MS.ProClosureS111ObservationMoments
import HRS.MS.ProClosureS111WindowRestriction
import HRS.MS.ProClosureS111GaussianSpace
import HRS.MS.Fp81V01UniformNoise
import HRS.Sections.IIDAux3

/-! Uniform fourth moments for the actual moving observation window. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.S111T HRS.MS.R26T6
open HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.S111X2 HRS.MC.QRSpec.Wick

private theorem fp81v01_qrpw_hilbert_fourth
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
        exact hcross α β |>.2
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
              _ = _ := by
                simp_rw [← Finset.mul_sum]
          _ = _ := by rw [← hsquare]
      _ ≤ 3 * R ^ 2 := by
        have hpart : (∑ α ∈ A n, ∫ w, OscDual.coord (X w) α ^ 2 ∂P) ≤ R := by
          calc
            _ = ∑ α ∈ A n, (fun α => ∫ w, OscDual.coord (X w) α ^ 2 ∂P) α := by rfl
            _ ≤ ∑' α, ∫ w, OscDual.coord (X w) α ^ 2 ∂P :=
              Summable.sum_le_tsum (A n) (fun α _ => hvar0 α) henergy
            _ ≤ R := hbound
        have hpart0 : 0 ≤ ∑ α ∈ A n, ∫ w, OscDual.coord (X w) α ^ 2 ∂P :=
          Finset.sum_nonneg fun α _ => hvar0 α
        nlinarith [sq_nonneg (R - ∑ α ∈ A n,
          ∫ w, OscDual.coord (X w) α ^ 2 ∂P)]
  have hcoordAE : ∀ α, AEMeasurable (fun w => OscDual.coord (X w) α) P :=
    fun α => (hcoordMeas α).aemeasurable
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
      have hn : ‖X w‖ ^ 2 = ∑' α, (OscDual.coord (X w) α) ^ 2 := by
        exact lp_two_norm_sq (ι := MultiIndex d)
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

/- The marginal estimate is independent of the Poincare input used for the
paired-difference estimate in the larger design block. -/
theorem canonical_window_L4
    {d : ℕ} (hd : 2 ≤ d) {s a beta gamma T : ℝ}
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hT : 0 < T) :
    ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      ∃ M : ℝ, 0 < M ∧
        ∀ u : ℝ, ∀ hu : 0 ≤ u,
          ∀ (P : Measure (PathPair d (wholeSpaceIndex d) (u + T)))
            [IsProbabilityMeasure P],
            r26t6_SharedThermalLaw P s a beta gamma (u + T) rho
              (pairedProcess d (wholeSpaceIndex d) (u + T)
                (add_nonneg hu hT.le)) →
            ∀ i : Fin 2,
              let W := physicalPairedWindow (d := d) (m := wholeSpaceIndex d)
                (T := T) (H := u + T) hu le_rfl
              MemLp (W i) 4 P ∧ eLpNorm (W i) 4 P ≤ ENNReal.ofReal M := by
  intro rho hrho
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hsd : s < (d : ℝ) := by
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hX0 : X1Input d s a beta 0 rho :=
    x1Input_of_exist hd hs0 hs ha hbeta 0 hrho
      (exist_of_thermal hd hs0 hs ha hbeta hrho)
  obtain ⟨M0, c, S, hc, hTc⟩ :=
    HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hbeta hrho
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  obtain ⟨Ltrace, hLtrace, htrace⟩ :=
    fp81v01_physicalLinear_uniform_summability hd hX0 hK hbeta.le hgamma
      hs0 hs ha hbeta hrho
  obtain ⟨_, ⟨Linc, hLinc, hinc⟩⟩ :=
    fp81v01_physicalLinear_increment_bound_uniform T hd hX0 hK hbeta.le hgamma
      hs0 hs ha hbeta hrho
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
  let C : ℝ := 3 * Linc ^ 2
  let Bwin : ℝ := 8 * (3 * Ltrace ^ 2 +
    (HRS.MP.KC.mkc_c r) ^ 4 * (C * T ^ 2 / (1 - 1 / (2 * r ^ 4))))
  let M : ℝ := Bwin ^ (1 / 4 : ℝ) + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hqden : 1 / (2 * r ^ 4) < 1 := (div_lt_one (by positivity)).2 hr
  have hBwin : 0 ≤ Bwin := by
    dsimp [Bwin]
    positivity
  have hM : 0 < M := by
    dsimp [M]
    have : 0 ≤ Bwin ^ (1 / 4 : ℝ) := Real.rpow_nonneg hBwin _
    linarith
  refine ⟨M, hM, ?_⟩
  intro u hu P _ hZ i
  let Z : Fin 2 → ℝ → PathPair d (wholeSpaceIndex d) (u + T) → OscDual d (wholeSpaceIndex d) :=
    pairedProcess d (wholeSpaceIndex d) (u + T) (add_nonneg hu hT.le)
  obtain ⟨G, hG, hobs⟩ :=
    physical_observation_gaussian_space Z hZ
  let X : ℝ → PathPair d (wholeSpaceIndex d) (u + T) → OscDual d (wholeSpaceIndex d) :=
    fun t w => Z i (u + t) w
  have hXm : ∀ t, Measurable (X t) := by
    intro t
    exact (hZ.evolution i).meas (u + t)
  have hcoordG : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ alpha : MultiIndex d,
      (fun w => OscDual.coord (X t w) alpha) ∈ G := by
    intro t ht alpha
    have htime : u + t ∈ Set.Icc (0 : ℝ) (u + T) :=
      ⟨add_nonneg hu ht.1, by linarith [ht.2]⟩
    have h := hobs i (u + t) htime (oscTestFun (wholeSpaceIndex d) alpha)
      (HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex d) alpha)
    have he : (fun w => OscDual.coord (X t w) alpha) =
        fun w => OscDual.eval (Z i (u + t) w) (oscTestFun (wholeSpaceIndex d) alpha) := by
      funext w
      simp [X, OscDual.eval_oscTestFun]
    rw [he]
    exact h
  have hcoordMeas : ∀ t alpha,
      Measurable (fun w => OscDual.coord (X t w) alpha) := by
    intro t alpha
    exact (HRS.MS.S111T.s111t_coordCLM d (wholeSpaceIndex d) alpha).continuous.measurable.comp
      (hXm t)
  have hcov : ∀ alpha : MultiIndex d, ∀ t v : ℝ,
      t ∈ Set.Icc (0 : ℝ) T → v ∈ Set.Icc (0 : ℝ) T →
      (∫ w, OscDual.coord (X t w) alpha * OscDual.coord (X v w) alpha ∂P) =
        inner ℝ
          (physicalLinear hX0 hK hbeta.le hgamma i (u + t)
            (initialTestBasis (wholeSpaceIndex d) alpha))
          (physicalLinear hX0 hK hbeta.le hgamma i (u + v)
            (initialTestBasis (wholeSpaceIndex d) alpha)) := by
    intro alpha t v ht hv
    let phi : Euc d → ℝ := initialTestBasis (wholeSpaceIndex d) alpha
    have htimeT : u + t ∈ Set.Icc (0 : ℝ) (u + T) :=
      ⟨add_nonneg hu ht.1, by linarith [ht.2]⟩
    have htimeV : u + v ∈ Set.Icc (0 : ℝ) (u + T) :=
      ⟨add_nonneg hu hv.1, by linarith [hv.2]⟩
    have hsec := physical_shared_observation_second hd hs0 hs ha hbeta hgamma hrho hZ
      2 (fun _ : Fin 2 => i) (fun j => if j = 0 then u + t else u + v)
      (fun _ => phi)
      (by intro j; fin_cases j <;> simp [htimeT, htimeV])
      (by intro _; exact (initialTestBasis (wholeSpaceIndex d) alpha).property)
    have hgram := physicalLinear_gram hd hs0 hs ha hbeta hgamma hrho hX0 hK
      i i htimeT.1 htimeV.1 (initialTestBasis (wholeSpaceIndex d) alpha)
      (initialTestBasis (wholeSpaceIndex d) alpha)
    calc
      _ = ∫ w, OscDual.eval (Z i (u + t) w) phi *
            OscDual.eval (Z i (u + v) w) phi ∂P := by
        refine integral_congr_ae (ae_of_all _ fun w => ?_)
        simp only [X, phi, initialTestBasis, OscDual.eval_oscTestFun]
      _ = _ := by simpa [r26t6_preparation] using hsec 0 1
      _ = _ := by simpa [r26t6_preparation] using hgram.symm
  have hvar : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T → ∀ alpha : MultiIndex d,
      (∫ w, OscDual.coord (X t w) alpha ^ 2 ∂P) =
        ‖physicalLinear hX0 hK hbeta.le hgamma i (u + t)
          (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 := by
    intro t ht alpha
    have h := hcov alpha t t ht ht
    simpa only [pow_two, real_inner_self_eq_norm_sq] using h
  have hvarDiff : ∀ t s : ℝ, t ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      ∀ alpha : MultiIndex d,
      (∫ w, (OscDual.coord (X t w) alpha - OscDual.coord (X s w) alpha) ^ 2 ∂P) =
        ‖physicalLinear hX0 hK hbeta.le hgamma i (u + t)
            (initialTestBasis (wholeSpaceIndex d) alpha) -
          physicalLinear hX0 hK hbeta.le hgamma i (u + s)
            (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 := by
    intro t s ht hs alpha
    let A : PathPair d (wholeSpaceIndex d) (u + T) → ℝ :=
      fun w => OscDual.coord (X t w) alpha
    let D : PathPair d (wholeSpaceIndex d) (u + T) → ℝ :=
      fun w => OscDual.coord (X s w) alpha
    let Ft := physicalLinear hX0 hK hbeta.le hgamma i (u + t)
      (initialTestBasis (wholeSpaceIndex d) alpha)
    let Fs := physicalLinear hX0 hK hbeta.le hgamma i (u + s)
      (initialTestBasis (wholeSpaceIndex d) alpha)
    have hAt := hG A (hcoordG t ht alpha)
    have hAs := hG D (hcoordG s hs alpha)
    have hAt2 : Integrable (fun w => A w ^ 2) P := qrpw_int_sq hAt.1
    have hAs2 : Integrable (fun w => D w ^ 2) P := qrpw_int_sq hAs.1
    have hcross : Integrable (fun w => A w * D w) P := qrpw_int_mul hAt.1 hAs.1
    have hpoint : (fun w => (A w - D w) ^ 2) =
        fun w => A w ^ 2 + D w ^ 2 - 2 * (A w * D w) := by
      funext w
      dsimp [A, D]
      ring
    have hexpand : (∫ w, (A w - D w) ^ 2 ∂P) =
        (∫ w, A w ^ 2 ∂P) + (∫ w, D w ^ 2 ∂P) - 2 * (∫ w, A w * D w ∂P) := by
      calc
        _ = ∫ w, A w ^ 2 + D w ^ 2 - 2 * (A w * D w) ∂P := by
          exact integral_congr_ae (ae_of_all _ fun w => congrFun hpoint w)
        _ = _ := by
          have hsplit : (fun w => A w ^ 2 + D w ^ 2 - 2 * (A w * D w)) =
              (fun w => A w ^ 2 + D w ^ 2) - (fun w => 2 * (A w * D w)) := by
            funext w
            simp only [Pi.sub_apply]
          change (∫ w, ((fun w => A w ^ 2 + D w ^ 2 - 2 * (A w * D w)) w) ∂P) = _
          rw [hsplit]
          have hsub := integral_sub (f := fun w => A w ^ 2 + D w ^ 2)
            (g := fun w => 2 * (A w * D w)) (hAt2.add hAs2) (hcross.const_mul 2)
          change (∫ w, A w ^ 2 + D w ^ 2 - 2 * (A w * D w) ∂P) = _
          calc
            _ = (∫ w, A w ^ 2 + D w ^ 2 ∂P) - ∫ w, 2 * (A w * D w) ∂P := by
              exact hsub
            _ = _ := by rw [integral_add hAt2 hAs2, integral_const_mul]
    have hcovTT := hcov alpha t t ht ht
    have hcovSS := hcov alpha s s hs hs
    have hcovTS := hcov alpha t s ht hs
    have hAA : (∫ w, A w ^ 2 ∂P) = inner ℝ Ft Ft := by
      simpa [A, Ft, pow_two] using hcovTT
    have hDD : (∫ w, D w ^ 2 ∂P) = inner ℝ Fs Fs := by
      simpa [D, Fs, pow_two] using hcovSS
    have hAD : (∫ w, A w * D w ∂P) = inner ℝ Ft Fs := by
      simpa [A, D, Ft, Fs] using hcovTS
    have hfeatures :
        (∫ w, (A w - D w) ^ 2 ∂P) = inner ℝ Ft Ft + inner ℝ Fs Fs - 2 * inner ℝ Ft Fs := by
      rw [hexpand, hAA, hDD, hAD]
    have hnorm : ‖Ft - Fs‖ ^ 2 =
        inner ℝ Ft Ft + inner ℝ Fs Fs - 2 * inner ℝ Ft Fs := by
      rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring
    rw [show (fun w => (OscDual.coord (X t w) alpha -
        OscDual.coord (X s w) alpha) ^ 2) = fun w => (A w - D w) ^ 2 from rfl]
    calc
      _ = inner ℝ Ft Ft + inner ℝ Fs Fs - 2 * inner ℝ Ft Fs := hfeatures
      _ = ‖Ft - Fs‖ ^ 2 := hnorm.symm
  let X0 : PathPair d (wholeSpaceIndex d) (u + T) → OscDual d (wholeSpaceIndex d) := X 0
  have henergy0 : Summable (fun alpha : MultiIndex d =>
      ∫ w, OscDual.coord (X0 w) alpha ^ 2 ∂P) := by
    have heq : (fun alpha : MultiIndex d =>
        ∫ w, OscDual.coord (X0 w) alpha ^ 2 ∂P) =
      fun alpha => ‖physicalLinear hX0 hK hbeta.le hgamma i u
        (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 := by
      funext alpha
      simpa only [add_zero] using hvar 0 ⟨le_rfl, hT.le⟩ alpha
    rw [heq]
    exact (htrace i u hu).1
  have hbound0 : (∑' alpha : MultiIndex d,
      ∫ w, OscDual.coord (X0 w) alpha ^ 2 ∂P) ≤ Ltrace := by
    have heq : (fun alpha : MultiIndex d =>
        ∫ w, OscDual.coord (X0 w) alpha ^ 2 ∂P) =
      fun alpha => ‖physicalLinear hX0 hK hbeta.le hgamma i u
        (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 := by
      funext alpha
      simpa only [add_zero] using hvar 0 ⟨le_rfl, hT.le⟩ alpha
    rw [heq]
    exact (htrace i u hu).2
  have hinitLinfour := fp81v01_qrpw_hilbert_fourth G hG X0
    (fun alpha => hcoordG 0 ⟨le_rfl, hT.le⟩ alpha)
    (fun alpha => hcoordMeas 0 alpha) Ltrace hLtrace henergy0 hbound0
  have hX04 : MemLp X0 4 P := by
    change eLpNorm X0 4 P < ⊤
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
      (hXm 0).aestronglyMeasurable).2
    have hlt : (∫⁻ w, ‖X0 w‖ₑ ^ (4 : ℝ) ∂P) < ⊤ :=
      hinitLinfour.trans_lt ENNReal.ofReal_lt_top
    simpa only [ENNReal.toReal_ofNat] using hlt
  have hX0int : (∫ w, ‖X0 w‖ ^ 4 ∂P) ≤ 3 * Ltrace ^ 2 := by
    have hI := hX04.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    have he := ofReal_integral_eq_lintegral_ofReal hI
      (ae_of_all _ fun w => pow_nonneg (norm_nonneg (X0 w)) 4)
    have hb : ENNReal.ofReal (∫ w, ‖X0 w‖ ^ 4 ∂P) ≤ ENNReal.ofReal (3 * Ltrace ^ 2) := by
      rw [he]
      simpa only [show ∀ y : OscDual d (wholeSpaceIndex d),
        ENNReal.ofReal (‖y‖ ^ 4) = ‖y‖ₑ ^ (4 : ℝ) from fun y => by
          rw [← ofReal_norm_eq_enorm]
          exact (ENNReal.ofReal_pow (norm_nonneg y) 4).trans
            (ENNReal.rpow_natCast (ENNReal.ofReal ‖y‖) 4).symm] using hinitLinfour
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb
  have hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ‖X t w - X s w‖ₑ ^ (4 : ℝ) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2) := by
    intro v hv t ht
    let D : PathPair d (wholeSpaceIndex d) (u + T) → OscDual d (wholeSpaceIndex d) :=
      fun w => X t w - X v w
    have htimeT : u + t ∈ Set.Icc (0 : ℝ) (u + T) :=
      ⟨add_nonneg hu ht.1, by linarith [ht.2]⟩
    have htimeV : u + v ∈ Set.Icc (0 : ℝ) (u + T) :=
      ⟨add_nonneg hu hv.1, by linarith [hv.2]⟩
    have habs : |(u + t) - (u + v)| ≤ T := by
      rw [show (u + t) - (u + v) = t - v by ring]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2, hv.1, hv.2]
    have hfeat := hinc i (u + t) (u + v) htimeT.1 htimeV.1 habs
    have henergyD : Summable (fun alpha : MultiIndex d =>
        ∫ w, OscDual.coord (D w) alpha ^ 2 ∂P) := by
      have heq : (fun alpha : MultiIndex d =>
          ∫ w, OscDual.coord (D w) alpha ^ 2 ∂P) =
        fun alpha => ‖physicalLinear hX0 hK hbeta.le hgamma i (u + t)
            (initialTestBasis (wholeSpaceIndex d) alpha) -
          physicalLinear hX0 hK hbeta.le hgamma i (u + v)
            (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 := by
        funext alpha
        exact hvarDiff t v ht hv alpha
      rw [heq]
      exact hfeat.1
    have hboundD : (∑' alpha : MultiIndex d,
        ∫ w, OscDual.coord (D w) alpha ^ 2 ∂P) ≤ Linc * |t - v| := by
      have heq : (fun alpha : MultiIndex d =>
          ∫ w, OscDual.coord (D w) alpha ^ 2 ∂P) =
        fun alpha => ‖physicalLinear hX0 hK hbeta.le hgamma i (u + t)
            (initialTestBasis (wholeSpaceIndex d) alpha) -
          physicalLinear hX0 hK hbeta.le hgamma i (u + v)
            (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2 := by
        funext alpha
        exact hvarDiff t v ht hv alpha
      rw [heq]
      calc
        _ ≤ Linc * |(u + t) - (u + v)| := hfeat.2
        _ = Linc * |t - v| := by congr 1 <;> ring
    have hcoordD : ∀ alpha : MultiIndex d, (fun w => OscDual.coord (D w) alpha) ∈ G := by
      intro alpha
      have h := G.sub_mem (hcoordG t ht alpha) (hcoordG v hv alpha)
      change (fun w => OscDual.coord (D w) alpha) ∈ G
      convert h using 1
      funext w
      change OscDual.coord (X t w - X v w) alpha =
        OscDual.coord (X t w) alpha - OscDual.coord (X v w) alpha
      rfl
    have hcoordDMeas : ∀ alpha : MultiIndex d, Measurable
        (fun w => OscDual.coord (D w) alpha) := by
      intro alpha
      exact (HRS.MS.S111T.s111t_coordCLM d (wholeSpaceIndex d) alpha).continuous.measurable.comp
        ((hXm t).sub (hXm v))
    have hDfour := fp81v01_qrpw_hilbert_fourth G hG D hcoordD hcoordDMeas
      (Linc * |t - v|) (mul_nonneg hLinc (abs_nonneg _)) henergyD hboundD
    calc
      _ ≤ ENNReal.ofReal (3 * (Linc * |t - v|) ^ 2) := hDfour
      _ = ENNReal.ofReal (C * |t - v| ^ 2) := by
        congr 1
        dsimp [C]
        ring
  have henorm (y : OscDual d (wholeSpaceIndex d)) :
      ENNReal.ofReal (‖y‖ ^ 4) = ‖y‖ₑ ^ (4 : ℝ) := by
    rw [← ofReal_norm_eq_enorm]
    exact (ENNReal.ofReal_pow (norm_nonneg y) 4).trans
      (ENNReal.rpow_natCast (ENNReal.ofReal ‖y‖) 4).symm
  have hmomReal : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2) := by
    intro s hs t ht
    calc
      _ = ∫⁻ w, ‖X t w - X s w‖ₑ ^ (4 : ℝ) ∂P :=
        lintegral_congr_ae (ae_of_all _ fun w => henorm (X t w - X s w))
      _ ≤ ENNReal.ofReal (C * |t - s| ^ 2) := hmom s hs t ht
  have hpow (x : ℝ) (hx : 0 ≤ x) : x ^ (1 + (1 : ℝ)) = x ^ (2 : ℕ) := by
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    exact Real.rpow_natCast x 2
  have hmomMod : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ‖X t w - X s w‖ₑ ^ (4 : ℝ) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ (1 + (1 : ℝ))) := by
    intro s hs t ht
    rw [hpow |t - s| (abs_nonneg _)]
    exact hmom s hs t ht
  have hmomRealMod : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫⁻ w, ENNReal.ofReal (‖X t w - X s w‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ (1 + (1 : ℝ))) := by
    intro s hs t ht
    rw [hpow |t - s| (abs_nonneg _)]
    exact hmomReal s hs t ht
  have hY4 : MemLp (fun w =>
      (HRS.Whole.AppendixALemmas.contPathOf T
        (fun t => HRS.MP.KC.mkc_Zc X T r t w) : OscPath d (wholeSpaceIndex d) T))
      4 P :=
    continuous_modification_memLp_four_of_fourth_increments P X hT hr0 hr1 hr
      hXm hX04 hC hmomReal
  have hYbound := continuous_modification_fourth_moment_bound P X hT hr0 hr1 hr
    hXm hX04 hC hmomReal
  have hYint : (∫ w, ‖(HRS.Whole.AppendixALemmas.contPathOf T
      (fun t => HRS.MP.KC.mkc_Zc X T r t w) : OscPath d (wholeSpaceIndex d) T)‖ ^ 4 ∂P) ≤ Bwin := by
    calc
      _ ≤ 8 * ((∫ w, ‖X 0 w‖ ^ 4 ∂P) +
          (HRS.MP.KC.mkc_c r) ^ 4 * (C * T ^ 2 / (1 - 1 / (2 * r ^ 4)))) := hYbound
      _ ≤ Bwin := by
        dsimp [Bwin]
        exact mul_le_mul_of_nonneg_left (add_le_add hX0int le_rfl) (by norm_num)
  let W : PathPair d (wholeSpaceIndex d) (u + T) → OscPath d (wholeSpaceIndex d) T :=
    fun w => physicalPairedWindow (d := d) (m := wholeSpaceIndex d)
      (T := T) (H := u + T) hu le_rfl i w
  let Y : PathPair d (wholeSpaceIndex d) (u + T) → OscPath d (wholeSpaceIndex d) T :=
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
        (C := C) (q := q) hT (by norm_num : 0 < (4 : ℝ)) one_pos hmomMod
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
        simpa [W, X] using physicalPairedWindow_apply hu le_rfl
          (add_nonneg hu hT.le) i w t
      have hYat : OscPath.at' (Y w) t = HRS.MP.KC.mkc_Zc X T r t.1 w :=
        HRS.MP.KC.mkc_contPathOf_apply X hT hr0.le hr1 w t
      change OscPath.at' (W w) t = OscPath.at' (Y w) t
      rw [hWat, hYat]
      exact hwmod.symm
    exact ContinuousMap.ext fun t => by
      change OscPath.at' (W w) t = OscPath.at' (Y w) t
      exact congrFun hfun t
  have hW4 : MemLp W 4 P := (memLp_congr_ae hWae).2 hY4
  have hWint : (∫ w, ‖W w‖ ^ 4 ∂P) ≤ Bwin := by
    have hnormAE : (fun w => ‖W w‖ ^ 4) =ᵐ[P] fun w => ‖Y w‖ ^ 4 :=
      hWae.mono fun w h => by
        change ‖W w‖ ^ 4 = ‖Y w‖ ^ 4
        rw [h]
    rw [integral_congr_ae hnormAE]
    exact hYint
  have hroot : (∫ w, ‖W w‖ ^ 4 ∂P) ^ (1 / 4 : ℝ) ≤ Bwin ^ (1 / 4 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg fun w => pow_nonneg (norm_nonneg (W w)) 4)
      hWint
    norm_num
  have heqNorm : eLpNorm W 4 P =
      ENNReal.ofReal ((∫ w, ‖W w‖ ^ 4 ∂P) ^ (1 / 4 : ℝ)) := by
    rw [hW4.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    norm_num
  refine ⟨hW4, ?_⟩
  rw [heqNorm]
  apply ENNReal.ofReal_le_ofReal
  dsimp [M]
  linarith [hroot]

#print axioms fp81v01_qrpw_hilbert_fourth
#print axioms canonical_window_L4

end HRS.Fp81.V01
