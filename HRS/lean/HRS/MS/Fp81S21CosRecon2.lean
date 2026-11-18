import HRS.MS.Fp81S21CosRecon
import HRS.MS.R2SeAux5
import HRS.MS.R2WinOrbAux10

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS (Euc cbNorm MemCb)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.S21

/-- The path coordinate used by the observation, extended by zero off the time interval. -/
def fp81s21_cosRecon_coordExt {p : Parameters}
    (y : Window p) (α : MultiIndex p.d) (v : ℝ) : ℝ :=
  if hv : v ∈ Set.Icc (0 : ℝ) p.T then
    OscDual.coord (OscPath.at' y ⟨v, hv⟩) α
  else 0

/-- The explicit shifted-cosine analysis coordinate of a window. The time coordinate is
extended by zero outside `[0,T]` in the defining real-variable integral. -/
def fp81s21_cosRecon_obs26 (p : Parameters) (y : Window p) (j : ℕ) : ℝ :=
  let i := r26t3_feature_enum p.d j
  (1 + (i.1 : ℝ) ^ 2) ^ (3 / 8 : ℝ) *
    ∫ v in Set.Icc (0 : ℝ) p.T,
      r26t3_cosine p.T i.1 v * fp81s21_cosRecon_coordExt y i.2 v

private theorem fp81s21_cosRecon2_kap_eq (n : ℕ) :
    s11p_kap n = s21f_w n := by
  unfold HRS.Whole.s11p_kap HRS.MS.R26T3.s21f_w
  congr 1
  norm_num

private theorem fp81s21_cosRecon2_coord_bound
    {p : Parameters} (σ : ℕ ≃ ℕ × MultiIndex p.d) (z : SeqL2)
    (n : ℕ) (α : MultiIndex p.d) :
    |(s21gTheta σ z).c (n, α)| ≤
      ‖s21f_slice (m := (wholeSpaceIndex p.d : ℕ)) σ n z‖ := by
  let sl := s21f_slice (m := (wholeSpaceIndex p.d : ℕ)) σ n z
  have htheta : (s21gTheta σ z).c (n, α) = SeqL2.coord z (σ.symm (n, α)) := by
    have h := s21gTheta_c σ z (σ.symm (n, α))
    simpa using h
  have hclm : ‖HRS.MS.R2Interp.s102_coordCLM (m := (wholeSpaceIndex p.d : ℕ)) α‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have happly : HRS.MS.R2Interp.s102_coordCLM (m := (wholeSpaceIndex p.d : ℕ)) α sl =
      OscDual.coord sl α := rfl
  have hcoord : SeqL2.coord z (σ.symm (n, α)) = OscDual.coord sl α := by
    simpa [sl] using (s21f_slice_coord (m := (wholeSpaceIndex p.d : ℕ)) σ n z α).symm
  have hop := (HRS.MS.R2Interp.s102_coordCLM
    (m := (wholeSpaceIndex p.d : ℕ)) α).le_opNorm sl
  calc |(s21gTheta σ z).c (n, α)| = ‖OscDual.coord sl α‖ := by
        rw [htheta, hcoord, Real.norm_eq_abs]
    _ = ‖HRS.MS.R2Interp.s102_coordCLM
          (m := (wholeSpaceIndex p.d : ℕ)) α sl‖ := by rw [happly]
    _ ≤ ‖HRS.MS.R2Interp.s102_coordCLM (m := (wholeSpaceIndex p.d : ℕ)) α‖ * ‖sl‖ := hop
    _ ≤ 1 * ‖sl‖ := mul_le_mul_of_nonneg_right hclm (norm_nonneg _)
    _ = ‖sl‖ := one_mul _

/-- The explicit observation applied to `s21gPhi` recovers the original sequence coordinate. -/
theorem fp81s21_cosRecon_obs26_synthesis
    (p : Parameters) (z : SeqL2) (j : ℕ) :
    fp81s21_cosRecon_obs26 p
      (s21gPhi (r26t3_feature_enum p.d) p.hT
        ((wholeSpaceIndex p.d : ℕ) : ℝ) z) j = SeqL2.coord z j := by
  let σ := r26t3_feature_enum p.d
  let i := σ j
  let n := i.1
  let α := i.2
  let c : ℕ → ℝ := fun k => SeqL2.coord z (σ.symm (k, α))
  let F : ℕ → ℝ → ℝ := fun k v =>
    r2CosBasis p.T n v * (s11p_kap k * r2CosBasis p.T k v * c k)
  have hcos : ∀ k v, r26t3_cosine p.T k v = r2CosBasis p.T k v := by
    intro k v
    unfold r26t3_cosine r2CosBasis
    split_ifs <;> simp [one_div]
  have hcoeff : ∀ k, (s21gTheta σ z).c (k, α) = c k := by
    intro k
    have h := s21gTheta_c σ z (σ.symm (k, α))
    simpa [c] using h
  have hholder := s21f_holder (m := (wholeSpaceIndex p.d : ℕ)) σ z
  have hcoef : Summable (fun k => s11p_kap k * |c k|) := by
    have hmajor : Summable (fun k => s21f_w k *
        ‖s21f_slice (m := (wholeSpaceIndex p.d : ℕ)) σ k z‖) := hholder.1
    refine Summable.of_nonneg_of_le
      (f := fun k => s21f_w k * ‖s21f_slice (m := (wholeSpaceIndex p.d : ℕ)) σ k z‖)
      (g := fun k => s11p_kap k * |c k|)
      (fun k => mul_nonneg (s11p_kap_pos k).le (abs_nonneg _)) (fun k => ?_) hmajor
    have hcθ := fp81s21_cosRecon2_coord_bound σ z k α
    have hc : |c k| ≤ ‖s21f_slice (m := (wholeSpaceIndex p.d : ℕ)) σ k z‖ := by
      calc |c k| = |(s21gTheta σ z).c (k, α)| := congrArg abs (hcoeff k).symm
        _ ≤ _ := hcθ
    calc s11p_kap k * |c k|
        ≤ s11p_kap k *
            ‖s21f_slice (m := (wholeSpaceIndex p.d : ℕ)) σ k z‖ :=
          mul_le_mul_of_nonneg_left hc (s11p_kap_pos k).le
      _ = s21f_w k *
            ‖s21f_slice (m := (wholeSpaceIndex p.d : ℕ)) σ k z‖ := by
          rw [fp81s21_cosRecon2_kap_eq]
  have hFi : ∀ k, Integrable (F k) (volume.restrict (Set.Icc (0 : ℝ) p.T)) := by
    intro k
    dsimp [F]
    have hFc : Continuous (F k) := by
      dsimp [F]
      exact (HRS.MS.R2WinOrb.s103_cosBasis_continuous p.T n).mul
        ((continuous_const.mul (HRS.MS.R2WinOrb.s103_cosBasis_continuous p.T k)).mul
          continuous_const)
    exact hFc.continuousOn.integrableOn_Icc
  have hFbound : ∀ k v, ‖F k v‖ ≤
      (Real.sqrt (2 / p.T)) ^ 2 * (s11p_kap k * |c k|) := by
    intro k v
    dsimp [F]
    change |r2CosBasis p.T n v *
      (s11p_kap k * r2CosBasis p.T k v * c k)| ≤ _
    simp only [abs_mul, abs_of_pos (s11p_kap_pos k)]
    have h1 := HRS.Whole.s11p_cos_bound p.hT n v
    have h2 := HRS.Whole.s11p_cos_bound p.hT k v
    have hInner : 0 ≤ s11p_kap k * Real.sqrt (2 / p.T) * |c k| :=
      mul_nonneg (mul_nonneg (s11p_kap_pos k).le (Real.sqrt_nonneg _)) (abs_nonneg _)
    calc |r2CosBasis p.T n v| *
          (s11p_kap k * |r2CosBasis p.T k v| * |c k|)
        ≤ |r2CosBasis p.T n v| *
            (s11p_kap k * Real.sqrt (2 / p.T) * |c k|) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left h2 (s11p_kap_pos k).le
            · exact abs_nonneg _
          · exact abs_nonneg _
        _ ≤ Real.sqrt (2 / p.T) *
            (s11p_kap k * Real.sqrt (2 / p.T) * |c k|) :=
          mul_le_mul_of_nonneg_right h1 hInner
        _ = (Real.sqrt (2 / p.T)) ^ 2 * (s11p_kap k * |c k|) := by ring
  have hsumNorm : Summable (fun k =>
      ∫ v in Set.Icc (0 : ℝ) p.T, ‖F k v‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun v => norm_nonneg _) (fun k => ?_)
      (hcoef.mul_left (p.T * (Real.sqrt (2 / p.T)) ^ 2))
    have hmono := integral_mono (hFi k).norm (integrable_const _)
      (fun v => hFbound k v)
    calc ∫ v in Set.Icc (0 : ℝ) p.T, ‖F k v‖
        ≤ ∫ _v in Set.Icc (0 : ℝ) p.T,
            (Real.sqrt (2 / p.T)) ^ 2 * (s11p_kap k * |c k|) := hmono
      _ = p.T * ((Real.sqrt (2 / p.T)) ^ 2 * (s11p_kap k * |c k|)) := by
        rw [integral_const]
        simp [Measure.real, p.hT.le]
      _ = p.T * (Real.sqrt (2 / p.T)) ^ 2 * (s11p_kap k * |c k|) := by ring
  have hcoordSeries : ∀ v : Set.Icc (0 : ℝ) p.T,
      OscDual.coord (OscPath.at' (s21gPhi σ p.hT
        ((wholeSpaceIndex p.d : ℕ) : ℝ) z) v) α =
        ∑' k, s11p_kap k * r2CosBasis p.T k v * c k := by
    intro v
    rw [s21gPhi_coord σ p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ) z v α]
    apply tsum_congr
    intro k
    rw [hcoeff k]
  have hobsIntegral :
      ∫ v in Set.Icc (0 : ℝ) p.T,
        r2CosBasis p.T n v * fp81s21_cosRecon_coordExt
          (s21gPhi σ p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ) z) α v =
      ∫ v in Set.Icc (0 : ℝ) p.T,
        r2CosBasis p.T n v * (∑' k, s11p_kap k * r2CosBasis p.T k v * c k) := by
    refine integral_congr_ae
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v hv => ?_))
    simp [fp81s21_cosRecon_coordExt, hv, hcoordSeries ⟨v, hv⟩]
  have htsum := integral_tsum_of_summable_integral_norm hFi hsumNorm
  have hseriesIntegral :
      ∫ v in Set.Icc (0 : ℝ) p.T,
        r2CosBasis p.T n v * (∑' k, s11p_kap k * r2CosBasis p.T k v * c k) =
      ∑' k, ∫ v in Set.Icc (0 : ℝ) p.T, F k v := by
    have hfun : (fun v => r2CosBasis p.T n v *
        (∑' k, s11p_kap k * r2CosBasis p.T k v * c k)) =
        fun v => ∑' k, F k v := by
      funext v
      simp [F, ← tsum_mul_left]
    rw [hfun]
    exact htsum.symm
  have htermIntegral : ∀ k, ∫ v in Set.Icc (0 : ℝ) p.T, F k v =
      if k = n then s11p_kap n * c n else 0 := by
    intro k
    have hF' : (fun v => F k v) = fun v =>
        (s11p_kap k * c k) * (r2CosBasis p.T n v * r2CosBasis p.T k v) := by
      funext v
      simp only [F]
      ring
    rw [hF', integral_const_mul, HRS.Whole.s11p_cos_orth p.hT n k]
    by_cases hk : k = n
    · subst k
      simp
    · have hnk : n ≠ k := fun h => hk h.symm
      simp [hk, hnk]
  have htermsum : (∑' k, ∫ v in Set.Icc (0 : ℝ) p.T, F k v) =
      s11p_kap n * c n := by
    rw [show (fun k => ∫ v in Set.Icc (0 : ℝ) p.T, F k v) =
        fun k => if k = n then s11p_kap n * c n else 0 from funext htermIntegral]
    rw [tsum_eq_single n]
    · simp
    · intro k hk
      simp [hk]
  have hobs := hobsIntegral.trans (hseriesIntegral.trans htermsum)
  have hcos' : ∀ k v, r26t3_cosine p.T k v = r2CosBasis p.T k v := hcos
  have hdef : fp81s21_cosRecon_obs26 p
      (s21gPhi σ p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ) z) j =
      (1 + (n : ℝ) ^ 2) ^ (3 / 8 : ℝ) *
        ∫ v in Set.Icc (0 : ℝ) p.T,
          r2CosBasis p.T n v * fp81s21_cosRecon_coordExt
            (s21gPhi σ p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ) z) α v := by
    simp [fp81s21_cosRecon_obs26, σ, i, n, α, hcos']
  rw [hdef, hobs]
  have htheta : c n = SeqL2.coord z j := by
    simp [c, σ, i, n, α]
  calc (1 + (n : ℝ) ^ 2) ^ (3 / 8 : ℝ) * (s11p_kap n * c n)
      = ((1 + (n : ℝ) ^ 2) ^ (3 / 8 : ℝ) * s11p_kap n) * c n := by ring
    _ = 1 * c n := by
      calc ((1 + (n : ℝ) ^ 2) ^ (3 / 8 : ℝ) * s11p_kap n) * c n
          = (s11p_kap n * (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8)) * c n := by ring
        _ = 1 * c n := by rw [HRS.Whole.s11p_kap_mul]
    _ = SeqL2.coord z j := by simpa [c, htheta]

/-- Particle coordinates of the centered qwin vector use the exact first marginal. -/
theorem fp81s21_cosRecon_W_coordinate
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (N : ℕ) (hN : 2 ≤ N)
    (a : ℝ) (ha : 0 ≤ a)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a))
    (X : EucConfig p.d N) (j : ℕ) :
    SeqL2.coord (r26t3_W R (r26t3_qwin R a) N X) j =
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (r26t3_qwin R a j) -
        HRS.Whole.pair (r26t3_marg R N) (r26t3_qwin R a j)) := by
  have hN1 : 1 ≤ N := by omega
  have hQ : IsProbabilityMeasure (r26t3_Q R N) :=
    (r26t3_static_pressure hδ hδhalf R hγ).1 N hN
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hMarg : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  letI : IsProbabilityMeasure (r26t3_marg R N) := hMarg
  unfold r26t3_W
  exact S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN1 hq X) j

/-- Particle qwin vectors have the feature-envelope norm bound. -/
theorem fp81s21_cosRecon_W_norm
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (N : ℕ) (hN : 2 ≤ N)
    (a : ℝ) (ha : 0 ≤ a)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a))
    (X : EucConfig p.d N) :
    ‖r26t3_W R (r26t3_qwin R a) N X‖ ≤
      2 * Real.sqrt N * featureSum (r26t3_J p.d) (r26t3_qwin R a) := by
  have hN1 : 1 ≤ N := by omega
  have hQ : IsProbabilityMeasure (r26t3_Q R N) :=
    (r26t3_static_pressure hδ hδhalf R hγ).1 N hN
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hMarg : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  letI : IsProbabilityMeasure (r26t3_marg R N) := hMarg
  unfold r26t3_W
  exact S45.s45_featureVec_norm_le hN1 hq X

#print axioms fp81s21_cosRecon_obs26_synthesis
#print axioms fp81s21_cosRecon_W_coordinate
#print axioms fp81s21_cosRecon_W_norm

end HRS.Fp81.S21

end
