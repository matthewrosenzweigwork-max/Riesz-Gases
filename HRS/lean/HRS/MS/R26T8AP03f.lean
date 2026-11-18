import HRS.MS.R26T8AP03e

/-!
# S8.2 local Newton layer, packet T8A.P03 (part f): the separated annular Newton integral, general bound
`r26t8a_sep_bound`: if the annulus is separated from `z` (`r0 <= |z-w| <= r1` for `R/2 <= |w| <= 2R`) and `B` bounds `D^q K` on
`r0 <= |u| <= r1`, then the nested jet of the annular Newton integral is `<= C A <X>^{2M} R^{d-sigma} (1+|log R|)^b B`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_ball_volume (R : ℝ) (hR : 0 < R) :
    (volume (Metric.closedBall (0 : Euc d) (2 * R))).toReal =
      (volume (Metric.ball (0 : Euc d) 1)).toReal * (2 ^ d * R ^ d) := by
  rw [Measure.addHaar_closedBall _ _ (by positivity : (0 : ℝ) ≤ 2 * R), finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), mul_pow]
  ring

/-- Pointwise bound of the `Y`-jet of a product `s(Y) . v` with a fixed vector. -/
theorem r26t8a_smul_const_jet_norm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Euc d → ℝ} {p : ℕ} {X : Euc d}
    (hs : ContDiffAt ℝ (p : WithTop ℕ∞) s X) (v : V) :
    ‖iteratedFDeriv ℝ p (fun Y => s Y • v) X‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ p s X‖ := by
  have h1 : (fun Y => s Y • v) = (ContinuousLinearMap.toSpanSingleton ℝ v) ∘ s := by
    funext Y; simp
  rw [h1]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hs le_rfl).trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton]

theorem r26t8a_zero_curry_jet {G : Euc d → Euc d → ℝ} {p : ℕ} {X : Euc d} (w : Euc d)
    (hs : ContDiffAt ℝ (p : WithTop ℕ∞) (fun Y => G Y w) X) :
    ‖iteratedFDeriv ℝ p (fun Y => G Y w) X‖ =
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ 0 (fun w' => G Y w') w) X‖ := by
  have h1 : (fun Y => iteratedFDeriv ℝ 0 (fun w' => G Y w') w) =
      (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm ∘ (fun Y => G Y w) := by
    funext Y; rw [iteratedFDeriv_zero_eq_comp]; rfl
  rw [h1]
  exact ((continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.norm_iteratedFDeriv_comp_left _ X p).symm

theorem r26t8a_sep_bound {k b : ℕ} {M sigma : ℝ} (hM : 0 ≤ M) (hsigma : 0 ≤ sigma)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {nu : ℝ}
    (hK : ContDiffOn ℝ ∞ (newtonKernel d nu) {z | z ≠ 0}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal k b M sigma A F →
      ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ r0 r1 : ℝ, 0 < r0 → r0 ≤ r1 → ∀ z : Euc d,
      (∀ w : Euc d, R / 2 ≤ ‖w‖ → ‖w‖ ≤ 2 * R → r0 ≤ ‖z - w‖ ∧ ‖z - w‖ ≤ r1) →
      ∀ q : ℕ, ∀ B : ℝ, 0 ≤ B →
      (∀ u : Euc d, r0 ≤ ‖u‖ → ‖u‖ ≤ r1 → ‖iteratedFDeriv ℝ q (newtonKernel d nu) u‖ ≤ B) →
      ∀ p : ℕ, p + q ≤ k → ∀ X : Euc d,
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (r26t8a_annularNewton nu chi R F Y) z) X‖ ≤
          C * A * jbracket X ^ (2 * M) * R ^ ((d : ℝ) - sigma) * (1 + |Real.log R|) ^ b * B := by
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_annular_source (d := d) k b M sigma hM hsigma chi hchi
  set Vd : ℝ := (volume (Metric.ball (0 : Euc d) 1)).toReal with hVd
  have hVd0 : 0 ≤ Vd := ENNReal.toReal_nonneg
  refine ⟨C1 * (Vd * 2 ^ d), by positivity, fun A hA F hF R hR hR1 r0 r1 hr0 hr01 z hgeo q B hB0 hB p hpq X => ?_⟩
  obtain ⟨-, hsrc⟩ := hC1 A hA F hF R hR hR1
  rw [r26t8a_sep_formula hchi hK hR hF.1 hr0 hr01 hgeo hpq X]
  set c : ℝ := C1 * A * jbracket X ^ (2 * M) * R ^ (-sigma) * (1 + |Real.log R|) ^ b with hc
  have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (by unfold jbracket; positivity) _
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hr1 : 0 < r1 := hr0.trans_le hr01
  set Kt := r26t8a_truncK chi nu r0 r1 with hKt
  have hSd : ContDiff ℝ k (fun Yw : Euc d × Euc d => r26t8a_annulus chi R Yw.2 * midPair F Yw.1 Yw.2) :=
    r26t8a_S_contDiff hchi hR hF.1
  have hpt : ∀ w : Euc d, ‖iteratedFDeriv ℝ p (fun Y => (chi (Y - X) *
      (r26t8a_annulus chi R w * midPair F Y w)) • iteratedFDeriv ℝ q Kt (z - w)) X‖ ≤
        (Metric.closedBall (0 : Euc d) (2 * R)).indicator (fun _ => c * B) w := by
    intro w
    have hind0 : 0 ≤ (Metric.closedBall (0 : Euc d) (2 * R)).indicator (fun _ => c * B) w :=
      Set.indicator_nonneg (fun _ _ => mul_nonneg hc0 hB0) w
    have hzero : r26t8a_annulus chi R w = 0 →
        ‖iteratedFDeriv ℝ p (fun Y => (chi (Y - X) *
          (r26t8a_annulus chi R w * midPair F Y w)) • iteratedFDeriv ℝ q Kt (z - w)) X‖ ≤
          (Metric.closedBall (0 : Euc d) (2 * R)).indicator (fun _ => c * B) w := by
      intro h0
      have e : (fun Y => (chi (Y - X) * (r26t8a_annulus chi R w * midPair F Y w)) •
          iteratedFDeriv ℝ q Kt (z - w)) = fun _ => 0 := by
        funext Y; simp [h0]
      rw [e, iteratedFDeriv_fun_zero]
      simpa using hind0
    by_cases ha : r26t8a_annulus chi R w = 0
    · exact hzero ha
    obtain ⟨hw1, hw2⟩ := r26t8a_annulus_ne_zero hchi hR ha
    obtain ⟨hg0, hg1⟩ := hgeo w hw1.le hw2.le
    have hmem : w ∈ Metric.closedBall (0 : Euc d) (2 * R) := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hw2.le
    rw [Set.indicator_of_mem hmem]
    have hTeq : iteratedFDeriv ℝ q Kt (z - w) = iteratedFDeriv ℝ q (newtonKernel d nu) (z - w) := by
      have hev : Kt =ᶠ[𝓝 (z - w)] newtonKernel d nu := by
        have hopen : IsOpen {u : Euc d | r0 / 2 < ‖u‖ ∧ ‖u‖ < 2 * r1} :=
          (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
        filter_upwards [hopen.mem_nhds (show r0 / 2 < ‖z - w‖ ∧ ‖z - w‖ < 2 * r1 from
          ⟨by linarith, by linarith⟩)] with u hu
        exact r26t8a_truncK_eq hchi hr0 hr1 hu.1.le hu.2.le
      exact (hev.iteratedFDeriv ℝ q).eq_of_nhds
    set v := iteratedFDeriv ℝ q (newtonKernel d nu) (z - w) with hv
    have hvB : ‖v‖ ≤ B := hB _ hg0 hg1
    rw [hTeq]
    have hloc : (fun Y => (chi (Y - X) * (r26t8a_annulus chi R w * midPair F Y w)) • v) =ᶠ[𝓝 X]
        fun Y => (r26t8a_annulus chi R w * midPair F Y w) • v := by
      have hopen : IsOpen {Y : Euc d | ‖Y - X‖ < 1} :=
        isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
      filter_upwards [hopen.mem_nhds (by simp)] with Y hY
      simp only [hchi.2.2.2.1 _ (le_of_lt (show ‖Y - X‖ < 1 from hY)), one_mul]
    rw [(hloc.iteratedFDeriv ℝ p).eq_of_nhds]
    have hgd : ContDiffAt ℝ (p : WithTop ℕ∞) (fun Y => r26t8a_annulus chi R w * midPair F Y w) X :=
      (hSd.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.of_le (by exact_mod_cast (by omega : p ≤ k))
    refine (r26t8a_smul_const_jet_norm hgd v).trans ?_
    have h1 := hsrc p 0 (by omega) X w
    simp only [Nat.cast_zero, add_zero] at h1
    have h2 : ‖iteratedFDeriv ℝ p (fun Y => r26t8a_annulus chi R w * midPair F Y w) X‖ ≤ c := by
      rw [r26t8a_zero_curry_jet (G := fun Y w' => r26t8a_annulus chi R w' * midPair F Y w') w hgd]
      exact h1
    calc _ ≤ B * c := mul_le_mul hvB h2 (norm_nonneg _) hB0
      _ = c * B := mul_comm _ _
  have hint : Integrable ((Metric.closedBall (0 : Euc d) (2 * R)).indicator fun _ => c * B) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
  have hR' : R ^ ((d : ℝ) - sigma) = R ^ d * R ^ (-sigma) := by
    rw [sub_eq_add_neg, Real.rpow_add hR, Real.rpow_natCast]
  calc _ ≤ ∫ w, (Metric.closedBall (0 : Euc d) (2 * R)).indicator (fun _ => c * B) w :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = (volume (Metric.closedBall (0 : Euc d) (2 * R))).toReal * (c * B) := by
        rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, smul_eq_mul]
        rfl
    _ = _ := by
        rw [r26t8a_ball_volume R hR, hc, hR']
        ring

end HRS.MS.R26T8A
