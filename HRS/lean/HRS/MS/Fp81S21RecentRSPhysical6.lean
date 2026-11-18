import HRS.MS.Fp81S21RecentRSPhysical4
import HRS.MS.Fp81S21GaussianPhysicalIncrements
import HRS.MS.Fp81S21MovingStd3

/-! Simultaneous compatibility with the supplied continuous Gaussian prediction.
Countable reconstruction is applied to two continuous predictions, never to an
uncountable family of raw almost-everywhere coefficient identities. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

local instance fp81s21_recentRS6_meas (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_recentRS6_borel (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

private theorem fp81s21_recentRS6_coeff_ext
    {d k : ℕ} {w : ℝ} (E : r26t6_WeightedChart d k w) (x y : r26t6_Coeff)
    (h : ∀ f, IsR2Test f → fp81s21_chartAction E x f = fp81s21_chartAction E y f) :
    x = y := by
  ext i
  have he : E.encode (E.test i) = (lp.single 2 i (1 : ℝ) : r26t6_Coeff) := by
    ext j
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  have hi := h (E.test i) (E.test_smooth i)
  simpa [fp81s21_chartAction, he, lp.inner_single_right] using hi

/-- Arbitrary realization and supplied continuous prediction with its physical
section certificate. The canonical family and packet-33 chart are literally Q's.
Two countable dense sets give one event before either time quantifier. -/
theorem fp81s21_recentRS_gaussian_prediction_restrict_supplied
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (Q : fp81s21_Physical35 p R)
    (G : GaussianRealization R)
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a)
    (Y : G.Ω → C(I (a + p.T), Window p))
    (hY : ∀ r : I (a + p.T), ∀ τ : I p.T, ∀ᵐ ω ∂G.P,
      OscPath.at' (Y ω r) τ =
        r2Vprop (r26t3_coeff R) (m p) (a + τ) (min (r : ℝ) (a + τ))
          (fp81s21_chartAction Q.E
            (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G)
              (min (r : ℝ) (a + τ)) ω)))
    (X : G.Ω → CH (L + p.T))
    (hX : CD Q.E G.P (fun u ω f => OscDual.eval (G.Z u ω) f)
      (max (a - L) 0) (L + p.T) X)
    (hmean : (∫ ω, X ω ∂G.P) = 0)
    (P : CH (L + p.T) →L[ℝ] YH p (L + p.T)) (hP : PSpec p R Q.E L a P) :
    ∀ᵐ ω ∂G.P, ∀ v : I (L + p.T),
      P (cen G.P X ω) v = fp81s21_remote_G_extend G a ha Y ω
        (max (a - L) 0 + min (v : ℝ) (a - max (a - L) 0 + p.T)) := by
  let b := max (a - L) 0
  let h := a - b + p.T
  have hg := recent_geometry L a hL ha
  have hb : 0 ≤ b := hg.1
  have hθ : 0 ≤ a - b := hg.2.1
  have hh : 0 ≤ h := add_nonneg hθ p.hT.le
  let cut : I (L + p.T) → I (a + p.T) := fun v =>
    ⟨b + min (v : ℝ) h, add_nonneg hb (le_min v.property.1 hh), by
      have := min_le_right (v : ℝ) h
      dsimp [h] at *
      linarith⟩
  have hcut : Continuous cut :=
    (continuous_const.add (continuous_subtype_val.min continuous_const)).subtype_mk _
  have hsec (s : I (L + p.T)) :
      (fun ω => X ω s) =ᵐ[G.P]
        fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G) (b + (s : ℝ)) := by
    have hc := ((Q.canon.payload G).coefficients.weak_momentRep.2
      (b + (s : ℝ)) (add_nonneg hb s.property.1)).2.2
    filter_upwards [hX.2.2, hc] with ω hx hq
    apply fp81s21_recentRS6_coeff_ext Q.E
    intro f hf
    exact (hx s f hf).trans (hq.1 f hf).symm
  have hfixed (v : I (L + p.T)) (τ : I p.T) :
      ∀ᵐ ω ∂G.P, OscPath.at' (P (cen G.P X ω) v) τ =
        OscPath.at' (Y ω (cut v)) τ := by
    let s : I (L + p.T) := ⟨min (v : ℝ) (a - b + (τ : ℝ)),
      le_min v.property.1 (add_nonneg hθ τ.property.1),
      (min_le_left _ _).trans v.property.2⟩
    have htime : b + (s : ℝ) = min (cut v : ℝ) (a + (τ : ℝ)) := by
      change b + min (v : ℝ) (a - b + (τ : ℝ)) =
        min (b + min (v : ℝ) h) (a + (τ : ℝ))
      dsimp [h]
      simp only [min_def]
      split_ifs <;> linarith [τ.property.2]
    filter_upwards [hsec s, hY (cut v) τ] with ω hx hw
    have hp := hP (X ω) v τ s.property
    simp only [cen, hmean, sub_zero]
    rw [hw]
    change OscPath.at' (P (X ω) v) τ = _
    change OscPath.at' (P (X ω) v) τ =
      r2Vprop (r26t3_coeff R) (m p) (a + (τ : ℝ)) (b + (s : ℝ))
        (fp81s21_chartAction Q.E (X ω s)) at hp
    rw [hp, hx, htime]
  letI : Nonempty (I (L + p.T)) := ⟨⟨0, le_rfl, (add_pos hL p.hT).le⟩⟩
  letI : Nonempty (I p.T) := ⟨⟨0, le_rfl, p.hT.le⟩⟩
  let vs : ℕ → I (L + p.T) := TopologicalSpace.denseSeq _
  let ts : ℕ → I p.T := TopologicalSpace.denseSeq _
  have hv : DenseRange vs := TopologicalSpace.denseRange_denseSeq _
  have ht : DenseRange ts := TopologicalSpace.denseRange_denseSeq _
  have hcount : ∀ᵐ ω ∂G.P, ∀ n : ℕ, ∀ k : ℕ,
      OscPath.at' (P (cen G.P X ω) (vs n)) (ts k) =
        OscPath.at' (Y ω (cut (vs n))) (ts k) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hfixed (vs n) (ts k)
  filter_upwards [hcount] with ω hω
  have hpaths (n : ℕ) : P (cen G.P X ω) (vs n) = Y ω (cut (vs n)) := by
    apply ContinuousMap.ext
    exact congrFun (DenseRange.equalizer ht
      (P (cen G.P X ω) (vs n)).continuous
      (Y ω (cut (vs n))).continuous (funext (hω n)))
  have hall := DenseRange.equalizer hv (P (cen G.P X ω)).continuous
    ((Y ω).continuous.comp hcut) (funext hpaths)
  intro v
  have he := congrFun hall v
  change P (cen G.P X ω) v = Y ω (cut v) at he
  rw [he]
  change Y ω (cut v) = Y ω (projIcc 0 (a + p.T) _ (cut v : ℝ))
  rw [projIcc_val]


/-- Same-field simultaneous increments for arbitrary supplied histories. The
moving-standard input precedes Q; neither interval operator is reselected. -/
theorem fp81s21_recentRS_gaussian_increments_of_std
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (coef : MultiIndex p.d → ℝ)
    (hstd : Fp81MovingStd (r26t3_coeff R) (m p) (a + p.T)
      (2 * p.d + 8) coef (add_pos_of_nonneg_of_pos ha p.hT))
    (Q : fp81s21_Physical35 p R) (G : GaussianRealization R)
    (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))))
    (hUG : fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G)) Q.MUG 0 (a + p.T) UG)
    (hUB : fp81s21_TimeL2Rep G.P (Q.S.qe G)
      (Q.S.Kstar ^ 4 * Q.S.B / 2) 0 (a + p.T) UB) :
    (∀ᵐ ω ∂G.P, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
      fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) UB v ω -
        fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) UB u ω =
      fp81s21_weightedDrift_windowInc ha le_rfl (r26t3_coeff R)
        (fun s f => fp81s21_chartAction Q.E (Q.S.qe G s ω) f) u v) ∧
    (∀ᵐ ω ∂G.P, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => fp81s21_chartAction Q.E
          (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G) s ω) f) (Ioc u v)
        ((fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) UG v ω -
          fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) UG u ω :
            projTensor (Window p) 2) : TensorDual (Window p) 2)) := by
  have hH := add_pos_of_nonneg_of_pos ha p.hT
  have hPw : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  have hchart := fp81s21_moving_charted_orbits p R hH hstd hPw Q.E
  have hB0 := fp81s21_quadraticPhysical31_zero_mass p R Q.Es Q.E Q.S G (a + p.T) hH.le
  exact ⟨fp81s21_gaussian_Dcum_physical_simultaneous Q.E (r26t3_coeff R)
    G.P (Q.S.qe G) (Q.S.Kstar ^ 4 * Q.S.B / 2) a p.T Q.cD Q.KD
    ha p.hT Q.hcD.le Q.hKD (Q.OD a ha) coef hstd.hD
    (fp81s21_S102Lin p R (a + p.T)) hchart hPw UB hUB hB0,
    fp81s21_gaussian_Jcum_physical_simultaneous Q.E (r26t3_coeff R)
      G.P (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q G)) Q.MUG
      a p.T Q.cJ Q.KJ ha p.hT Q.hcJ.le Q.hKJ (Q.OJ a ha) UG hUG⟩

/-- One moving-standard radius precedes every Q and yields both simultaneous
increment certificates for its literal retained source and origin histories. -/
theorem fp81s21_recentRS_gaussian_increments (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∀ (a : ℝ) (ha : 0 ≤ a),
      (∀ᵐ ω ∂Q.src.G0.P, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
        fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) v ω -
          fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) u ω =
        fp81s21_weightedDrift_windowInc ha le_rfl (r26t3_coeff R)
          (fun s f => fp81s21_chartAction Q.E (Q.S.qe Q.src.G0 s ω) f) u v) ∧
      (∀ᵐ ω ∂Q.src.G0.P, ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
        fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
          (fun s f => fp81s21_chartAction Q.E
            (fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection s ω) f) (Ioc u v)
          ((fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) v ω -
            fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) u ω :
              projTensor (Window p) 2) : TensorDual (Window p) 2))) := by
  obtain ⟨δ₀, hδ₀, hhalf, hstd⟩ := fp81s21_moving_std p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q a ha
  obtain ⟨coef, hdata⟩ := hstd δ hδ hδle R a ha
  exact fp81s21_recentRS_gaussian_increments_of_std p R a ha coef hdata Q Q.src.G0
    (Q.UG a ha) (Q.UB a ha) (Q.hUG a ha) (Q.hUB a ha)

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recentRS_gaussian_prediction_restrict_supplied
#print axioms HRS.Fp81.S21.fp81s21_recentRS_gaussian_increments_of_std
#print axioms HRS.Fp81.S21.fp81s21_recentRS_gaussian_increments
end
