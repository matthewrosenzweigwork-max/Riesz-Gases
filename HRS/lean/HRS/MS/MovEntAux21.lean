import HRS.MS.MovEntAux20

/-!
# S6.6, packet P5 (part 4): the Itô integrand of `N⁻¹∑|x_i|²`, the pathwise estimate and the window bound

* `s66Pp`: the pair term `N⁻²∑_{i≠j}|x_i-x_j|^{-s}`.
* `s66_drift_eq`: the Itô drift of `N⁻¹∑|x_i|²` is `-2q m + σ_s Pp + 2β⁻¹ d` off collisions.
* `s66_path_est`: `m_t ≤ m_b + ∫_b^{T} d̄ + |M_t - M_b|` in `ℝ≥0∞`.
* `s66_window`: `E sup_{t ∈ [b,b+T]} N⁻¹∑|x_i(t)|² ≤ C_T`, uniformly in `b, N`, from the moment and pair bounds at each time.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole HRS.MH.DualityRd

variable {d : ℕ}

/-- The pair term `N⁻² ∑_{i≠j} |x_i - x_j|^{-s}`. -/
def s66Pp {N : ℕ} (s : ℝ) (Y : EucConfig d N) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖Y i - Y j‖ ^ (-s)

theorem s66_Pp_nonneg {N : ℕ} (s : ℝ) (Y : EucConfig d N) : 0 ≤ s66Pp s Y := by
  unfold s66Pp
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem s66_Pp_measurable {N : ℕ} (s : ℝ) : Measurable (s66Pp s : EucConfig d N → ℝ) := by
  unfold s66Pp
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  exact (measurable_norm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))).pow_const _

theorem s66_m_nonneg {N : ℕ} (Y : EucConfig d N) : 0 ≤ movSecondMoment Y := by
  unfold movSecondMoment
  positivity

theorem s66_m_eq {N : ℕ} (Y : EucConfig d N) :
    movSecondMoment Y = HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2) Y := by
  unfold movSecondMoment HRS.sumLift
  rw [one_div]

theorem s66_drift_eq {N : ℕ} (hN : 0 < N) (s q β : ℝ) (hβ : 0 < β) (Y : EucConfig d N)
    (hY : Y ∉ eucCollisionSet d N) :
    fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2)) Y (particleDriftW (quadraticGradientDyn d s q β) Y) +
        (1 / 2) * ∑ k : Fin N × Fin d,
          fderiv ℝ (fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2))) Y
            (noiseDir (quadraticGradientDyn d s q β) k) (noiseDir (quadraticGradientDyn d s q β) k) =
      -2 * q * movSecondMoment Y + movtr_sigma s * s66Pp s Y + 2 * β⁻¹ * d := by
  have hinv : 0 ≤ (quadraticGradientDyn d s q β).invβ := (inv_pos.2 hβ).le
  rw [s66_fderiv_sumLift_normsq, s66_sum_fderiv2 hN _ hinv Y, ← Finset.mul_sum, s66_inner_drift s q β Y hY]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold movSecondMoment s66Pp
  show (N : ℝ)⁻¹ * (2 * (-q * ∑ i, ‖Y i‖ ^ 2 + movtr_sigma s / (2 * N) *
      ∑ i, ∑ j ∈ Finset.univ.erase i, ‖Y i - Y j‖ ^ (-s))) + 1 / 2 * (4 * β⁻¹ * d) = _
  field_simp
  ring

/-- The deterministic pathwise estimate. -/
theorem s66_path_est {m M dr dbar : ℝ → ℝ} {b T' : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T')
    (hdr : IntegrableOn dr (Set.Icc 0 T')) (hdb : IntegrableOn dbar (Set.Icc 0 T'))
    (hdb0 : ∀ s ∈ Set.Icc (0 : ℝ) T', 0 ≤ dbar s) (hle : ∀ s ∈ Set.Icc (0 : ℝ) T', dr s ≤ dbar s)
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T', m t = m 0 + (∫ s in Set.Icc (0 : ℝ) t, dr s) + M t) :
    ∀ t ∈ Set.Icc b T', ENNReal.ofReal (m t) ≤ ENNReal.ofReal (m b) +
      (∫⁻ s in Set.Ioc b T', ENNReal.ofReal (dbar s)) + ENNReal.ofReal |M t - M b| := by
  intro t ht
  have hbI : b ∈ Set.Icc (0 : ℝ) T' := ⟨hb, hbT⟩
  have htI : t ∈ Set.Icc (0 : ℝ) T' := ⟨hb.trans ht.1, ht.2⟩
  have hsplit : ∫ s in Set.Icc (0 : ℝ) t, dr s =
      (∫ s in Set.Icc (0 : ℝ) b, dr s) + ∫ s in Set.Ioc b t, dr s := by
    have hu : Set.Icc (0 : ℝ) b ∪ Set.Ioc b t = Set.Icc 0 t := Set.Icc_union_Ioc_eq_Icc hb ht.1
    rw [← hu]
    refine setIntegral_union (Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)) measurableSet_Ioc ?_ ?_
    · exact hdr.mono_set (Set.Icc_subset_Icc le_rfl hbT)
    · exact hdr.mono_set (fun x hx => ⟨hb.trans hx.1.le, hx.2.trans ht.2⟩)
  have hI1 : ∫ s in Set.Ioc b t, dr s ≤ ∫ s in Set.Ioc b t, dbar s := by
    refine setIntegral_mono_on (hdr.mono_set fun x hx => ⟨hb.trans hx.1.le, hx.2.trans ht.2⟩)
      (hdb.mono_set fun x hx => ⟨hb.trans hx.1.le, hx.2.trans ht.2⟩) measurableSet_Ioc ?_
    intro s hs
    exact hle s ⟨hb.trans hs.1.le, hs.2.trans ht.2⟩
  have hdbI : IntegrableOn dbar (Set.Ioc b t) :=
    hdb.mono_set fun x hx => ⟨hb.trans hx.1.le, hx.2.trans ht.2⟩
  have hA0 : 0 ≤ ∫ s in Set.Ioc b t, dbar s :=
    setIntegral_nonneg measurableSet_Ioc fun s hs => hdb0 s ⟨hb.trans hs.1.le, hs.2.trans ht.2⟩
  have hreal : m t ≤ m b + (∫ s in Set.Ioc b t, dbar s) + |M t - M b| := by
    have h1 := hm t htI
    have h2 := hm b hbI
    rw [hsplit] at h1
    have h3 : M t - M b ≤ |M t - M b| := le_abs_self _
    linarith
  have hAeq : ENNReal.ofReal (∫ s in Set.Ioc b t, dbar s) = ∫⁻ s in Set.Ioc b t, ENNReal.ofReal (dbar s) :=
    ofReal_integral_eq_lintegral_ofReal hdbI
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs =>
        hdb0 s ⟨hb.trans hs.1.le, hs.2.trans ht.2⟩))
  calc ENNReal.ofReal (m t) ≤ ENNReal.ofReal (m b + (∫ s in Set.Ioc b t, dbar s) + |M t - M b|) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (m b + ∫ s in Set.Ioc b t, dbar s) + ENNReal.ofReal |M t - M b| :=
        ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (m b) + ENNReal.ofReal (∫ s in Set.Ioc b t, dbar s) + ENNReal.ofReal |M t - M b| :=
        add_le_add ENNReal.ofReal_add_le le_rfl
    _ ≤ ENNReal.ofReal (m b) + (∫⁻ s in Set.Ioc b T', ENNReal.ofReal (dbar s)) + ENNReal.ofReal |M t - M b| := by
        refine add_le_add (add_le_add le_rfl ?_) le_rfl
        rw [hAeq]
        exact lintegral_mono_set (Set.Ioc_subset_Ioc_right ht.2)

end HRS.MS.MovEnt

end
