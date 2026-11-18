import HRS.Commutator.Whole.XLIAux24

/-!
# X-LI part 25: the Bessel potential bound `‖f‖_p ≲ ‖J^α f‖_p`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

section BP2

variable (α : ℝ)

/-- the low-frequency symbol of `J^{-α}` -/
def thLow (η : 𝔼) : ℂ := bsymX (-α) η * cutC η

lemma thLow_contDiff : ContDiff ℝ ∞ (thLow α : 𝔼 → ℂ) :=
  (bsymX_temperate (-α)).1.mul cutC_contDiff

lemma thLow_cs : HasCompactSupport (thLow α : 𝔼 → ℂ) := cutC_cs.mul_left

lemma Pm0_eq_cv (f : SchwartzMap 𝔼 ℂ) :
    ⇑(Pm 0 f) = cv (symK (thLow α) 0) ⇑(Fm α f) := by
  funext x
  have hf : f = mulS (bsymX (-α)) (bsymX_temperate (-α)) (Fm α f) :=
    SchwartzMap.ext fun y => (congrFun (Fm_inv α f) y).symm
  have h1 := congrFun (cv_symK_eq_mulS (thLow_contDiff α) (thLow_cs α) (Fm α f) 0) x
  rw [h1]
  have h2 : (Pm 0 f) x = (mulS (fun ξ : 𝔼 => cutC (((2 : ℝ) ^ (0 : ℤ))⁻¹ • ξ))
      (temperate_symbol cutC_contDiff cutC_cs 0) (mulS (bsymX (-α)) (bsymX_temperate (-α))
        (Fm α f))) x := by
    have := congrArg (fun φ : SchwartzMap 𝔼 ℂ => (mulS (fun ξ : 𝔼 => cutC (((2 : ℝ) ^ (0 : ℤ))⁻¹ • ξ))
      (temperate_symbol cutC_contDiff cutC_cs 0) φ) x) hf
    exact this
  rw [h2, mulS_mulS _ _ (temperate_symbol cutC_contDiff cutC_cs 0) (bsymX_temperate (-α))
    ((temperate_symbol cutC_contDiff cutC_cs 0).mul (bsymX_temperate (-α)))]
  have hsym : (fun ξ : 𝔼 => cutC (((2 : ℝ) ^ (0 : ℤ))⁻¹ • ξ) * bsymX (-α) ξ) =
      fun ξ : 𝔼 => thLow α (((2 : ℝ) ^ (0 : ℤ))⁻¹ • ξ) := by
    funext ξ
    simp [thLow, mul_comm]
  exact (congrFun (congrArg (⇑) (mulS_congr hsym
    ((temperate_symbol cutC_contDiff cutC_cs 0).mul (bsymX_temperate (-α)))
    (temperate_symbol (thLow_contDiff α) (thLow_cs α) 0) (Fm α f))) x).trans rfl

lemma Pm_range (f : SchwartzMap 𝔼 ℂ) (K : ℕ) (x : 𝔼) :
    Pm (K : ℤ) f x = Pm 0 f x + ∑ k ∈ Finset.range K, Dm ((k : ℤ) + 1) f x := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h := Pm_succ ((K : ℤ) + 1) f
    rw [add_sub_cancel_right] at h
    have h' : Pm (((K + 1 : ℕ)) : ℤ) f x = Pm (K : ℤ) f x + Dm ((K : ℤ) + 1) f x := by
      have := congrFun (congrArg (⇑) h) x
      simpa using this
    rw [h', ih]
    ring

lemma geom_term_sum_ne_top (hα : 0 < α) :
    ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α)) ≠ ⊤ := by
  set q : ℝ := (2 : ℝ) ^ (-α) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) = q * q ^ k := by
    intro k
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    have : ((2 : ℝ) ^ ((k : ℤ) + 1)) = (2 : ℝ) ^ ((k : ℝ) + 1) := by
      rw [← Real.rpow_intCast]; push_cast; ring_nf
    rw [this, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
  · exact ENNReal.ofReal_ne_top
  · exact (summable_geometric_of_lt_one hq0.le hq1).mul_left _

/-- **Bessel potential bound**: `‖f‖_p ≲ ‖J^α f‖_p` for `1 ≤ p ≤ ∞` -/
lemma BP (hα : 0 < α) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f : SchwartzMap 𝔼 ℂ) (p : ℝ≥0∞), 1 ≤ p →
    eLpNorm (⇑f) p volume ≤ C * eLpNorm (⇑(Fm α f)) p volume := by
  obtain ⟨AΘ, hAΘ, hdec⟩ := dK_dec (symFam_Ths (d := d) (-α))
  set κ0 : 𝔼 → ℂ := symK (thLow α) 0 with hκ0
  have hκ0i : Integrable κ0 := symK_integrable (thLow_contDiff α) (thLow_cs α) 0
  set N0 : ℝ≥0∞ := ∫⁻ z, ‖κ0 z‖ₑ with hN0
  have hN0ne : N0 ≠ ⊤ := hκ0i.hasFiniteIntegral.ne
  set G : ℝ≥0∞ := ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α)) with hG
  have hGne : G ≠ ⊤ := geom_term_sum_ne_top α hα
  refine ⟨N0 + AΘ * KP d * G, ENNReal.add_ne_top.2 ⟨hN0ne,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hAΘ KP_ne_top) hGne⟩, fun f p hp => ?_⟩
  set F : 𝔼 → ℂ := ⇑(Fm α f) with hF
  have hFm : Measurable F := (Fm α f).continuous.measurable
  have hκ0m : Measurable κ0 := (symK_continuous (thLow_contDiff α) (thLow_cs α) 0).measurable
  have hKm : ∀ k, Measurable (dK (Ths (-α) : ℤ → 𝔼 → ℂ) k) := fun k =>
    (dK_continuous (symFam_Ths (d := d) (-α)) k).measurable
  have hcvm : ∀ k, Measurable (cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) k) F) := fun k =>
    measurable_cv (hKm k) hFm
  -- the norm of each piece
  have hpiece : ∀ k : ℕ, eLpNorm (fun x => (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) *
      cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F x) p volume ≤
      ENNReal.ofReal (((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α)) * (AΘ * KP d * eLpNorm F p volume) := by
    intro k
    have h1 : (fun x => (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) *
        cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F x) =
        (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) • cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F := by
      funext x; simp
    rw [h1, eLpNorm_const_smul]
    have hc : ‖(((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ)‖ₑ =
        ENNReal.ofReal (((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α)) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg
        (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _)]
    rw [hc]
    refine mul_le_mul_right ?_ _
    refine (eLpNorm_cv_le (hKm _) hFm hp).trans ?_
    exact mul_le_mul_left (lintegral_enorm_le_of_dec (hdec _)) _
  have hK : ∀ K : ℕ, eLpNorm (⇑(Pm (K : ℤ) f)) p volume ≤
      (N0 + AΘ * KP d * G) * eLpNorm F p volume := by
    intro K
    have heq : ⇑(Pm (K : ℤ) f) = fun x => cv κ0 F x + ∑ k ∈ Finset.range K,
        (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) *
          cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F x := by
      funext x
      rw [Pm_range, congrFun (Pm0_eq_cv α f) x]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have := delta_eq_bessel α (show -2 ≤ (k : ℤ) + 1 by omega) f x
      rw [← congrFun (cv_rho_eq_Dm _ f) x]
      exact this
    rw [heq]
    have hsum : eLpNorm (fun x => cv κ0 F x + ∑ k ∈ Finset.range K,
        (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) *
          cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F x) p volume ≤
        eLpNorm (cv κ0 F) p volume + ∑ k ∈ Finset.range K,
          eLpNorm (fun x => (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) *
            cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F x) p volume := by
      have h1 := eLpNorm_add_le (μ := volume) (f := cv κ0 F)
        (g := fun x => ∑ k ∈ Finset.range K, (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) *
          cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F x) hp
      have h2 := eLpNorm_sum_le (μ := volume) (p := p) (s := Finset.range K)
        (f := fun (k : ℕ) (x : 𝔼) => (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) *
          cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F x) hp
      refine le_trans h1 ?_
      refine add_le_add le_rfl ?_
      simpa [Finset.sum_fn] using h2
    refine hsum.trans ?_
    have h0 : eLpNorm (cv κ0 F) p volume ≤ N0 * eLpNorm F p volume := eLpNorm_cv_le hκ0m hFm hp
    calc eLpNorm (cv κ0 F) p volume + ∑ k ∈ Finset.range K,
          eLpNorm (fun x => (((((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α) : ℝ)) : ℂ) *
            cv (dK (Ths (-α) : ℤ → 𝔼 → ℂ) ((k : ℤ) + 1)) F x) p volume
        ≤ N0 * eLpNorm F p volume + ∑ k ∈ Finset.range K,
          ENNReal.ofReal (((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α)) * (AΘ * KP d * eLpNorm F p volume) :=
          add_le_add h0 (Finset.sum_le_sum fun k _ => hpiece k)
      _ ≤ N0 * eLpNorm F p volume + ∑' k : ℕ,
          ENNReal.ofReal (((2 : ℝ) ^ ((k : ℤ) + 1)) ^ (-α)) * (AΘ * KP d * eLpNorm F p volume) :=
          add_le_add le_rfl (ENNReal.sum_le_tsum _)
      _ = (N0 + AΘ * KP d * G) * eLpNorm F p volume := by
          rw [ENNReal.tsum_mul_right, ← hG]
          ring
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun K : ℕ => ⇑(Pm (K : ℤ) f))
    (Eventually.of_forall hK) (fun K => (Pm (K : ℤ) f).continuous.aestronglyMeasurable)
    f.continuous.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => tendsto_Pm_top f x

end BP2

end HRS.Commutator.Whole.XLI
