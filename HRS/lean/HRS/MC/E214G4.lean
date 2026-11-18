import HRS.MC.E214G3
import HRS.MC.E214G1
import HRS.MC.E214G2

/-!
# E214G4: from second-moment and restart inputs to the weighted coordinate-increment bound

* `lint_coord_sq_le`: `E eval(F, e_k)² ≤ C₁` gives `E coord_k(F)² ≤ C₁ ⟨k⟩^{-2r}` (as a lower integral of `ofReal`).
* `energy_of_coord`: the `E_j`-energy moment `E adjkEnergy_j(F) ≤ C₁ ∑_k ⟨k⟩^{-2j}` from coordinate moments.
* `coord_incr_of_inputs`: from the restart estimate `E‖η^t-η^s‖²_{E_r} ≤ K (t-s)` and the coordinate moments, the weighted
  coordinate increments `E (ξ_k(t)-ξ_k(s))² ≤ B |t-s|^{1/2} ⟨k⟩^{-r}` (geometric mean of the two bounds).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.AdjK

noncomputable section

namespace HRS.MC.E214G

variable {d : ℕ}

theorem coord_sq_le_norm_sq {r : ℝ} (F : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.coord F k ^ 2 ≤ ‖F‖ ^ 2 := by
  obtain ⟨hs, he⟩ := NegSobolev.coord_sq F
  rw [he]
  exact hs.le_tsum k (fun j _ => sq_nonneg _)

theorem ofReal_coord_sq_le {r : ℝ} (F : NegSobolev d r) (k : NonzeroLattice d) :
    ENNReal.ofReal (NegSobolev.coord F k ^ 2) ≤ ‖F‖ₑ ^ 2 := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (coord_sq_le_norm_sq F k)

/-- Coordinate second moment as a lower integral of `ofReal`. -/
theorem lint_coord_sq_le {r : ℝ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → NegSobolev d r)
    (k : NonzeroLattice d) {C₁ : ℝ}
    (hmem : MemLp (fun ω => NegSobolev.eval (F ω) (Torus.realMode k)) 2 P)
    (hb : ∫ ω, NegSobolev.eval (F ω) (Torus.realMode k) ^ 2 ∂P ≤ C₁) :
    ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) ∂P ≤
      ENNReal.ofReal (C₁ * Lattice.jp k.1 ^ (-(2 * r))) := by
  have hj : 0 ≤ Lattice.jp k.1 ^ (-(2 * r)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hint : Integrable (fun ω => NegSobolev.eval (F ω) (Torus.realMode k) ^ 2) P := hmem.integrable_sq
  have e1 : ∀ ω, ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) =
      ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * r))) *
        ENNReal.ofReal (NegSobolev.eval (F ω) (Torus.realMode k) ^ 2) := fun ω => by
    rw [HRS.MC.E214F.coord_sq_eq, ENNReal.ofReal_mul hj]
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _), mul_comm C₁,
    ENNReal.ofReal_mul hj]
  gcongr

theorem continuous_coord {r : ℝ} (k : NonzeroLattice d) :
    Continuous fun F : NegSobolev d r => NegSobolev.coord F k := by
  have h := HRS.MC.L2C6Aux.l2c6_eval_continuous r (HRS.FieldSingAux.isSmooth_realMode (d := d) k)
  have : (fun F : NegSobolev d r => NegSobolev.coord F k) =
      fun F => Lattice.jp k.1 ^ (-r) * NegSobolev.eval F (Torus.realMode k) := funext fun F => coord_eq_eval F k
  rw [this]
  exact continuous_const.mul h

/-- The `E_j`-energy moment from the coordinate moments. -/
theorem energy_of_coord {r j C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hj : (d : ℝ) < 2 * j) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Ω → NegSobolev d r) (hF : Measurable F)
    (h1 : ∀ k : NonzeroLattice d, ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) ∂P ≤
      ENNReal.ofReal (C₁ * Lattice.jp k.1 ^ (-(2 * r)))) :
    ∫⁻ ω, adjkEnergy j r (F ω) ∂P ≤
      ENNReal.ofReal (C₁ * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * j))) := by
  have hs := HRS.summable_jp_rpow (d := d) j hj
  have hcm : ∀ k : NonzeroLattice d, Measurable fun ω => NegSobolev.coord (F ω) k ^ 2 := fun k =>
    ((continuous_coord k).measurable.comp hF).pow_const 2
  have hjp : ∀ k : NonzeroLattice d, 0 ≤ Lattice.jp k.1 ^ (2 * (r - j)) := fun k =>
    Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hjq : ∀ k : NonzeroLattice d, 0 ≤ Lattice.jp k.1 ^ (-(2 * j)) := fun k =>
    Real.rpow_nonneg (Torus.jp_pos k.1).le _
  unfold adjkEnergy
  rw [lintegral_tsum (f := fun (k : NonzeroLattice d) ω => ENNReal.ofReal (Lattice.jp k.1 ^ (2 * (r - j)) *
    NegSobolev.coord (F ω) k ^ 2)) (fun k => (((hcm k).const_mul _).ennreal_ofReal).aemeasurable)]
  have hk : ∀ k : NonzeroLattice d, ∫⁻ ω, ENNReal.ofReal (Lattice.jp k.1 ^ (2 * (r - j)) *
      NegSobolev.coord (F ω) k ^ 2) ∂P ≤ ENNReal.ofReal (C₁ * Lattice.jp k.1 ^ (-(2 * j))) := by
    intro k
    have e1 : ∀ ω, ENNReal.ofReal (Lattice.jp k.1 ^ (2 * (r - j)) * NegSobolev.coord (F ω) k ^ 2) =
        ENNReal.ofReal (Lattice.jp k.1 ^ (2 * (r - j))) *
          ENNReal.ofReal (NegSobolev.coord (F ω) k ^ 2) := fun ω => ENNReal.ofReal_mul (hjp k)
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right (h1 k) _).trans ?_
    rw [← ENNReal.ofReal_mul (hjp k)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hj0 := Torus.jp_pos k.1
    have : Lattice.jp k.1 ^ (2 * (r - j)) * Lattice.jp k.1 ^ (-(2 * r)) = Lattice.jp k.1 ^ (-(2 * j)) := by
      rw [← Real.rpow_add hj0]; congr 1; ring
    calc Lattice.jp k.1 ^ (2 * (r - j)) * (C₁ * Lattice.jp k.1 ^ (-(2 * r)))
        = C₁ * (Lattice.jp k.1 ^ (2 * (r - j)) * Lattice.jp k.1 ^ (-(2 * r))) := by ring
      _ = C₁ * Lattice.jp k.1 ^ (-(2 * j)) := by rw [this]
  refine (ENNReal.tsum_le_tsum hk).trans ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hC₁ (hjq k)) (hs.mul_left C₁), tsum_mul_left]

/-- Weighted coordinate increments from the restart estimate and the coordinate moments (geometric mean). -/
theorem coord_incr_of_inputs {r C₁ K : ℝ} (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (η : ℝ → Ω → NegSobolev d r) (hη : ∀ t, Measurable (η t))
    (h1 : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d, ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (η t ω) k ^ 2) ∂P ≤
      ENNReal.ofReal (C₁ * Lattice.jp k.1 ^ (-(2 * r))))
    (h3 : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ s + 1 → ∫⁻ ω, ‖η t ω - η s ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (K * (t - s))) :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |t - s| ≤ 1 → ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) ^ 2) ∂P ≤
        ENNReal.ofReal (Real.sqrt (K * (4 * C₁)) * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r)) := by
  have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ s + 1 → ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) ^ 2) ∂P ≤
        ENNReal.ofReal (Real.sqrt (K * (4 * C₁)) * (t - s) ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r)) := by
    intro s t hs hst ht1 k
    set x := ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) ^ 2) ∂P with hx
    set w : ℝ := Lattice.jp k.1 ^ (-(2 * r)) with hw
    have hw0 : 0 ≤ w := Real.rpow_nonneg (Torus.jp_pos k.1).le _
    have hh0 : 0 ≤ t - s := sub_nonneg.2 hst
    have hA : x ≤ ENNReal.ofReal (K * (t - s)) := by
      refine le_trans (lintegral_mono fun ω => ?_) (h3 s t hs hst ht1)
      exact ofReal_coord_sq_le (η t ω - η s ω) k
    have hcm : ∀ u, Measurable fun ω => NegSobolev.coord (η u ω) k := fun u =>
      (continuous_coord k).measurable.comp (hη u)
    have hB : x ≤ ENNReal.ofReal (4 * C₁ * w) := by
      have hpt : ∀ ω, ENNReal.ofReal ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) ^ 2) ≤
          2 * ENNReal.ofReal (NegSobolev.coord (η t ω) k ^ 2) +
            2 * ENNReal.ofReal (NegSobolev.coord (η s ω) k ^ 2) := fun ω => by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [sq_nonneg (NegSobolev.coord (η t ω) k + NegSobolev.coord (η s ω) k)]
      have hmt : Measurable fun ω => ENNReal.ofReal (NegSobolev.coord (η t ω) k ^ 2) :=
        ((hcm t).pow_const 2).ennreal_ofReal
      refine le_trans (lintegral_mono hpt) ?_
      rw [lintegral_add_left (hmt.const_mul _), lintegral_const_mul _ hmt,
        lintegral_const_mul _ (((hcm s).pow_const 2).ennreal_ofReal)]
      have e1 := h1 t (hs.trans hst) k
      have e2 := h1 s hs k
      calc 2 * ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (η t ω) k ^ 2) ∂P +
            2 * ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (η s ω) k ^ 2) ∂P
          ≤ 2 * ENNReal.ofReal (C₁ * w) + 2 * ENNReal.ofReal (C₁ * w) := by gcongr
        _ = ENNReal.ofReal (4 * C₁ * w) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
    -- geometric mean
    have hsq : Real.sqrt (K * (t - s) * (4 * C₁ * w)) =
        Real.sqrt (K * (4 * C₁)) * (t - s) ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r) := by
      have e : K * (t - s) * (4 * C₁ * w) = (K * (4 * C₁)) * (t - s) * w := by ring
      rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (t - s),
        Real.sqrt_eq_rpow w, hw, ← Real.rpow_mul (Torus.jp_pos k.1).le]
      congr 2
      ring
    rw [← hsq]
    by_cases hab : K * (t - s) ≤ 4 * C₁ * w
    · refine hA.trans (ENNReal.ofReal_le_ofReal ?_)
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith [mul_nonneg hK hh0]
    · push Not at hab
      refine hB.trans (ENNReal.ofReal_le_ofReal ?_)
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith [mul_nonneg hC₁ hw0]
  intro s t hs ht hst k
  rcases le_total s t with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)] at hst ⊢
    exact key s t hs h (by linarith) k
  · have := key t s ht h (by rw [abs_of_nonpos (sub_nonpos.2 h)] at hst; linarith) k
    rw [abs_of_nonpos (sub_nonpos.2 h)]
    simpa [neg_sub, sub_sq_comm] using this

theorem integral_sq_le_of_lint {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hm : Measurable f) {b : ℝ} (hb : 0 ≤ b)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂P ≤ ENNReal.ofReal b) : ∫ ω, f ω ^ 2 ∂P ≤ b := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
    (hm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hb h

/-- Increments of the coordinates of `η - ηs` from the increments of the two fields. -/
theorem pair_inc_of_fields {r B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (η ηs : ℝ → Ω → NegSobolev d r) (hη : ∀ t, Measurable (η t))
    (hηs : ∀ t, Measurable (ηs t))
    (h₁ : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |t - s| ≤ 1 → ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) ^ 2) ∂P ≤
        ENNReal.ofReal (B₁ * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r)))
    (h₂ : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |t - s| ≤ 1 → ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (ηs t ω) k - NegSobolev.coord (ηs s ω) k) ^ 2) ∂P ≤
        ENNReal.ofReal (B₂ * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r))) :
    ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |t - s| ≤ 1 → ∀ k : NonzeroLattice d,
      ∫ ω, (NegSobolev.coord (η t ω - ηs t ω) k - NegSobolev.coord (η s ω - ηs s ω) k) ^ 2 ∂P ≤
        (2 * B₁ + 2 * B₂) * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r) := by
  intro s t hs ht hst k
  have hw : 0 ≤ |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
  have hb : 0 ≤ (2 * B₁ + 2 * B₂) * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r) := by
    rw [mul_assoc]; positivity
  have hc1 : ∀ u, Measurable fun ω => NegSobolev.coord (η u ω) k := fun u =>
    (continuous_coord k).measurable.comp (hη u)
  have hc2 : ∀ u, Measurable fun ω => NegSobolev.coord (ηs u ω) k := fun u =>
    (continuous_coord k).measurable.comp (hηs u)
  have e : ∀ ω, NegSobolev.coord (η t ω - ηs t ω) k - NegSobolev.coord (η s ω - ηs s ω) k =
      (NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) -
        (NegSobolev.coord (ηs t ω) k - NegSobolev.coord (ηs s ω) k) := fun ω => by
    simp only [HRS.MC.E214F.coord_sub']; ring
  refine integral_sq_le_of_lint P ?_ hb ?_
  · simp_rw [e]
    exact ((hc1 t).sub (hc1 s)).sub ((hc2 t).sub (hc2 s))
  · simp_rw [e]
    have hpt : ∀ ω, ENNReal.ofReal (((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) -
        (NegSobolev.coord (ηs t ω) k - NegSobolev.coord (ηs s ω) k)) ^ 2) ≤
        2 * ENNReal.ofReal ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) ^ 2) +
          2 * ENNReal.ofReal ((NegSobolev.coord (ηs t ω) k - NegSobolev.coord (ηs s ω) k) ^ 2) := fun ω => by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [sq_nonneg ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) +
        (NegSobolev.coord (ηs t ω) k - NegSobolev.coord (ηs s ω) k))]
    have hm1 : Measurable fun ω => ENNReal.ofReal
        ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) ^ 2) :=
      (((hc1 t).sub (hc1 s)).pow_const 2).ennreal_ofReal
    have hm2 : Measurable fun ω => ENNReal.ofReal
        ((NegSobolev.coord (ηs t ω) k - NegSobolev.coord (ηs s ω) k) ^ 2) :=
      (((hc2 t).sub (hc2 s)).pow_const 2).ennreal_ofReal
    refine le_trans (lintegral_mono hpt) ?_
    rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1, lintegral_const_mul _ hm2]
    calc 2 * ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (η t ω) k - NegSobolev.coord (η s ω) k) ^ 2) ∂P +
          2 * ∫⁻ ω, ENNReal.ofReal ((NegSobolev.coord (ηs t ω) k - NegSobolev.coord (ηs s ω) k) ^ 2) ∂P
        ≤ 2 * ENNReal.ofReal (B₁ * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r)) +
          2 * ENNReal.ofReal (B₂ * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r)) := by
          gcongr
          · exact h₁ s t hs ht hst k
          · exact h₂ s t hs ht hst k
      _ = ENNReal.ofReal ((2 * B₁ + 2 * B₂) * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r)) := by
          have hx1 : 0 ≤ B₁ * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r) := by
            rw [mul_assoc]; exact mul_nonneg hB₁ hw
          have hx2 : 0 ≤ B₂ * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r) := by
            rw [mul_assoc]; exact mul_nonneg hB₂ hw
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hx1)
              (mul_nonneg (by norm_num) hx2)]
          congr 1; ring

end HRS.MC.E214G

end
