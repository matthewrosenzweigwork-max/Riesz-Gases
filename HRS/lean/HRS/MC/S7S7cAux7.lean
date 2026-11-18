import HRS.MC.S7S7cAux6

/-!
# Packet `s7_S7c_hilbert_stein`, helper 7: Fourier truncation in `E_r` and integrability of `||W_N||`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

open Classical

variable {d : ℕ}

/-! ### Truncation -/

theorem s7c_norm_trunc_le {r : ℝ} (K : Finset (NonzeroLattice d)) (x : NegSobolev d r) :
    ‖truncE K x‖ ≤ ‖x‖ := by
  have h1 := lp_norm_sq (show lp (fun _ : NonzeroLattice d => ℝ) 2 from truncE K x)
  have h2 := lp_norm_sq (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x)
  have hs := lp_sq_summable (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x)
  have hle : ‖truncE K x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have e1 : ‖truncE K x‖ ^ 2 = ∑' k : NonzeroLattice d, (NegSobolev.coord (truncE K x) k) ^ 2 := h1
    have e2 : ‖x‖ ^ 2 = ∑' k : NonzeroLattice d, (NegSobolev.coord x k) ^ 2 := h2
    rw [e1, e2]
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ hs
    · rw [coord_truncE]
      split_ifs
      · exact le_rfl
      · simpa using sq_nonneg (NegSobolev.coord x k)
    · exact lp_sq_summable (show lp (fun _ : NonzeroLattice d => ℝ) 2 from truncE K x)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hle

theorem s7c_tendsto_trunc {r : ℝ} (x : NegSobolev d r) :
    Tendsto (fun K : Finset (NonzeroLattice d) => truncE K x) atTop (𝓝 x) := by
  have h := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by simp)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x)
  have e : ∀ K : Finset (NonzeroLattice d), truncE K x =
      ∑ i ∈ K, (lp.single 2 i ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from x) i) :
        lp (fun _ : NonzeroLattice d => ℝ) 2) := by
    intro K
    show ∑ i ∈ K, (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x) i •
      (lp.single 2 i (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2) = _
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← lp.single_smul]
    simp
  exact h.congr fun K => (e K).symm

/-! ### The index set `Fin K.card` -/

def s7c_kap (K : Finset (NonzeroLattice d)) : Fin K.card → NonzeroLattice d :=
  fun a => (K.equivFin.symm a).1

theorem s7c_sum_kap {M : Type*} [AddCommMonoid M] (K : Finset (NonzeroLattice d))
    (g : NonzeroLattice d → M) : ∑ b : Fin K.card, g (s7c_kap K b) = ∑ k ∈ K, g k := by
  unfold s7c_kap
  rw [Equiv.sum_comp K.equivFin.symm (fun k : K => g k.1)]
  exact Finset.sum_coe_sort K g

theorem s7c_Wtr_kap {r : ℝ} (hr : (d : ℝ) < 2 * r) {N : ℕ} (hN : 1 ≤ N)
    (Q : Measure (Config d N)) [IsProbabilityMeasure Q] (K : Finset (NonzeroLattice d))
    (X : Config d N) : s7c_Wtr r Q (s7c_kap K) X = truncE K (zetaE r Q X) := by
  rw [s7c_Wtr_eq, s7c_sum_kap K (fun k => sed_Y Q (s7_phi r k) X • s7_eps r k)]
  show _ = ∑ k ∈ K, NegSobolev.coord (zetaE r Q X) k • (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [s7c_coord_zeta hN hr Q X k]
  rfl

theorem s7c_sedY_meas {N : ℕ} (hN : 1 ≤ N) (Q : Measure (Config d N)) {w : Torus d → ℝ}
    (hw : Continuous w) : Measurable (sed_Y Q w) := by
  unfold sed_Y
  exact measurable_const.mul ((HRS.MC.SEdge.B5b.b5b_pair_meas hN hw.measurable).sub_const _)

theorem s7c_summable_jp {r : ℝ} (hr : (d : ℝ) < r) :
    Summable (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-r)) := by
  have := summable_jp_rpow (d := d) (r / 2) (by linarith)
  simpa [show 2 * (r / 2) = r by ring] using this

theorem s7c_W_integrable {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ}
    (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6)
    {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun X => ‖zetaE r (sed_Q d s N γ ρ) X‖) (sed_Q d s N γ ρ) := by
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hr'' : (d : ℝ) < r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  obtain ⟨c0, hc0, hW⟩ := s7c_Wk_L1 (r := r) hd hs0 hs hγ hρ
  set Q := sed_Q d s N γ ρ with hQdef
  have hWm := s7c_zeta_meas hN hr' Q
  have hYm : ∀ k : NonzeroLattice d, Measurable (sed_Y Q (s7_phi r k)) := fun k =>
    s7c_sedY_meas hN Q (HRS.Q66.q66_cont_of_smooth (HRS.MC.Sec7.S7a.s7a_phi_smooth r k))
  have hsum : Summable (fun k : NonzeroLattice d => c0 * Lattice.jp k.1 ^ (-r)) :=
    (s7c_summable_jp hr'').mul_left c0
  refine ⟨(measurable_norm.comp hWm).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hpt : ∀ X : Config d N, ‖‖zetaE r Q X‖‖ₑ ≤
      ∑' k : NonzeroLattice d, ‖sed_Y Q (s7_phi r k) X‖ₑ := by
    intro X
    rw [enorm_norm]
    have h := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by simp)
      (show lp (fun _ : NonzeroLattice d => ℝ) 2 from zetaE r Q X)
    refine h.enorm_le_of_bounded (g := fun k => ‖sed_Y Q (s7_phi r k) X‖ₑ)
      ENNReal.summable.hasSum fun k => ?_
    have hn := lp.norm_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num) k
      ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from zetaE r Q X) k)
    rw [← ofReal_norm_eq_enorm, hn, ofReal_norm_eq_enorm, ← s7c_coord_zeta hN hr' Q X k]
    rfl
  calc ∫⁻ X, ‖‖zetaE r Q X‖‖ₑ ∂Q ≤ ∫⁻ X, ∑' k : NonzeroLattice d, ‖sed_Y Q (s7_phi r k) X‖ₑ ∂Q :=
        lintegral_mono hpt
    _ = ∑' k : NonzeroLattice d, ∫⁻ X, ‖sed_Y Q (s7_phi r k) X‖ₑ ∂Q :=
        lintegral_tsum fun k => (hYm k).enorm.aemeasurable
    _ ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal (c0 * Lattice.jp k.1 ^ (-r)) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        obtain ⟨hint, hb⟩ := hW N hN k
        rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
        exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hb)
    _ = ENNReal.ofReal (∑' k : NonzeroLattice d, c0 * Lattice.jp k.1 ^ (-r)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => by have := Torus.jp_pos k.1; positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end HRS.MC.Sec7.S7c

end
