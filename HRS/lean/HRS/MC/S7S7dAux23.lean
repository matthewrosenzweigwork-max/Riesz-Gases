import HRS.MC.S7S7dAux22
import HRS.MC.S7S7dAux19

/-!
# Packet `s7_S7d_uniform_limits`, helper 23: the limit (R2), uniformly over the unit ball

Splits the double series over `(k, l)` into a finite block `S × S` (where the pair estimate `s7d_pair_R2` applies) and a tail
controlled by the weights `b_k b_l`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_main_R2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (NegSobolev d r) 5,
      |∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d,
          ∫ X, Real.sqrt N * (sed_A (v k) (s7_phi r l) X -
              ∫ Y, sed_A (v k) (s7_phi r l) Y ∂(sed_Q d s N γ ρ)) *
            iteratedFDeriv ℝ 2 (steinSolG G Φ) (zetaE r (sed_Q d s N γ ρ) X)
              ![s7_eps r k, s7_eps r l] ∂(sed_Q d s N γ ρ) -
        ∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
          (∫ x, a j x * sed_drift (v k) (s7_phi r l) x ∂(withDensityReal ρ)) *
            ∫ F, iteratedFDeriv ℝ 3 (steinSolG G Φ) F ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G| ≤ ε := by
  classical
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨C₀', Cd, hC₀', hCd, ha, hdr, -⟩ := s7d_mode_bounds hr hmode
  obtain ⟨C1, hC1, hY1⟩ := HRS.MC.Sec7.S7b.s7b_Y_moment hd hs0 hs hγ hρ 1
  have hb0 : ∀ k : NonzeroLattice d, 0 < s7_b k := s7d_b_pos
  have hbs : Summable (fun k : NonzeroLattice d => s7_b k) := s7d_b_summable
  set Sb : ℝ := ∑' k : NonzeroLattice d, s7_b k with hSb
  have hSb0 : 0 ≤ Sb := tsum_nonneg fun k => (hb0 k).le
  -- the observables
  set w : NonzeroLattice d → NonzeroLattice d → Torus d → ℝ := fun k l => sed_drift (v k) (s7_phi r l)
    with hwdef
  have hws : ∀ k l, Torus.IsSmooth (w k l) := fun k l =>
    HRS.MC.Sec7.S7b.s7b_drift_smooth (hmode.smooth_v k) (HRS.MC.Sec7.S7a.s7a_phi_smooth r l)
  set T : NonzeroLattice d → NonzeroLattice d → ℝ := fun k l => (Cd + 1) * (s7_b k * s7_b l) with hTdef
  have hT0 : ∀ k l, 0 < T k l := fun k l => by
    have := hb0 k; have := hb0 l; positivity
  have hwT : ∀ k l x, |w k l x| ≤ T k l := fun k l x =>
    (hdr k l x).trans (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (hb0 k).le (hb0 l).le))
  have hQ : ∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (sed_Q d s N γ ρ) := fun N hN =>
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hYm : ∀ N, 1 ≤ N → ∀ k l, Measurable (sed_Y (sed_Q d s N γ ρ) (w k l)) := fun N hN k l =>
    haveI := hQ N hN
    HRS.MC.Sec7.S7c.s7c_sedY_meas hN _ (HRS.Q66.q66_cont_of_smooth (hws k l))
  have hY2 : ∀ N, 1 ≤ N → ∀ k l,
      Integrable (fun X => sed_Y (sed_Q d s N γ ρ) (w k l) X ^ 2) (sed_Q d s N γ ρ) := fun N hN k l => by
    haveI := hQ N hN
    simpa [sq_abs] using s7d_sedY_pow_integrable hN (sed_Q d s N γ ρ)
      (HRS.Q66.q66_cont_of_smooth (hws k l)) (hwT k l) 2
  have hYsq : ∀ N, 1 ≤ N → ∀ k l,
      ∫ X, sed_Y (sed_Q d s N γ ρ) (w k l) X ^ 2 ∂(sed_Q d s N γ ρ) ≤ C1 * T k l ^ 2 := fun N hN k l => by
    have := hY1 (w k l) (T k l) (hws k l) (hwT k l) N hN
    simpa [sq_abs] using this
  -- coefficient bounds
  set c1 : ℝ := (1 + C1) * (Cd + 1) / 2 with hc1
  set c2 : ℝ := C₀' * (Cd + 1) * Sb with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  set τ : NonzeroLattice d → NonzeroLattice d → NonzeroLattice d → ℝ := fun k l j => C₀' * T k l * s7_b j
    with hτdef
  have hτ0 : ∀ k l j, 0 ≤ τ k l j := fun k l j => by
    have := hT0 k l; have := hb0 j; positivity
  have hτs : ∀ k l, Summable (τ k l) := fun k l => hbs.mul_left _
  have hτb : ∀ k l j, |∫ x, a j x * w k l x ∂(withDensityReal ρ)| ≤ τ k l j := fun k l j => by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
      (f := fun x => a j x * w k l x) (C := C₀' * T k l * s7_b j)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 := ha j x
        have h2 := hwT k l x
        calc |a j x| * |w k l x| ≤ (C₀' * s7_b j) * T k l :=
              mul_le_mul h1 h2 (abs_nonneg _) (by have := hb0 j; positivity)
          _ = C₀' * T k l * s7_b j := by ring)
    simpa [Real.norm_eq_abs] using this
  have hτsum : ∀ k l, ∑' j, τ k l j = c2 * (s7_b k * s7_b l) := fun k l => by
    simp only [hτdef, hTdef]
    rw [tsum_mul_left]
    simp only [hc2, hSb]
    ring
  -- Step 1: choose `S`
  obtain ⟨S, hS⟩ := (s7d_tail2_eventually (τ := fun k : NonzeroLattice d => s7_b k) hbs
    (fun k => (hb0 k).le) (c := c1 + c2) (δ := ε / 4) (by positivity) (by positivity)).exists
  set η : ℝ := ε / (2 * ((S.card : ℝ) ^ 2 + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- Step 2: pair estimates
  have hpair := fun k l => s7d_pair_R2 (r := r) hd hs0 hs hr hγ hρ hmode G hG (hws k l) (hτs k l)
    (hτ0 k l) (hτb k l) (C2 := C1 * T k l ^ 2) (fun N hN => hYsq N hN k l) hη0
  choose N₀f hN₀f using hpair
  refine ⟨S.sup fun k => S.sup fun l => N₀f k l, fun N hN hN1 Φ hΦ => ?_⟩
  haveI := hQ N hN1
  set Q := sed_Q d s N γ ρ with hQdef
  have hf : s7d_Cl (steinSolG G Φ) := s7d_stein_cl G hG.1 hΦ
  set f := steinSolG G Φ with hfdef
  set F1 : NonzeroLattice d → NonzeroLattice d → ℝ := fun k l =>
    ∫ X, sed_Y Q (w k l) X * iteratedFDeriv ℝ 2 f (zetaE r Q X) ![s7_eps r k, s7_eps r l] ∂Q with hF1
  set F2 : NonzeroLattice d → NonzeroLattice d → ℝ := fun k l =>
    ∑' j, (∫ x, a j x * w k l x ∂(withDensityReal ρ)) *
      ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G with hF2
  have hε1 : ∀ k : NonzeroLattice d, ‖s7_eps r k‖ ≤ 1 := fun k => le_of_eq (HRS.MC.Sec7.S7c.s7c_norm_eps r k)
  -- bounds
  have hF1b : ∀ k l, |F1 k l| ≤ c1 * (s7_b k * s7_b l) := fun k l => by
    have hΘ := s7d_Th_D2 hf (s7_eps r k) (s7_eps r l) (hε1 k) (hε1 l)
    obtain ⟨hI, hI2⟩ := s7d_L1_of_L2 Q (hYm N hN1 k l) (hY2 N hN1 k l) (hYsq N hN1 k l) (hT0 k l)
    have hint : Integrable (fun X => sed_Y Q (w k l) X *
        iteratedFDeriv ℝ 2 f (zetaE r Q X) ![s7_eps r k, s7_eps r l]) Q := by
      refine hI.mono' ?_ (Eventually.of_forall fun X => ?_)
      · exact (hYm N hN1 k l).aestronglyMeasurable.mul
          (hΘ.1.measurable.comp (HRS.MC.Sec7.S7c.s7c_zeta_meas hN1 hr' Q)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        calc _ ≤ |sed_Y Q (w k l) X| * 1 := mul_le_mul_of_nonneg_left (hΘ.2.1 (zetaE r Q X)) (abs_nonneg _)
          _ = _ := mul_one _
    have h1 : |F1 k l| ≤ ∫ X, |sed_Y Q (w k l) X| ∂Q := by
      have := norm_integral_le_of_norm_le (μ := Q)
        (f := fun X => sed_Y Q (w k l) X * iteratedFDeriv ℝ 2 f (zetaE r Q X) ![s7_eps r k, s7_eps r l]) hI
        (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_mul]
        calc _ ≤ |sed_Y Q (w k l) X| * 1 := mul_le_mul_of_nonneg_left (hΘ.2.1 (zetaE r Q X)) (abs_nonneg _)
          _ = _ := mul_one _)
      simpa [Real.norm_eq_abs, hF1] using this
    refine h1.trans (hI2.trans (le_of_eq ?_))
    simp only [hc1, hTdef]; ring
  have hF2b : ∀ k l, |F2 k l| ≤ c2 * (s7_b k * s7_b l) := fun k l => by
    have hF : ∀ j, |(∫ x, a j x * w k l x ∂(withDensityReal ρ)) *
        ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G| ≤ τ k l j := fun j => by
      rw [abs_mul]
      calc _ ≤ τ k l j * 1 := mul_le_mul (hτb k l j)
            (s7d_Th_abs_int G (s7d_Th_D3 hf _ _ _ (hε1 k) (hε1 l) (hε1 j))) (abs_nonneg _) (hτ0 k l j)
        _ = _ := mul_one _
    have := s7d_tsum1_tail (hτs k l) hF ∅
    simp only [Finset.sum_empty, sub_zero] at this
    rw [hτsum k l] at this
    exact this
  have hT1 := s7d_tsum2_tail (F := F1) hbs (fun k => (hb0 k).le) hc10 hF1b S
  have hT2 := s7d_tsum2_tail (F := F2) hbs (fun k => (hb0 k).le) hc20 hF2b S
  have hX : 0 ≤ Sb ^ 2 - (∑ i ∈ S, s7_b i) ^ 2 := by
    have h1 := hbs.sum_le_tsum S (fun j _ => (hb0 j).le)
    have h2 : 0 ≤ ∑ i ∈ S, s7_b i := Finset.sum_nonneg fun j _ => (hb0 j).le
    nlinarith
  have hfin : |∑ k ∈ S, ∑ l ∈ S, F1 k l - ∑ k ∈ S, ∑ l ∈ S, F2 k l| ≤ (S.card : ℝ) ^ 2 * η := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hk : ∀ k ∈ S, |∑ l ∈ S, (F1 k l - F2 k l)| ≤ S.card * η := fun k hk => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l ∈ S, |F1 k l - F2 k l| ≤ ∑ l ∈ S, η := Finset.sum_le_sum fun l hl => ?_
        _ = S.card * η := by simp
      have hge : N₀f k l ≤ N := hN.trans' (le_trans
        (Finset.le_sup (f := fun l => N₀f k l) hl) (Finset.le_sup (f := fun k => S.sup fun l => N₀f k l) hk))
      exact hN₀f k l N hge hN1 f hf (s7_eps r k) (s7_eps r l) (hε1 k) (hε1 l)
    calc ∑ k ∈ S, |∑ l ∈ S, (F1 k l - F2 k l)| ≤ ∑ k ∈ S, (S.card * η) := Finset.sum_le_sum hk
      _ = (S.card : ℝ) ^ 2 * η := by simp; ring
  have hcη : (S.card : ℝ) ^ 2 * η ≤ ε / 2 := by
    rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  show |∑' k, ∑' l, F1 k l - ∑' k, ∑' l, F2 k l| ≤ ε
  have h1 : c1 * (Sb ^ 2 - (∑ i ∈ S, s7_b i) ^ 2) ≤ ε / 4 := by
    have := mul_nonneg hc20 hX
    nlinarith
  have h2 : c2 * (Sb ^ 2 - (∑ i ∈ S, s7_b i) ^ 2) ≤ ε / 4 := by
    have := mul_nonneg hc10 hX
    nlinarith
  calc |∑' k, ∑' l, F1 k l - ∑' k, ∑' l, F2 k l|
      = |((∑' k, ∑' l, F1 k l) - ∑ k ∈ S, ∑ l ∈ S, F1 k l) +
        (∑ k ∈ S, ∑ l ∈ S, F1 k l - ∑ k ∈ S, ∑ l ∈ S, F2 k l) +
        (∑ k ∈ S, ∑ l ∈ S, F2 k l - ∑' k, ∑' l, F2 k l)| := by congr 1; ring
    _ ≤ |(∑' k, ∑' l, F1 k l) - ∑ k ∈ S, ∑ l ∈ S, F1 k l| +
        |∑ k ∈ S, ∑ l ∈ S, F1 k l - ∑ k ∈ S, ∑ l ∈ S, F2 k l| +
        |∑ k ∈ S, ∑ l ∈ S, F2 k l - ∑' k, ∑' l, F2 k l| := abs_add_three _ _ _
    _ ≤ ε / 4 + ε / 2 + ε / 4 := by
        refine add_le_add (add_le_add (hT1.trans h1) (hfin.trans hcη)) ?_
        rw [abs_sub_comm]; exact hT2.trans h2
    _ = ε := by ring

end HRS.MC.Sec7.S7d

end
