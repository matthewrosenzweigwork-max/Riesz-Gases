import HRS.MC.S7S7dAux23
import HRS.MC.S7S7dAux20

/-!
# Packet `s7_S7d_uniform_limits`, helper 24: the limit (R3), uniformly over the unit ball

For `0 < γ`: splits the series over `k` into a finite block (single-mode estimate `s7d_pair_R3`) and a tail controlled by `b_k`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_main_R3 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 < γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ Φ ∈ CbUnitBall (NegSobolev d r) 5,
      |∑' k : NonzeroLattice d, ∫ X, sed_B d s ρ γ (v k) X *
            fderiv ℝ (steinSolG G Φ) (zetaE r (sed_Q d s N γ ρ) X) (s7_eps r k)
            ∂(sed_Q d s N γ ρ) -
        (1 / 2) * ∑' k : NonzeroLattice d, ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
          sed_Qt d s ρ (v k) (a l) (a j) *
            ∫ F, iteratedFDeriv ℝ 3 (steinSolG G Φ) F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G| ≤ ε := by
  classical
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨C₀', Cd, hC₀', hCd, ha, -, hLip⟩ := s7d_mode_bounds hr hmode
  obtain ⟨CB, hCB0, hCB⟩ := HRS.MC.Sec7.S7c.s7c_B_mode hd hs0 hs hγ.le hρ hmode
  obtain ⟨Cm4, hm4⟩ := HRS.MC.Sec7.S7b.s7_S7b_weighted_moments_proof hd hs0 hs r hr hγ.le hρ hmode 2
  obtain ⟨Cm2, hm2⟩ := HRS.MC.Sec7.S7b.s7_S7b_weighted_moments_proof hd hs0 hs r hr hγ.le hρ hmode 1
  obtain ⟨Gq, hGq0, hGq⟩ := s7d_Qt_bound hd hs0 hs hρ
  have hb0 : ∀ k : NonzeroLattice d, 0 < s7_b k := s7d_b_pos
  have hbs : Summable (fun k : NonzeroLattice d => s7_b k) := s7d_b_summable
  set Sb : ℝ := ∑' k : NonzeroLattice d, s7_b k with hSb
  have hSb0 : 0 ≤ Sb := tsum_nonneg fun k => (hb0 k).le
  set cQ0 : ℝ := C₀' ^ 3 * (1 + Gq) * d / 2 with hcQ0
  have hcQ00 : 0 ≤ cQ0 := by positivity
  have hQb : ∀ k l j : NonzeroLattice d,
      |sed_Qt d s ρ (v k) (a l) (a j)| ≤ (cQ0 * s7_b k) * (s7_b l * s7_b j) := fun k l j => by
    have := hGq (v k) (L := C₀' * s7_b k) (by have := hb0 k; positivity) (hLip k) (hmode.smooth_v k)
      (HRS.Q66.q66_cont_of_smooth (hmode.smooth_a l)) (HRS.Q66.q66_cont_of_smooth (hmode.smooth_a j))
      (ha l) (ha j)
    refine this.trans (le_of_eq ?_)
    simp only [hcQ0]; ring
  have hQ : ∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (sed_Q d s N γ ρ) := fun N hN =>
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ.le hρ N hN
  have hε1 : ∀ k : NonzeroLattice d, ‖s7_eps r k‖ ≤ 1 := fun k =>
    le_of_eq (HRS.MC.Sec7.S7c.s7c_norm_eps r k)
  set c2 : ℝ := cQ0 * Sb ^ 2 / 2 with hc2
  have hc20 : 0 ≤ c2 := by positivity
  -- Step 1: choose `S`
  have hev := (tendsto_order.1 (s7d_tail_tendsto hbs)).2 (ε / (4 * (CB + c2 + 1))) (by positivity)
  obtain ⟨S, hS⟩ := hev.exists
  set η : ℝ := ε / (2 * ((S.card : ℝ) + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- Step 2: single-mode estimates
  have hpair := fun k => s7d_pair_R3 (r := r) hd hs0 hs hr hγ hρ hmode G hG (hmode.smooth_v k)
    (C2 := Cm2 * s7_b k ^ (2 * 1))
    ⟨Cm4 * s7_b k ^ (2 * 2), fun N hN => (hm4 N hN k k).2.1 hγ⟩ (fun N hN => (hm2 N hN k k).2.1 hγ)
    (τ := fun j => s7_b j) hbs (fun j => (hb0 j).le) (cQ := cQ0 * s7_b k)
    (by have := hb0 k; positivity) (hQb k) hη0
  choose N₀f hN₀f using hpair
  refine ⟨S.sup N₀f, fun N hN hN1 Φ hΦ => ?_⟩
  haveI := hQ N hN1
  set Q := sed_Q d s N γ ρ with hQdef
  have hf : s7d_Cl (steinSolG G Φ) := s7d_stein_cl G hG.1 hΦ
  set f := steinSolG G Φ with hfdef
  set F1 : NonzeroLattice d → ℝ := fun k =>
    ∫ X, sed_B d s ρ γ (v k) X * fderiv ℝ f (zetaE r Q X) (s7_eps r k) ∂Q with hF1
  set F2 : NonzeroLattice d → ℝ := fun k => (1 / 2) * ∑' l : NonzeroLattice d, ∑' j : NonzeroLattice d,
      sed_Qt d s ρ (v k) (a l) (a j) *
        ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G with hF2
  have hF1b : ∀ k, |F1 k| ≤ CB * s7_b k := fun k => by
    have hΘ := s7d_Th_D1 hf (s7_eps r k) (hε1 k)
    obtain ⟨hBi, hBb⟩ := hCB N hN1 k
    have hBm : Measurable (fun X : Config d N => sed_B d s ρ γ (v k) X) :=
      s7d_B_meas hd hs0 hs hγ hρ (hmode.smooth_v k) hN1
    have hI : Integrable (fun X => |sed_B d s ρ γ (v k) X|) Q := hBi.abs
    have hpt : ∀ X, ‖sed_B d s ρ γ (v k) X * fderiv ℝ f (zetaE r Q X) (s7_eps r k)‖ ≤
        |sed_B d s ρ γ (v k) X| := fun X => by
      rw [Real.norm_eq_abs, abs_mul]
      calc _ ≤ |sed_B d s ρ γ (v k) X| * 1 :=
            mul_le_mul_of_nonneg_left (hΘ.2.1 (zetaE r Q X)) (abs_nonneg _)
        _ = _ := mul_one _
    have h1 := norm_integral_le_of_norm_le (μ := Q)
      (f := fun X => sed_B d s ρ γ (v k) X * fderiv ℝ f (zetaE r Q X) (s7_eps r k)) hI
      (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans hBb
  have hF2b : ∀ k, |F2 k| ≤ c2 * s7_b k := fun k => by
    have hF : ∀ l j : NonzeroLattice d, |sed_Qt d s ρ (v k) (a l) (a j) *
        ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G| ≤
          (cQ0 * s7_b k) * (s7_b l * s7_b j) := fun l j => by
      rw [abs_mul]
      calc _ ≤ ((cQ0 * s7_b k) * (s7_b l * s7_b j)) * 1 := mul_le_mul (hQb k l j)
            (s7d_Th_abs_int G (s7d_Th_D3 hf _ _ _ (hε1 l) (hε1 j) (hε1 k))) (abs_nonneg _)
            (by have := hb0 k; have := hb0 l; have := hb0 j; positivity)
        _ = _ := mul_one _
    have h := s7d_tsum2_tail (F := fun l j => sed_Qt d s ρ (v k) (a l) (a j) *
        ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G) hbs
      (fun k => (hb0 k).le) (by have := hb0 k; positivity) hF ∅
    simp only [Finset.sum_empty, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h
    simp only [hF2, abs_mul]
    calc |(1 / 2 : ℝ)| * |∑' l, ∑' j, sed_Qt d s ρ (v k) (a l) (a j) *
          ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G|
        ≤ (1 / 2) * ((cQ0 * s7_b k) * Sb ^ 2) := by
          rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left h (by norm_num)
      _ = c2 * s7_b k := by simp only [hc2]; ring
  have hT1 : |(∑' k, F1 k) - ∑ k ∈ S, F1 k| ≤ CB * (Sb - ∑ i ∈ S, s7_b i) := by
    have := s7d_tsum1_tail (F := F1) (b := fun k => CB * s7_b k) (hbs.mul_left _) hF1b S
    rw [show ∑' k, CB * s7_b k = CB * Sb from tsum_mul_left,
      show ∑ k ∈ S, CB * s7_b k = CB * ∑ i ∈ S, s7_b i from (Finset.mul_sum _ _ _).symm, ← mul_sub] at this
    exact this
  have hT2 : |(∑' k, F2 k) - ∑ k ∈ S, F2 k| ≤ c2 * (Sb - ∑ i ∈ S, s7_b i) := by
    have := s7d_tsum1_tail (F := F2) (b := fun k => c2 * s7_b k) (hbs.mul_left _) hF2b S
    rw [show ∑' k, c2 * s7_b k = c2 * Sb from tsum_mul_left,
      show ∑ k ∈ S, c2 * s7_b k = c2 * ∑ i ∈ S, s7_b i from (Finset.mul_sum _ _ _).symm, ← mul_sub] at this
    exact this
  have hX : Sb - ∑ i ∈ S, s7_b i < ε / (4 * (CB + c2 + 1)) := hS
  have hXn : 0 ≤ Sb - ∑ i ∈ S, s7_b i := by
    have := hbs.sum_le_tsum S (fun j _ => (hb0 j).le); linarith
  have hcX : (CB + c2) * (Sb - ∑ i ∈ S, s7_b i) ≤ ε / 4 := by
    have h1 : (CB + c2) * (Sb - ∑ i ∈ S, s7_b i) ≤ (CB + c2) * (ε / (4 * (CB + c2 + 1))) :=
      mul_le_mul_of_nonneg_left hX.le (by positivity)
    refine h1.trans ?_
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hfin : |∑ k ∈ S, F1 k - ∑ k ∈ S, F2 k| ≤ (S.card : ℝ) * η := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ S, |F1 k - F2 k| ≤ ∑ k ∈ S, η := Finset.sum_le_sum fun k hk => ?_
      _ = S.card * η := by simp
    have hge : N₀f k ≤ N := hN.trans' (Finset.le_sup (f := N₀f) hk)
    have h := hN₀f k N hge hN1 f hf (s7_eps r k) (hε1 k)
    have e : ∀ l j : NonzeroLattice d, ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r k, s7_eps r l, s7_eps r j] ∂G =
        ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G := fun l j =>
      integral_congr_ae (Eventually.of_forall fun F => s7d_D3_cyc (hf.1.of_le (by norm_num)) F _ _ _)
    simp only [e] at h
    exact h
  have hcη : (S.card : ℝ) * η ≤ ε / 2 := by
    rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hhalf : (1 / 2 : ℝ) * ∑' k, ∑' l, ∑' j, sed_Qt d s ρ (v k) (a l) (a j) *
      ∫ F, iteratedFDeriv ℝ 3 f F ![s7_eps r l, s7_eps r j, s7_eps r k] ∂G = ∑' k, F2 k := by
    simp only [hF2]; rw [tsum_mul_left]
  rw [hhalf]
  show |∑' k, F1 k - ∑' k, F2 k| ≤ ε
  calc |∑' k, F1 k - ∑' k, F2 k|
      = |((∑' k, F1 k) - ∑ k ∈ S, F1 k) + (∑ k ∈ S, F1 k - ∑ k ∈ S, F2 k) +
        (∑ k ∈ S, F2 k - ∑' k, F2 k)| := by congr 1; ring
    _ ≤ |(∑' k, F1 k) - ∑ k ∈ S, F1 k| + |∑ k ∈ S, F1 k - ∑ k ∈ S, F2 k| +
        |∑ k ∈ S, F2 k - ∑' k, F2 k| := abs_add_three _ _ _
    _ ≤ CB * (Sb - ∑ i ∈ S, s7_b i) + ε / 2 + c2 * (Sb - ∑ i ∈ S, s7_b i) := by
        refine add_le_add (add_le_add hT1 (hfin.trans hcη)) ?_
        rw [abs_sub_comm]; exact hT2
    _ ≤ ε := by nlinarith

end HRS.MC.Sec7.S7d

end
