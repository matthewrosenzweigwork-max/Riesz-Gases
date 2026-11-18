import HRS.MS.S104eEx3
import HRS.MS.S104eC0

/-!
# S104E route C, packet C5 part B: the density path in `U2Dec`

`s104e_sqrt_leib`: `‖D^k(√ρ_β u)(x)‖ ≤ K E e^{-c|x|²}` linearly in `E` (bound of the jets of `u`).
`c5_rho_unif`: `ρ^t ∈ U2Dec N n A` uniformly in `t ≥ 0` (no smallness of `ε_*`).
`c5_rho_cont`: `t ↦ ρ^t` is continuous in `U2Dec N n` (the difference `ρ^r - ρ^{r₀}` is in `U2Dec N n ε` for `r` close to `r₀`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r

variable {d : ℕ}

theorem s104e_sqrt_leib {ρβ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (hq : 0 < q')
    (hR : HRS.MS.Gap.GapRef d ρβ q' B) (n : ℕ) :
    ∃ c K0 : ℝ, 0 < c ∧ 0 ≤ K0 ∧ ∀ (u : Euc d → ℝ) (E : ℝ), 0 ≤ E → ContDiff ℝ (n : WithTop ℕ∞) u →
      (∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k u x‖ ≤ E) →
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => Real.sqrt (ρβ x) * u x) ∧
      ∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun x => Real.sqrt (ρβ x) * u x) x‖ ≤
        K0 * E * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨hss, -, cs, hcs, hsb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq hR
  choose Cs hCs using hsb
  set Ps : ℝ := ∑ k ∈ Finset.range (n + 1), |Cs k| with hPs
  have hPs0 : 0 ≤ Ps := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hsk : ∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρβ y)) x‖ ≤
      Ps * Real.exp (-cs * ‖x‖ ^ 2) := by
    intro k hk x
    refine (hCs k x).trans ?_
    have h2 : Cs k ≤ Ps := by
      calc Cs k ≤ |Cs k| := le_abs_self _
        _ ≤ Ps := Finset.single_le_sum (f := fun k => |Cs k|) (fun k _ => abs_nonneg _)
            (Finset.mem_range.2 (by omega))
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  refine ⟨cs, 2 ^ n * Ps, hcs, by positivity, fun u E hE hu hub => ?_⟩
  have hsn : ContDiff ℝ (n : WithTop ℕ∞) (fun y => Real.sqrt (ρβ y)) := hss.of_le (by simp)
  refine ⟨hsn.mul hu, fun k hk x => ?_⟩
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsn hu x (n := k) (by exact_mod_cast hk)
  have hex0 : 0 ≤ Real.exp (-cs * ‖x‖ ^ 2) := (Real.exp_pos _).le
  have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => Real.sqrt (ρβ y)) x‖ *
      ‖iteratedFDeriv ℝ (k - i) u x‖ ≤ (k.choose i : ℝ) * (Ps * Real.exp (-cs * ‖x‖ ^ 2) * E) := by
    intro i hi
    have hik : i ≤ n := by have := Finset.mem_range.1 hi; omega
    have : ‖iteratedFDeriv ℝ i (fun y => Real.sqrt (ρβ y)) x‖ * ‖iteratedFDeriv ℝ (k - i) u x‖ ≤
        Ps * Real.exp (-cs * ‖x‖ ^ 2) * E :=
      mul_le_mul (hsk i hik x) (hub (k - i) (by omega) x) (norm_nonneg _) (by positivity)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  refine hL.trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul]
  have hch : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by exact_mod_cast Nat.sum_range_choose k
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hk
  have h8 : 0 ≤ Ps * Real.exp (-cs * ‖x‖ ^ 2) * E := by positivity
  rw [hch]
  calc (2 : ℝ) ^ k * (Ps * Real.exp (-cs * ‖x‖ ^ 2) * E) ≤ 2 ^ n * (Ps * Real.exp (-cs * ‖x‖ ^ 2) * E) :=
        mul_le_mul_of_nonneg_right h2k h8
    _ = 2 ^ n * Ps * E * Real.exp (-cs * ‖x‖ ^ 2) := by ring

theorem c5_rho_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) (N n : ℕ) (hN : N ≤ 100 * d + 1000) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 ≤ t → U2Dec N (n : ℝ) A (ρ t) := by
  obtain ⟨c, K, hc, hK0, hG⟩ := s104e_gauss_rho hd hs0 hsd ha hβ εstar c₁ C₁ N hN hρβ hres
  obtain ⟨P, hP0, hP⟩ := s104e_u2dec_of_gauss (d := d) hc N n
  exact ⟨P * K, by positivity, fun t ht => hP (ρ t) K hK0 (hG t ht).1 (hG t ht).2⟩

theorem c5_rho_cont (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) (N n : ℕ) (hN : N ≤ 100 * d + 1000) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) :
    ∀ T : ℝ, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ r₀ ∈ Icc (0 : ℝ) T, |r - r₀| < δ →
      U2Dec N (n : ℝ) e (fun y => ρ r y - ρ r₀ y) := by
  obtain ⟨B, hBdef, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρβ
  have hq : 0 < β * a := mul_pos hβ ha
  have hpos : ∀ x, 0 < ρβ x := hR.pos
  have hρβc : Continuous ρβ := hR.smooth.continuous
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 102 * d + 1020 := ⟨_, rfl⟩
  have hmR : (m : ℝ) = 102 * (d : ℝ) + 1020 := by rw [hm]; push_cast; ring
  have hm1 : (d : ℝ) / 2 + (N : ℝ) + 2 < m := by
    rw [hmR]
    have h1 : (N : ℝ) ≤ 100 * (d : ℝ) + 1000 := by exact_mod_cast hN
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cv, hCv0, hCv⟩ := mn_force_bound hd hs0 hsd β a hβ ha ρβ hρβ N m hm1
  obtain ⟨c, K0, hc, hK0, hSL⟩ := s104e_sqrt_leib hq hR N
  obtain ⟨P, hP0, hP⟩ := s104e_u2dec_of_gauss (d := d) hc N n
  set v : ℝ → Euc d → ℝ := fun t x => (ρ t x - ρβ x) / Real.sqrt (ρβ x) with hv
  have hvc : ∀ t, 0 ≤ t → Continuous (v t) := fun t ht =>
    ((hres.regular t ht).sub hρβc).div hρβc.sqrt (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
  have hvm : ∀ t, 0 ≤ t → MemOsc (m : ℝ) (v t) := fun t ht => by
    rw [hmR]; exact (hres.weighted t ht).1
  have hcont : ContinuousOn (fun t : ℝ => OscSpace.ofFun (d := d) (m : ℝ) (v t)) (Ici 0) := by
    rw [hmR]; exact hres.cont
  intro T e he
  set M₀ : ℝ := P * (K0 * Cv) + 1 with hM₀
  have hM₀pos : 0 < M₀ := by positivity
  have hUC := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    (hcont.mono Icc_subset_Ici_self)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 hUC (e / M₀) (by positivity)
  refine ⟨δ, hδ, fun r hrT r₀ hr₀T hrd => ?_⟩
  have hr : 0 ≤ r := hrT.1
  have hr₀ : 0 ≤ r₀ := hr₀T.1
  have hdist := hδ' r hrT r₀ hr₀T (by rwa [Real.dist_eq])
  set D := dist (OscSpace.ofFun (d := d) (m : ℝ) (v r)) (OscSpace.ofFun (d := d) (m : ℝ) (v r₀)) with hDd
  have hwm := HRS.MS.MovLin.mov2d_memOsc_sub (hvm r hr) (hvm r₀ hr₀)
  have hwc : Continuous (fun z => v r z - v r₀ z) := (hvc r hr).sub (hvc r₀ hr₀)
  have hDn : oscNorm (m : ℝ) (fun z => v r z - v r₀ z) = D := by
    rw [hDd, dist_eq_norm, ← HRS.MS.MovLin.mov2d_ofFun_sub (hvm r hr) (hvm r₀ hr₀),
      OscSpace.norm_ofFun _ hwm]
  obtain ⟨hw2, hsup, -⟩ := hCv _ hwc hwm
  have hD0 : 0 ≤ D := dist_nonneg
  have hu : ContDiff ℝ (N : WithTop ℕ∞) (fun z => v r z - v r₀ z) :=
    hw2.of_le (by exact_mod_cast (by omega : N ≤ N + 2))
  have hub : ∀ k ≤ N, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun z => v r z - v r₀ z) x‖ ≤ Cv * D := fun k hk x => by
    have := hsup k (by omega) x
    rwa [hDn] at this
  obtain ⟨hs1, hs2⟩ := hSL _ (Cv * D) (by positivity) hu hub
  have heq : (fun y => ρ r y - ρ r₀ y) = fun x => Real.sqrt (ρβ x) * (v r x - v r₀ x) := by
    funext x
    have hsq : 0 < Real.sqrt (ρβ x) := Real.sqrt_pos.2 (hpos x)
    simp only [hv]; field_simp; ring
  rw [heq]
  have := hP (fun x => Real.sqrt (ρβ x) * (v r x - v r₀ x)) (K0 * (Cv * D)) (by positivity) hs1
    (fun k hk x => by have := hs2 k hk x; linarith)
  have hdist' : D < e / M₀ := by rw [hDd]; exact hdist
  have hle : P * (K0 * (Cv * D)) ≤ e := by
    calc P * (K0 * (Cv * D)) = (P * (K0 * Cv)) * D := by ring
      _ ≤ M₀ * D := mul_le_mul_of_nonneg_right (by linarith) hD0
      _ ≤ e := by
        have := (lt_div_iff₀ hM₀pos).1 hdist'
        nlinarith
  exact ⟨this.1, fun m hm y => (this.2 m hm y).trans
    (mul_le_mul_of_nonneg_right hle (u2Wt_pos _ y).le)⟩

end HRS.MS.S104e
