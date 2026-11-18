import HRS.MS.MovSchAux3

/-!
# S64 (S6.4 `mov_schwartz`), part 4: weighted bounds of `ρ_u - ρ` and of `div Y_u`

Namespace `HRS.MS.MovSch`, prefix `s64_`.
* `s64_Y_W`: for `‖u‖ ≤ R`, `Y_u ∈ s64_W (K+1) L` with constant `MY ‖u‖`.
* `s64_out`: for `‖u‖ ≤ R`: `ρ_u = ρ + h_u ∈ C^K`, `div Y_u ∈ C^K` and for all `k ≤ K`, `x`:
  `⟨x⟩^L (‖D^k (ρ_u - ρ) x‖ + ‖D^k (div Y_u) x‖) ≤ M ‖u‖` with `M` independent of `u`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ} {m K : ℕ}

lemma s64_Y_W (H : Mov2dTh d s β q ρ) (hmK : (K : ℝ) + d / 2 + 4 < m) (L : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ MY : ℝ, 0 ≤ MY ∧ ∀ u : OscSpace d (m : ℝ), ‖u‖ ≤ R →
      s64_W (K + 1) L (mneY d s q β ρ (s64_hm3 hmK) u) (MY * ‖u‖) := by
  obtain ⟨Mh1, hMh1, h1⟩ := s64_h_W H hmK L
  obtain ⟨Mh2, hMh2, h2⟩ := s64_h_W H hmK (L + 1)
  obtain ⟨Mρ, hMρ⟩ := s64_rho_W H (K + 1) L
  obtain ⟨BA, hBA⟩ := s64_A_P H (K + 1)
  obtain ⟨CF, hCF0, hCF⟩ := s64_Fu_bdd H hmK
  have hMρ0 := s64_W_nonneg hMρ
  have hBA0 := s64_P_nonneg hBA
  set c : ℝ := 2 ^ (K + 1) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨|β⁻¹| * Mh1 + c * (Mh2 * BA) + c * (Mρ * CF) + c * (Mh1 * CF * R), by positivity, fun u hu => ?_⟩
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  set h := mnc_hu ρ (mne_hn (s64_hm3 hmK)) u with hh
  set Fu := mneFo d s ρ (s64_hm3 hmK) u with hFu
  have hFuP : s64_P (K + 1) 0 Fu (CF * ‖u‖) := ⟨(hCF u).1, fun k hk x => by simpa using (hCF u).2 k hk x⟩
  -- T1
  have hT1 : s64_W (K + 1) L (fun x => β⁻¹ • gradient h x) (|β⁻¹| * (Mh1 * ‖u‖)) :=
    s64_W_const_smul β⁻¹ (s64_W_gradient (n := K + 1) (h1 u))
  -- T2
  have hT2 : s64_W (K + 1) L (fun x => h x • (q • x + movForce d s ρ x)) (c * ((Mh2 * ‖u‖) * BA)) :=
    s64_W_smul (L := L) (p := 1) (s64_W_mono_n (by omega) (h2 u)) hBA
  -- T3
  have hT3 : s64_W (K + 1) L (fun x => ρ x • Fu x) (c * (Mρ * (CF * ‖u‖))) :=
    s64_W_smul (L := L) (p := 0) hMρ hFuP
  -- T4
  have hT4 : s64_W (K + 1) L (fun x => h x • Fu x) (c * ((Mh1 * ‖u‖) * (CF * ‖u‖))) :=
    s64_W_smul (L := L) (p := 0) (s64_W_mono_n (by omega) (h1 u)) hFuP
  have hsum := s64_W_add (s64_W_add hT1 hT2) (s64_W_add hT3 hT4)
  have hfun : mneY d s q β ρ (s64_hm3 hmK) u = fun x =>
      (β⁻¹ • gradient h x + h x • (q • x + movForce d s ρ x)) + (ρ x • Fu x + h x • Fu x) := by
    funext x
    rw [s64_Y_decomp H (s64_hm3 hmK) u x, add_smul, add_assoc]
  rw [hfun]
  refine s64_W_mono_M ?_ hsum
  have hq : ‖u‖ * ‖u‖ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right hu hu0
  have h5 : c * ((Mh1 * ‖u‖) * (CF * ‖u‖)) ≤ c * (Mh1 * CF * R) * ‖u‖ := by
    have : (Mh1 * ‖u‖) * (CF * ‖u‖) = Mh1 * CF * (‖u‖ * ‖u‖) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hq (mul_nonneg hMh1 hCF0)
    nlinarith
  nlinarith

lemma s64_out (H : Mov2dTh d s β q ρ) (hmK : (K : ℝ) + d / 2 + 4 < m) (L : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : OscSpace d (m : ℝ), ‖u‖ ≤ R →
      ContDiff ℝ (K : WithTop ℕ∞) (mneRho ρ (s64_hm3 hmK) u) ∧
      ContDiff ℝ (K : WithTop ℕ∞) (fun x => movDiv (mneY d s q β ρ (s64_hm3 hmK) u) x) ∧
      ∀ k ≤ K, ∀ x : Euc d,
        movBracket x ^ L * (‖iteratedFDeriv ℝ k (fun y => mneRho ρ (s64_hm3 hmK) u y - ρ y) x‖ +
          ‖iteratedFDeriv ℝ k (fun x => movDiv (mneY d s q β ρ (s64_hm3 hmK) u) x) x‖) ≤ M * ‖u‖ := by
  obtain ⟨Mh, hMh, hh⟩ := s64_h_W H hmK L
  obtain ⟨MY, hMY, hY⟩ := s64_Y_W H hmK L hR
  refine ⟨Mh + ‖HRS.MS.MovForce.movb2_divL d‖ * MY, by positivity, fun u hu => ?_⟩
  have hW1 := hh u
  have hW2 := s64_W_div (n := K) (hY u hu)
  have hrho : (fun y => mneRho ρ (s64_hm3 hmK) u y - ρ y) = mnc_hu ρ (mne_hn (s64_hm3 hmK)) u := by
    funext y
    simp [mneRho]
  refine ⟨?_, hW2.1, fun k hk x => ?_⟩
  · have h1 : ContDiff ℝ (K : WithTop ℕ∞) (mnc_hu ρ (mne_hn (s64_hm3 hmK)) u) :=
      hW1.1.of_le (by exact_mod_cast (by omega : K ≤ K + 2))
    have h2 : ContDiff ℝ (K : WithTop ℕ∞) ρ := (contDiff_infty.1 (mnc_rho_smooth H)) K
    exact h2.add h1
  · rw [hrho]
    have a1 := hW1.2 k (by omega) x
    have a2 := hW2.2 k hk x
    have hb := s64_bracket_pos x
    calc movBracket x ^ L * (‖iteratedFDeriv ℝ k (mnc_hu ρ (mne_hn (s64_hm3 hmK)) u) x‖ +
          ‖iteratedFDeriv ℝ k (fun x => movDiv (mneY d s q β ρ (s64_hm3 hmK) u) x) x‖)
        = movBracket x ^ L * ‖iteratedFDeriv ℝ k (mnc_hu ρ (mne_hn (s64_hm3 hmK)) u) x‖ +
          movBracket x ^ L * ‖iteratedFDeriv ℝ k (fun x => movDiv (mneY d s q β ρ (s64_hm3 hmK) u) x) x‖ := by ring
      _ ≤ Mh * ‖u‖ + ‖HRS.MS.MovForce.movb2_divL d‖ * (MY * ‖u‖) := add_le_add a1 a2
      _ = (Mh + ‖HRS.MS.MovForce.movb2_divL d‖ * MY) * ‖u‖ := by ring

end HRS.MS.MovSch

end
