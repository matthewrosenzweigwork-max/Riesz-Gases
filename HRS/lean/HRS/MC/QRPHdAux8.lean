import HRS.MC.QRPHdAux7

/-!
# Packet HD, part 8: the total mass `∑_α D(α,λ)² ≲ |λ|^{1+2s}`
-/

noncomputable section

open Finset
open scoped BigOperators

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ} {s : ℝ}

theorem hd_enorm_add_le (a b : Lattice d) : Lattice.enorm (a + b) ≤ Lattice.enorm a + Lattice.enorm b := by
  rw [hd_enorm_def, hd_enorm_def, hd_enorm_def, hd_toEuc_add]
  exact norm_add_le _ _

theorem hd_sq_aux {a b D : ℝ} (h0 : 0 ≤ D) (h : D ≤ a + b) : D ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

set_option maxHeartbeats 1600000 in
open Classical in
theorem hd_totalB (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : 2 * s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : Lattice d, lam ≠ 0 →
      Summable (fun α => hdD d s lam α ^ 2) ∧
      ∑' α, hdD d s lam α ^ 2 ≤ C * Lattice.enorm lam ^ (1 + 2 * s) := by
  have hp : 0 < (d : ℝ) - 2 * s := by linarith
  have hσ : 0 < 1 + 2 * s := by linarith
  have hsd' : s < d := by linarith
  obtain ⟨At, hAt0, hAt⟩ := hd_tail_tsum (d := d) (by omega) hp
  obtain ⟨Al, hAl0, hAl⟩ := hd_low_tsum (d := d) (by omega) hσ
  set C1 := |hdκ d s| * (1 + 3 * |s - (d : ℝ)|) * 2 ^ ((d : ℝ) - s) with hC1
  set κ0 := hdκ d s with hκ0
  refine ⟨C1 ^ 2 * At + 4 * κ0 ^ 2 * Al * 4 ^ (1 + 2 * s), by positivity, fun lam hlam => ?_⟩
  set el := Lattice.enorm lam with hel
  have hel1 : 1 ≤ el := hd_enorm_ge_one hlam
  have hel0 : 0 < el := by linarith
  obtain ⟨hsT, htT⟩ := hAt (2 * el) (by linarith)
  obtain ⟨hsg, htg⟩ := hAl (3 * el) (by linarith)
  set Tf : Lattice d → ℝ := fun k => if 2 * el ≤ Lattice.enorm k then
    Lattice.enorm k ^ (-(d : ℝ) - ((d : ℝ) - 2 * s)) else 0 with hTf
  set g : Lattice d → ℝ := fun k => if Lattice.enorm k < 3 * el then
    (if k = 0 then (0 : ℝ) else Lattice.enorm k ^ (1 + 2 * s - (d : ℝ))) else 0 with hg
  have hgnn : ∀ k, 0 ≤ g k := by
    intro k; simp only [hg]
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (hd_enorm_nonneg k) _
    · exact le_rfl
  have hTnn : ∀ k, 0 ≤ Tf k := by
    intro k; simp only [hTf]
    split_ifs
    · exact Real.rpow_nonneg (hd_enorm_nonneg k) _
    · exact le_rfl
  have hsg' : Summable (fun α => g (α + lam)) := (Equiv.addRight lam).summable_iff.mpr hsg
  have htg' : ∑' α, g (α + lam) = ∑' α, g α := (Equiv.addRight lam).tsum_eq g
  set M : Lattice d → ℝ := fun α => (C1 ^ 2 * el ^ 2) * Tf α + 2 * κ0 ^ 2 * (g α + g (α + lam)) with hM
  have hMs : Summable M := (hsT.mul_left _).add ((hsg.add hsg').mul_left _)
  have hq : ∀ c : Lattice d, Lattice.enorm c < 3 * el → ‖hdq d s c‖ ^ 2 ≤ κ0 ^ 2 * g c := by
    intro c hc
    by_cases h0 : c = 0
    · subst h0; simp [hdq_zero, hg, hd_enorm_def, hd_toEuc_zero]
    · have := hdq_sq_le (s := s) c h0 (by omega)
      simp only [hg, if_pos hc, if_neg h0]
      exact this
  have hpt : ∀ α, hdD d s lam α ^ 2 ≤ M α := by
    intro α
    by_cases hfar : 2 * el ≤ Lattice.enorm α
    · have hα : α ≠ 0 := by
        rintro rfl
        have : Lattice.enorm (0 : Lattice d) = 0 := by
          rw [hd_enorm_def, hd_toEuc_zero, norm_zero]
        linarith
      have := hdD_sq_far hsd' hα hfar
      have h2 : 0 ≤ 2 * κ0 ^ 2 * (g α + g (α + lam)) := by
        have := hgnn α; have := hgnn (α + lam); positivity
      simp only [hM, hTf, if_pos hfar]
      calc hdD d s lam α ^ 2 ≤ _ := this
        _ ≤ _ := by linarith
    · push Not at hfar
      have hn1 : Lattice.enorm α < 3 * el := by linarith
      have hn2 : Lattice.enorm (α + lam) < 3 * el := by
        have := hd_enorm_add_le α lam; linarith
      have h1 := hq α hn1
      have h2 := hq (α + lam) hn2
      have hD : hdD d s lam α ≤ ‖hdq d s α‖ + ‖hdq d s (α + lam)‖ := norm_sub_le _ _
      have hD2 := hd_sq_aux (hdD_nonneg s lam α) hD
      have h3 : 0 ≤ (C1 ^ 2 * el ^ 2) * Tf α := mul_nonneg (by positivity) (hTnn α)
      simp only [hM] at h3 ⊢
      linarith
  have hS : Summable (fun α => hdD d s lam α ^ 2) :=
    Summable.of_nonneg_of_le (fun α => sq_nonneg _) hpt hMs
  refine ⟨hS, ?_⟩
  have hts : ∑' α, M α = (C1 ^ 2 * el ^ 2) * ∑' α, Tf α + 2 * κ0 ^ 2 * (∑' α, g α + ∑' α, g (α + lam)) := by
    simp only [hM]
    rw [Summable.tsum_add (hsT.mul_left _) ((hsg.add hsg').mul_left _), tsum_mul_left, tsum_mul_left,
      Summable.tsum_add hsg hsg']
  rw [htg'] at hts
  have e1 : (2 * el) ^ (-((d : ℝ) - 2 * s)) ≤ el ^ (-((d : ℝ) - 2 * s)) := by
    rw [Real.mul_rpow (by norm_num) hel0.le]
    have : (2 : ℝ) ^ (-((d : ℝ) - 2 * s)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have h0 : 0 ≤ el ^ (-((d : ℝ) - 2 * s)) := Real.rpow_nonneg hel0.le _
    calc _ ≤ 1 * el ^ (-((d : ℝ) - 2 * s)) := mul_le_mul_of_nonneg_right this h0
      _ = _ := one_mul _
  have e2 : el ^ 2 * el ^ (-((d : ℝ) - 2 * s)) ≤ el ^ (1 + 2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hel0]
    exact Real.rpow_le_rpow_of_exponent_le hel1 (by push_cast; have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
                                                    linarith)
  have e3 : (3 * el + 1) ^ (1 + 2 * s) ≤ 4 ^ (1 + 2 * s) * el ^ (1 + 2 * s) := by
    rw [← Real.mul_rpow (by norm_num) hel0.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hσ.le
  have hC1n : 0 ≤ C1 ^ 2 := sq_nonneg _
  have b1 : (C1 ^ 2 * el ^ 2) * ∑' α, Tf α ≤ C1 ^ 2 * At * el ^ (1 + 2 * s) := by
    calc (C1 ^ 2 * el ^ 2) * ∑' α, Tf α ≤ (C1 ^ 2 * el ^ 2) * (At * (2 * el) ^ (-((d : ℝ) - 2 * s))) :=
          mul_le_mul_of_nonneg_left htT (by positivity)
      _ ≤ (C1 ^ 2 * el ^ 2) * (At * el ^ (-((d : ℝ) - 2 * s))) := by
          gcongr
      _ = C1 ^ 2 * At * (el ^ 2 * el ^ (-((d : ℝ) - 2 * s))) := by ring
      _ ≤ C1 ^ 2 * At * el ^ (1 + 2 * s) := mul_le_mul_of_nonneg_left e2 (by positivity)
  have b2 : 2 * κ0 ^ 2 * (∑' α, g α + ∑' α, g α) ≤ 4 * κ0 ^ 2 * Al * 4 ^ (1 + 2 * s) * el ^ (1 + 2 * s) := by
    have : ∑' α, g α ≤ Al * (4 ^ (1 + 2 * s) * el ^ (1 + 2 * s)) := htg.trans (by
      exact mul_le_mul_of_nonneg_left e3 hAl0)
    have hk : 0 ≤ κ0 ^ 2 := sq_nonneg _
    nlinarith
  calc ∑' α, hdD d s lam α ^ 2 ≤ ∑' α, M α := Summable.tsum_le_tsum hpt hS hMs
    _ = _ := hts
    _ ≤ _ := by nlinarith

end HRS.MC.QRSpec.Hd

end
