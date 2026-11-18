import HRS.MC.D3T3Aux7

/-!
# Packet D3T3, auxiliary facts: partial sums of `|k|² ĝ_λ(k)` (Tonelli).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

lemma d3f_ghat_partial (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb0 : 0 < b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ lam : ℝ, 0 < lam → ∀ F : Finset (Lattice d),
      ∑ k ∈ F, Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k ≤ M * lam ^ (-s - 2) := by
  obtain ⟨A, hA0, hA⟩ := d3f_lattice_sum hd hψ
  refine ⟨b * A / (s + 2), by positivity, fun lam hlam F => ?_⟩
  have h0 : Lattice.enorm (0 : Lattice d) ^ 2 * fdlGhat ψ s b lam 0 = 0 := by
    have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    simp [Lattice.enorm, this]
  rw [← Finset.sum_erase F h0]
  set F' := F.erase 0 with hF'
  have hk0 : ∀ k ∈ F', k ≠ 0 := fun k hk => Finset.ne_of_mem_erase hk
  set f : Lattice d → ℝ → ℝ := fun k t =>
    t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t with hf
  have hint : ∀ k ∈ F', IntegrableOn (fun t => Lattice.enorm k ^ 2 * f k t) (Ioi lam) :=
    fun k hk => (d3f_int_psi hψ hs0 hlam (hk0 k hk)).const_mul _
  have hterm : ∀ k ∈ F', Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k
      = b * ∫ t in Ioi lam, Lattice.enorm k ^ 2 * f k t := by
    intro k hk
    unfold fdlGhat
    rw [integral_const_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← integral_finset_sum _ hint]
  set g : ℝ → ℝ := fun t => A * t ^ (-s - 3) with hg
  have hgint : IntegrableOn g (Ioi lam) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hlam).const_mul A
  have hmono : ∫ t in Ioi lam, ∑ k ∈ F', Lattice.enorm k ^ 2 * f k t ≤ ∫ t in Ioi lam, g t := by
    refine setIntegral_mono_on (integrable_finset_sum _ hint) hgint measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hlam ht
    obtain ⟨hsm, hle⟩ := hA t ht0
    have h1 : ∑ k ∈ F', Lattice.enorm k ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2
        ≤ A * t ^ (-((d : ℝ) + 2)) :=
      (hsm.sum_le_tsum F' (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans hle
    have h2 : ∑ k ∈ F', Lattice.enorm k ^ 2 * f k t
        = (t ^ ((d : ℝ) - s) / t) *
          ∑ k ∈ F', Lattice.enorm k ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hf]; ring
    rw [h2]
    calc (t ^ ((d : ℝ) - s) / t) *
          ∑ k ∈ F', Lattice.enorm k ^ 2 * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2
        ≤ (t ^ ((d : ℝ) - s) / t) * (A * t ^ (-((d : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (Real.rpow_nonneg ht0.le _) ht0.le)
      _ = A * (t ^ ((d : ℝ) - s) / t * t ^ (-((d : ℝ) + 2))) := by ring
      _ = g t := by
          rw [d3f_rpow_comb ht0]
          simp only [hg]
          congr 2
          ring
  have hval : ∫ t in Ioi lam, g t = A * (lam ^ (-s - 2) / (s + 2)) := by
    simp only [hg]
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hlam]
    have e1 : -s - 3 + 1 = -s - 2 := by ring
    rw [e1]
    generalize lam ^ (-s - 2) = X
    have : (-s - 2 : ℝ) = -(s + 2) := by ring
    rw [this, neg_div_neg_eq]
  calc b * ∫ t in Ioi lam, ∑ k ∈ F', Lattice.enorm k ^ 2 * f k t
      ≤ b * ∫ t in Ioi lam, g t := mul_le_mul_of_nonneg_left hmono hb0.le
    _ = b * A / (s + 2) * lam ^ (-s - 2) := by rw [hval]; ring

end HRS.MC.D3T3
