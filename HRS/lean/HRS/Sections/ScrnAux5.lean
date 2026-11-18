import HRS.Sections.ScrnAux4

/-!
# Packet SCRN, part 5: Schwartz decay of `φ̂` and the `ℓ`-scaling of weighted Fourier sums of `ψ = φ_ℓ`

* `scrn_fourier_decay`: `(1+|ξ|)^N |D^n φ̂(ξ)| ≤ A` for `φ ∈ C_c^∞` (`HasCompactSupport.toSchwartzMap`).
* `scrn_wsum`: `∑_k |k|^r |φ̂(ℓk)|^e ≤ C ℓ^{-d-r}` (`0 < ℓ ≤ 1`), through `scrn_latsum`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform SchwartzMap

namespace HRS

variable {d : ℕ}

/-- The complexified test function. -/
def scrnPhiC (φ : Euc d → ℝ) : Euc d → ℂ := fun x => ((φ x : ℝ) : ℂ)

lemma contDiff_scrnPhiC {φ : Euc d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (scrnPhiC φ) :=
  Complex.ofRealCLM.contDiff.comp hφ

lemma hasCompactSupport_scrnPhiC {φ : Euc d → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (scrnPhiC φ) := hc.comp_left Complex.ofReal_zero

theorem scrn_fourier_decay {φ : Euc d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (N n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : Euc d,
      (1 + ‖ξ‖) ^ N * ‖iteratedFDeriv ℝ n (𝓕 (scrnPhiC φ)) ξ‖ ≤ A := by
  set f : 𝓢(Euc d, ℂ) := (hasCompactSupport_scrnPhiC hc).toSchwartzMap (contDiff_scrnPhiC hφ) with hf
  set g : 𝓢(Euc d, ℂ) := 𝓕 f with hg
  have hcoe : ⇑g = 𝓕 (scrnPhiC φ) := by
    rw [hg, SchwartzMap.fourier_coe]
    rfl
  refine ⟨2 ^ (N, n).1 * ((Finset.Iic (N, n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) g, ?_, ?_⟩
  · positivity
  · intro ξ
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, n)) (k := N) (n := n)
      le_rfl le_rfl g ξ
    rwa [hcoe] at this

theorem scrn_fourier_bound {φ : Euc d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (N : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : Euc d,
      ‖𝓕 (scrnPhiC φ) ξ‖ ≤ A * (1 + ‖ξ‖) ^ (-(N : ℝ)) ∧
      ‖fderiv ℝ (𝓕 (scrnPhiC φ)) ξ‖ ≤ A * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  obtain ⟨A0, hA0, h0⟩ := scrn_fourier_decay hφ hc N 0
  obtain ⟨A1, hA1, h1⟩ := scrn_fourier_decay hφ hc N 1
  refine ⟨max A0 A1, le_max_of_le_left hA0, fun ξ => ⟨?_, ?_⟩⟩
  · have := h0 ξ
    rw [norm_iteratedFDeriv_zero] at this
    have hp : 0 < (1 + ‖ξ‖) ^ N := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
    nlinarith [le_max_left A0 A1]
  · have := h1 ξ
    rw [norm_iteratedFDeriv_one] at this
    have hp : 0 < (1 + ‖ξ‖) ^ N := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
    nlinarith [le_max_right A0 A1]


/-- Weighted lattice sums of a Schwartz-type function sampled on `ℓℤ^d`. -/
theorem scrn_wsum (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r) {e N : ℕ} (he : 1 ≤ e)
    (hN : (d : ℝ) + r < e * N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Euc d → ℂ) (A : ℝ), 0 ≤ A →
      (∀ ξ, ‖F ξ‖ ≤ A * (1 + ‖ξ‖) ^ (-(N : ℝ))) → ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
      Summable (fun k : Lattice d => Lattice.enorm k ^ r * ‖F (ℓ • Lattice.toEuc k)‖ ^ e) ∧
      ∑' k : Lattice d, Lattice.enorm k ^ r * ‖F (ℓ • Lattice.toEuc k)‖ ^ e ≤
        C * A ^ e * ℓ ^ (-((d : ℝ) + r)) := by
  have hL : (d : ℝ) < (e * N : ℝ) - r := by linarith
  obtain ⟨C, hC, hlat⟩ := scrn_latsum hd (g := 0) (L := (e * N : ℝ) - r) le_rfl
    (by exact_mod_cast hd) hL
  refine ⟨C, hC, fun F A hA hF ℓ hℓ hℓ1 => ?_⟩
  obtain ⟨hs, hsum⟩ := hlat ℓ hℓ hℓ1
  have hbound : ∀ k : Lattice d, Lattice.enorm k ^ r * ‖F (ℓ • Lattice.toEuc k)‖ ^ e ≤
      A ^ e * ℓ ^ (-r) * scrnW d 0 ((e * N : ℝ) - r) ℓ k := by
    intro k
    have hE : 0 ≤ Lattice.enorm k := norm_nonneg _
    have h1 : ‖F (ℓ • Lattice.toEuc k)‖ ≤ A * (1 + ℓ * Lattice.enorm k) ^ (-(N : ℝ)) := by
      have := hF (ℓ • Lattice.toEuc k)
      rwa [norm_smul_toEuc hℓ k] at this
    have h2 : ‖F (ℓ • Lattice.toEuc k)‖ ^ e ≤ A ^ e * (1 + ℓ * Lattice.enorm k) ^ (-(e * N : ℝ)) := by
      calc ‖F (ℓ • Lattice.toEuc k)‖ ^ e ≤ (A * (1 + ℓ * Lattice.enorm k) ^ (-(N : ℝ))) ^ e :=
            pow_le_pow_left₀ (norm_nonneg _) h1 e
        _ = A ^ e * (1 + ℓ * Lattice.enorm k) ^ (-(e * N : ℝ)) := by
            rw [mul_pow, ← Real.rpow_natCast ((1 + ℓ * Lattice.enorm k) ^ (-(N : ℝ))) e,
              ← Real.rpow_mul (by positivity)]
            congr 2; ring
    have h3 : Lattice.enorm k ^ r ≤ ℓ ^ (-r) * (1 + ℓ * Lattice.enorm k) ^ r := by
      have : (ℓ * Lattice.enorm k) ^ r ≤ (1 + ℓ * Lattice.enorm k) ^ r :=
        Real.rpow_le_rpow (by positivity) (by linarith) hr
      rw [Real.mul_rpow hℓ.le hE] at this
      have hℓr : ℓ ^ (-r) * ℓ ^ r = 1 := by
        rw [← Real.rpow_add hℓ]; simp
      calc Lattice.enorm k ^ r = (ℓ ^ (-r) * ℓ ^ r) * Lattice.enorm k ^ r := by rw [hℓr, one_mul]
        _ = ℓ ^ (-r) * (ℓ ^ r * Lattice.enorm k ^ r) := by ring
        _ ≤ _ := by gcongr
    have hw : scrnW d 0 ((e * N : ℝ) - r) ℓ k = (1 + ℓ * Lattice.enorm k) ^ (-((e * N : ℝ) - r)) := by
      unfold scrnW; simp
    rw [hw]
    have hpos : 0 < 1 + ℓ * Lattice.enorm k := by positivity
    calc Lattice.enorm k ^ r * ‖F (ℓ • Lattice.toEuc k)‖ ^ e
        ≤ (ℓ ^ (-r) * (1 + ℓ * Lattice.enorm k) ^ r) *
          (A ^ e * (1 + ℓ * Lattice.enorm k) ^ (-(e * N : ℝ))) :=
          mul_le_mul h3 h2 (by positivity) (by positivity)
      _ = A ^ e * ℓ ^ (-r) * ((1 + ℓ * Lattice.enorm k) ^ r * (1 + ℓ * Lattice.enorm k) ^ (-(e * N : ℝ))) := by
          ring
      _ = A ^ e * ℓ ^ (-r) * (1 + ℓ * Lattice.enorm k) ^ (-((e * N : ℝ) - r)) := by
          rw [← Real.rpow_add hpos]; congr 2; ring
  have hnn : ∀ k : Lattice d, 0 ≤ Lattice.enorm k ^ r * ‖F (ℓ • Lattice.toEuc k)‖ ^ e := fun k =>
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _)
  have hsumm : Summable (fun k : Lattice d => Lattice.enorm k ^ r * ‖F (ℓ • Lattice.toEuc k)‖ ^ e) :=
    Summable.of_nonneg_of_le hnn hbound (hs.mul_left _)
  refine ⟨hsumm, ?_⟩
  calc ∑' k : Lattice d, Lattice.enorm k ^ r * ‖F (ℓ • Lattice.toEuc k)‖ ^ e
      ≤ ∑' k : Lattice d, A ^ e * ℓ ^ (-r) * scrnW d 0 ((e * N : ℝ) - r) ℓ k :=
        hsumm.tsum_le_tsum hbound (hs.mul_left _)
    _ = A ^ e * ℓ ^ (-r) * ∑' k : Lattice d, scrnW d 0 ((e * N : ℝ) - r) ℓ k := tsum_mul_left
    _ ≤ A ^ e * ℓ ^ (-r) * (C * ℓ ^ (-((d : ℝ) - 0))) := by gcongr
    _ = C * A ^ e * ℓ ^ (-((d : ℝ) + r)) := by
        have : ℓ ^ (-r) * ℓ ^ (-((d : ℝ) - 0)) = ℓ ^ (-((d : ℝ) + r)) := by
          rw [← Real.rpow_add hℓ]; congr 1; ring
        calc A ^ e * ℓ ^ (-r) * (C * ℓ ^ (-((d : ℝ) - 0)))
            = C * A ^ e * (ℓ ^ (-r) * ℓ ^ (-((d : ℝ) - 0))) := by ring
          _ = _ := by rw [this]

end HRS
