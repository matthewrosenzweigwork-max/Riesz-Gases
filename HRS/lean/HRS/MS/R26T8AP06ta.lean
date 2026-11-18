import HRS.MS.R26T8AP06z
import HRS.MS.R26T8AP11jc
import HRS.MS.R26T8AP11wt
import HRS.MS.R26T8AP01p

/-!
# S8.2 Taylor split (T), step C2: the smooth polynomial part `Pxy` in the original variables and its nested jets
`Pm Y w = chi(w) Pfull Y w`, `Pxy x y = Pm ((x+y)/2) (x-y)`; `midPair Pxy = Pm`; `Pxy` is `C^(k+1)`, and
`‖nest p q Pm X z‖ <= C A jb(X)^(2M)` for `|z| <= 2`, `= 0` for `|z| > 2`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

def r26t8a_Pxy (chi : Euc d → ℝ) (m : ℕ) (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ)
    (x y : Euc d) : ℝ :=
  chi (x - y) * r26t8a_Pfull m c ((1 / 2 : ℝ) • (x + y)) (x - y)

theorem r26t8a_midPair_Pxy (chi : Euc d → ℝ) (m : ℕ)
    (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ) (Y w : Euc d) :
    midPair (r26t8a_Pxy chi m c) Y w = chi w * r26t8a_Pfull m c Y w := by
  unfold midPair r26t8a_Pxy
  have e1 : Y + (1 / 2 : ℝ) • w - (Y - (1 / 2 : ℝ) • w) = w := by module
  have e2 : (1 / 2 : ℝ) • (Y + (1 / 2 : ℝ) • w + (Y - (1 / 2 : ℝ) • w)) = Y := by module
  rw [e1, e2]

theorem r26t8a_Pxy_contDiff (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (m k : ℕ)
    (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ)
    (hc : ∀ ℓ ≤ m, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (c ℓ)) :
    ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry (r26t8a_Pxy chi m c)) := by
  have hPf := r26t8a_Pfull_contDiff m c hc
  have hchic : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
  have hlin : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun p : Euc d × Euc d => ((1 / 2 : ℝ) • (p.1 + p.2), p.1 - p.2)) :=
    ((contDiff_fst.add contDiff_snd).const_smul _).prodMk (contDiff_fst.sub contDiff_snd)
  have h1 : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun p : Euc d × Euc d => chi (p.1 - p.2)) :=
    hchic.comp (contDiff_fst.sub contDiff_snd)
  exact h1.mul (hPf.comp hlin)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem r26t8a_nest_Pm_bound (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (m k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ),
      (∀ ℓ ≤ m, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (c ℓ)) →
      ∀ (p q : ℕ), p + q ≤ k → ∀ (X z : Euc d), ‖z‖ ≤ 2 → ∀ BX : ℝ,
      (∀ ℓ ≤ m, ‖iteratedFDeriv ℝ p (c ℓ) X‖ ≤ BX) →
      ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2) X z‖ ≤ D * BX := by
  obtain ⟨Dχ, hDχ0, hDχ⟩ := r26t8a_chi_jet_bound hchi k
  refine ⟨2 ^ k * Dχ * ((m + 1) * 2 ^ m), by positivity, ?_⟩
  intro c hc p q hpq X z hz BX hBX
  have hB0 : 0 ≤ BX := (norm_nonneg _).trans (hBX 0 (Nat.zero_le _))
  have hPf : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) :=
    r26t8a_Pfull_contDiff m c hc
  have hchic : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
  refine (r26t8a_nest_product_bound p q chi _ X z hchic (hPf.of_le (by exact_mod_cast (by omega : p + q ≤ k + 1)))).trans ?_
  have hterm : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
      ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) X z‖ ≤
      (q.choose i : ℝ) * (Dχ * ((m + 1) * 2 ^ m * BX)) := by
    intro i hi
    have hiq : i ≤ q := by rw [Finset.mem_range] at hi; omega
    have h1 := hDχ i (by omega) z
    have h2 := r26t8a_nest_Pfull_bound m k c hc p (q - i) (by omega) X z hz BX hBX
    have hch : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
    calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
          ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Pfull m c Yw.1 Yw.2) X z‖
        ≤ (q.choose i : ℝ) * Dχ * ((m + 1) * 2 ^ m * BX) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (norm_nonneg _) (by positivity)
      _ = (q.choose i : ℝ) * (Dχ * ((m + 1) * 2 ^ m * BX)) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)) = 2 ^ q := by exact_mod_cast Nat.sum_range_choose q
  rw [hsum]
  have h2k : (2 : ℝ) ^ q ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  have hR0 : 0 ≤ Dχ * ((m + 1) * 2 ^ m * BX) := by positivity
  calc (2 : ℝ) ^ q * (Dχ * ((m + 1) * 2 ^ m * BX)) ≤ 2 ^ k * (Dχ * ((m + 1) * 2 ^ m * BX)) :=
        mul_le_mul_of_nonneg_right h2k hR0
    _ = 2 ^ k * Dχ * ((m + 1) * 2 ^ m) * BX := by ring

theorem r26t8a_nest_Pm_far (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (p q : ℕ) (m : ℕ)
    (c : (ℓ : ℕ) → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => Euc d) ℝ) (X z : Euc d) (hz : 2 < ‖z‖) :
    r26t8a_nest p q (fun Yw : Euc d × Euc d => chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2) X z = 0 := by
  refine r26t8a_nest_eq_zero p q _ X z ?_
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw Y
  simp only [hchi.2.2.2.2 w hw.le, zero_mul]

end HRS.MS.R26T8A
