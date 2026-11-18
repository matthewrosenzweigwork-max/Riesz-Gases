import HRS.MS.R2WinOrbAux1
import HRS.MS.UlOrbitAux1
import HRS.MS.MovOscAux5

/-!
# S10.3 (stationary half), part 2: `oscNorm` of the dual tests and explicit-order weighted sup bounds

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.

* `s103_oscNorm_test`: `‖φ_α‖_{Σ^r} = λ_α^{(r-m)/2}`.
* `s103_weighted`: for Schwartz `f`, `(1+‖x‖)^N ‖D^j f(x)‖ ≤ C ‖f‖_{Σ^{N+⌊j+d/2⌋+1}}` (explicit order; the order of the
  analogous `ul6_weighted` is existential).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s103_oscNorm_test (m r : ℝ) (α : MultiIndex d) :
    oscNorm r (oscTestFun m α) = oscEigenvalue d α ^ ((r - m) / 2) := by
  set lam := oscEigenvalue d α with hlam
  have hlam0 : 0 < lam := oscEigenvalue_pos α
  set c : ℝ := lam ^ (-(m / 2)) with hc
  have hfun : oscTestFun m α = HRS.MS.MovOsc.mo_hsum {α} (fun _ => c) := by
    funext x; simp [oscTestFun, HRS.MS.MovOsc.mo_hsum, hc, hlam]
  have hsq := HRS.MS.MovOsc.mo_hsum_oscNorm_sq r ({α} : Finset (MultiIndex d)) (fun _ => c)
  rw [← hfun] at hsq
  simp only [Finset.sum_singleton] at hsq
  have hnn : 0 ≤ oscNorm r (oscTestFun m α) := Real.sqrt_nonneg _
  have h2 : (lam ^ ((r - m) / 2)) ^ 2 = lam ^ r * c ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam0.le, hc, ← Real.rpow_natCast (lam ^ (-(m / 2))),
      ← Real.rpow_mul hlam0.le, ← Real.rpow_add hlam0]
    congr 1; push_cast; ring
  have h3 : oscNorm r (oscTestFun m α) = Real.sqrt (lam ^ r * c ^ 2) := by
    rw [← hsq, Real.sqrt_sq hnn]
  rw [h3, ← h2, Real.sqrt_sq (Real.rpow_nonneg hlam0.le _)]

lemma s103_osc_mono {a b : ℕ} (h : a ≤ b) (f : SchwartzMap (Euc d) ℝ) :
    oscNorm (a : ℝ) f ≤ oscNorm (b : ℝ) f := ul6_osc_mono h f

/-- Weighted sup bounds with explicit oscillator order. -/
theorem s103_weighted (N : ℕ) : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j f x‖ ≤
      C * oscNorm ((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f := by
  induction N with
  | zero =>
    intro j
    have hlt : (j : ℝ) + (d : ℝ) / 2 < ((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    obtain ⟨C, hC0, hC⟩ := HRS.MS.MovOsc.mo_sobolev_emb (d := d) j _ hlt
    refine ⟨C, hC0, fun f x => ?_⟩
    have := hC f x
    push_cast at this ⊢
    simpa using this
  | succ N ih =>
    intro j
    obtain ⟨C0, hC0, h0⟩ := ih j
    obtain ⟨C1, hC1, h1⟩ := ih (j - 1)
    set n0 : ℕ := N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hn0
    set n1 : ℕ := N + ⌊((j - 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hn1
    set nn : ℕ := N + 1 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hnn
    have hn1le : n1 ≤ n0 := by
      rw [hn1, hn0]
      have : ⌊((j - 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ ≤ ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ :=
        Nat.floor_le_floor (by gcongr; exact_mod_cast Nat.sub_le j 1)
      omega
    obtain ⟨Cx, hCx0, hCx⟩ := HRS.MS.MovOsc.mo_xmul (d := d) (n0 : ℝ)
    refine ⟨C0 + d * (C0 * Cx + j * C1), by positivity, fun f x => ?_⟩
    have hw := ul6_w_pos' x
    have hw0 : 0 ≤ (1 + ‖x‖) ^ N := by positivity
    have hf : ContDiff ℝ ∞ (f : Euc d → ℝ) := f.smooth _
    have hxi : ∀ i : Fin d, (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖) ≤
        C0 * Cx * oscNorm (nn : ℝ) f + j * (C1 * oscNorm (nn : ℝ) f) := by
      intro i
      have hp := ul6_pt_xmul f hf i j x
      have e1 : (fun y => y i * f y) = ⇑(HRS.MS.MovOsc.mova1_X i f) := funext fun y => by simp
      rw [e1] at hp
      have a1 := h0 (HRS.MS.MovOsc.mova1_X i f) x
      have a2 := h1 f x
      have a3 : oscNorm (n0 : ℝ) ⇑(HRS.MS.MovOsc.mova1_X i f) ≤ Cx * oscNorm ((n0 : ℝ) + 1) f := by
        have := (hCx i f).2
        rwa [e1] at this
      have b1 : oscNorm ((n0 : ℝ) + 1) f ≤ oscNorm (nn : ℝ) f := by
        have := s103_osc_mono (a := n0 + 1) (b := nn) (by omega) f
        simpa using this
      have b2 : oscNorm (n1 : ℝ) f ≤ oscNorm (nn : ℝ) f := s103_osc_mono (by omega) f
      calc (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖)
          ≤ (1 + ‖x‖) ^ N * (‖iteratedFDeriv ℝ j (⇑(HRS.MS.MovOsc.mova1_X i f)) x‖ +
              j * ‖iteratedFDeriv ℝ (j - 1) f x‖) := mul_le_mul_of_nonneg_left hp hw0
        _ = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (⇑(HRS.MS.MovOsc.mova1_X i f)) x‖ +
              j * ((1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ (j - 1) f x‖) := by ring
        _ ≤ C0 * oscNorm (n0 : ℝ) ⇑(HRS.MS.MovOsc.mova1_X i f) + j * (C1 * oscNorm (n1 : ℝ) f) := by
            gcongr
        _ ≤ C0 * (Cx * oscNorm ((n0 : ℝ) + 1) f) + j * (C1 * oscNorm (n1 : ℝ) f) := by gcongr
        _ ≤ C0 * (Cx * oscNorm (nn : ℝ) f) + j * (C1 * oscNorm (nn : ℝ) f) := by gcongr
        _ = _ := by ring
    have hsum : (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖) ≤
        ∑ i : Fin d, (C0 * Cx * oscNorm (nn : ℝ) f + j * (C1 * oscNorm (nn : ℝ) f)) := by
      calc (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖)
          ≤ (1 + ‖x‖) ^ N * ((∑ i, |x i|) * ‖iteratedFDeriv ℝ j f x‖) := by
            gcongr; exact ul6_norm_le_sum x
        _ = ∑ i, (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖) := by
            rw [Finset.sum_mul, Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun i _ => hxi i
    have hb0 : oscNorm (n0 : ℝ) f ≤ oscNorm (nn : ℝ) f := s103_osc_mono (by omega) f
    have a0 := h0 f x
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    calc (1 + ‖x‖) ^ (N + 1) * ‖iteratedFDeriv ℝ j f x‖
        = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j f x‖ + (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖) := by
          ring
      _ ≤ C0 * oscNorm (n0 : ℝ) f + d * (C0 * Cx * oscNorm (nn : ℝ) f +
          j * (C1 * oscNorm (nn : ℝ) f)) := add_le_add a0 hsum
      _ ≤ C0 * oscNorm (nn : ℝ) f + d * (C0 * Cx * oscNorm (nn : ℝ) f +
          j * (C1 * oscNorm (nn : ℝ) f)) := by gcongr
      _ = _ := by ring

end HRS.MS.R2WinOrb

end
