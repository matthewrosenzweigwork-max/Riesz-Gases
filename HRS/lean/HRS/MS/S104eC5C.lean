import HRS.MS.S104eC5A
import HRS.MS.S104eC5B
import HRS.MS.S104eC4E
import HRS.MS.S104eC3J

/-!
# S104E route C, packet C5 part C: existence of the classical adjoint solution from a `VolHyp` instance

`c5_exists`: given the hypotheses `VolHyp d 2 η (t+1) (ouSg (ouQ d a) β⁻¹) (s103bQ d s (ρ ·))` (supplied by C1/C2, see `S104eC5D`), the Hermite datum `φ_α` has a classical
adjoint solution with terminal time `t` along `(quadraticGradientDyn d s a β).coeff ρ`: Picard solution (`c3_volterra_exists`) + `c4_classical`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.R2WinOrb HRS.MS.Ul

variable {d : ℕ}

theorem c5_norm0_le {f f' : Euc d → ℝ} {x : Euc d} {ε : ℝ}
    (h : ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f' x‖ ≤ ε) : |f x - f' x| ≤ ε := by
  have := ((iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f' x).le_opNorm (fun _ => (0 : Euc d)))
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at this
  rw [Real.norm_eq_abs] at this
  have e : (iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f' x) (fun _ => (0 : Euc d)) = f x - f' x := by
    simp [iteratedFDeriv_zero_apply]
  rw [e] at this
  exact this.trans h

theorem c5_vanB_of_decay {N p : ℕ} {A : ℝ} {f : Euc d → ℝ}
    (h : ∀ i ≤ N, ∀ x, ‖iteratedFDeriv ℝ i f x‖ * (1 + ‖x‖) ^ p ≤ A) (hp : 1 ≤ p) : VanB N f := by
  intro i hi
  have h1 : Tendsto (fun x : Euc d => A * ((1 + ‖x‖) ^ p)⁻¹) (cocompact (Euc d)) (𝓝 0) := by
    have : Tendsto (fun x : Euc d => (1 + ‖x‖) ^ p) (cocompact (Euc d)) atTop :=
      (tendsto_pow_atTop (by omega)).comp (tendsto_atTop_add_const_left _ _ tendsto_norm_cocompact_atTop)
    simpa using (tendsto_inv_atTop_zero.comp this).const_mul A
  refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) h1
  have hpos : 0 < (1 + ‖x‖) ^ p := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  exact h i hi x

/-- the Hermite datum is in the Picard class -/
theorem c5_datum {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (α : MultiIndex d) :
    ∃ (B : ℝ), HolB 2 η B (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) ∧
      VanB 3 (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) ∧ Bd 2 B (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) := by
  obtain ⟨Kφ, hKφ0, hKφ⟩ := s103c_phi_syn3 (d := d) 4 (by omega)
  have hS := hKφ α
  have hS' : SyN 3 4 (Kφ * s103_b d α) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) := hS
  have hb4 : Bd 4 (Kφ * s103_b d α) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) := hS'.bd
  have hA0 : 0 ≤ Kφ * s103_b d α := mul_nonneg hKφ0 (s103_b_nonneg α)
  refine ⟨2 * (Kφ * s103_b d α), holB_of_bd hη0 hη1 hb4, ?_, ?_⟩
  · exact c5_vanB_of_decay (fun i hi x => hS'.2 i (by omega) x) (by norm_num)
  · exact ⟨hb4.1.of_le (by exact_mod_cast (by omega : 2 ≤ 4)), fun i hi x => (hb4.2 i (by omega) x).trans (by linarith)⟩

theorem c5_exists (s a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (ρ : ℝ → Euc d → ℝ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (α : MultiIndex d) {t : ℝ} (ht : 0 ≤ t)
    (hyp : VolHyp d 2 η (t + 1) (ouSg (ouQ d a) β⁻¹) (fun v f => s103bQ d s (ρ v) f)) :
    ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t
      (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) f := by
  obtain ⟨B, hψH, hψV, hψB⟩ := c5_datum (d := d) hη0 hη1.le α
  obtain ⟨C3, hC30, hex⟩ := c3_volterra_exists 2 η (t + 1) hη0 hη1 (by linarith) _ _ hyp
  obtain ⟨w, hwH, hwt, hwc, hwm, hwV, hwTC⟩ := hex t ⟨ht, by linarith⟩ B _ hψH hψV
  set ψ := oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α with hψdef
  set Bw := C3 * B with hBw
  have hw2 : ∀ r ∈ Icc (0 : ℝ) t, Bd 2 Bw (w r) := fun r hr =>
    ⟨(hwH r hr).1.1.of_le (by exact_mod_cast (by omega : 2 ≤ 2 + 1)),
      fun i hi x => (hwH r hr).1.2 i (by omega) x⟩
  have hmem : ∀ v ∈ Icc (0 : ℝ) t, v ∈ Icc (0 : ℝ) (t + 1) := fun v hv => ⟨hv.1, by linarith [hv.2]⟩
  have hg2 : ∀ r ∈ Icc (0 : ℝ) t, Bd 2 (hyp.CA * Bw) (s103bQ d s (ρ r) (w r)) := fun r hr =>
    hyp.A_bd r (hmem r hr) Bw (w r) (hwH r hr)
  have hTCg := hyp.A_tc t ⟨ht, by linarith⟩ Bw w hwH hwTC
  refine ⟨w, c4_classical s a β ha hβ ρ ht hψB hw2 (fun i hi => hwc i (by omega)) hwt (fun r hr => rfl) hg2
    (fun r₀ hr₀ ε hε => ?_) (fun r hr x => ?_)⟩
  · obtain ⟨δ, hδ, h⟩ := hTCg 0 (Nat.zero_le _) ε hε
    exact ⟨δ, hδ, fun r hr hd y => c5_norm0_le (h r hr r₀ hr₀ hd y)⟩
  · exact hwm r hr x

end HRS.MS.S104e.C
