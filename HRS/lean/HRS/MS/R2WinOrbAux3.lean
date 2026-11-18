import HRS.MS.R2WinOrbAux2
import HRS.MS.UlOrbitAux3

/-!
# S10.3 (stationary half), part 3: explicit-order symbol bounds of the orbit data `L^a φ`

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  `s103_chain`: for the generator `L` of `fixedViscosityCoeff` (rapidly decaying `ρ`,
`σ`, `c = σ - ∇g*ρ`) and every Schwartz `f`, `‖D^j L^a f(x)‖ ≤ K ‖f‖_{Σ^{n*}} (1+‖x‖)^{-(s+1)-j}` for `j ≤ μ`, with the explicit order
`n* = s103_nstar s (μ + 2a)` (the analogue `ul6_orbit_S` hides the order).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- The explicit oscillator order for symbol bounds up to order `μ`. -/
def s103_nstar (d : ℕ) (s : ℝ) (μ : ℕ) : ℕ := μ + ⌈s + 1⌉₊ + ⌊(μ : ℝ) + (d : ℝ) / 2⌋₊ + 1

theorem s103_nstar_mono (s : ℝ) {μ μ' : ℕ} (h : μ ≤ μ') : s103_nstar d s μ ≤ s103_nstar d s μ' := by
  unfold s103_nstar
  have : ⌊(μ : ℝ) + (d : ℝ) / 2⌋₊ ≤ ⌊(μ' : ℝ) + (d : ℝ) / 2⌋₊ :=
    Nat.floor_le_floor (by gcongr)
  omega

theorem s103_schwartz_S (s : ℝ) (μ : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : SchwartzMap (Euc d) ℝ, ul6S (-(s + 1)) μ (C * oscNorm (s103_nstar d s μ : ℝ) f) f := by
  have hj : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
      (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) * ‖iteratedFDeriv ℝ j f x‖ ≤
        C * oscNorm (((j + ⌈s + 1⌉₊) + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f :=
    fun j => s103_weighted (j + ⌈s + 1⌉₊) j
  choose C hC0 hC using hj
  refine ⟨∑ j ∈ Finset.range (μ + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun f j hj x => ?_⟩
  have hjm : j ∈ Finset.range (μ + 1) := Finset.mem_range.2 (by omega)
  have hw := ul6_w_pos' x
  have h1 : (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) * (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) ≥ 1 := by
    have hnat : ((j + ⌈s + 1⌉₊ : ℕ) : ℝ) = (j : ℝ) + (⌈s + 1⌉₊ : ℝ) := by push_cast; ring
    rw [← Real.rpow_natCast, hnat, ← Real.rpow_add hw]
    refine Real.one_le_rpow (by linarith [norm_nonneg x]) ?_
    have : s + 1 ≤ (⌈s + 1⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hq : 0 ≤ (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := Real.rpow_nonneg hw.le _
  have h2 : ‖iteratedFDeriv ℝ j f x‖ ≤
      C j * oscNorm (((j + ⌈s + 1⌉₊) + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f *
        (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := by
    have := hC j f x
    have hp : 0 < (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) := by positivity
    calc ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ *
          ((1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) * (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊)) := by
          nlinarith [norm_nonneg (iteratedFDeriv ℝ j f x)]
      _ = (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) * ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hq
  refine h2.trans (mul_le_mul_of_nonneg_right ?_ hq)
  have hosc : oscNorm (((j + ⌈s + 1⌉₊) + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤
      oscNorm (s103_nstar d s μ : ℝ) f := by
    refine s103_osc_mono ?_ f
    unfold s103_nstar
    have : ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ ≤ ⌊(μ : ℝ) + (d : ℝ) / 2⌋₊ :=
      Nat.floor_le_floor (by gcongr)
    omega
  have hCj : C j ≤ ∑ j ∈ Finset.range (μ + 1), C j :=
    Finset.single_le_sum (f := C) (fun _ _ => hC0 _) hjm
  have hC00 : 0 ≤ ∑ j ∈ Finset.range (μ + 1), C j := Finset.sum_nonneg fun j _ => hC0 j
  exact mul_le_mul hCj hosc (Real.sqrt_nonneg _) hC00

/-- The orbit data with explicit order. -/
theorem s103_chain (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (ν : ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) {ρ : Euc d → ℝ} (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    {σ : Euc d → Euc d} (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i)
    {c : Euc d → Euc d} (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) (a : ℕ) :
    ∀ μ : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ f : SchwartzMap (Euc d) ℝ,
      ul6S (-(s + 1)) μ (K * oscNorm (s103_nstar d s (μ + 2 * a) : ℝ) f)
        ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f) := by
  induction a with
  | zero =>
    intro μ
    obtain ⟨C, hC0, hC⟩ := s103_schwartz_S (d := d) s μ
    exact ⟨C, hC0, fun f => by simpa using hC f⟩
  | succ a ih =>
    intro μ
    obtain ⟨K, hK0, hK⟩ := ih (μ + 2)
    obtain ⟨ψ, hψ⟩ := hρ
    have hρr : UlRapid ρ := by rw [← hψ]; exact ult_schwartz_rapid ψ
    choose φ hφ using hσ
    have hσr : ∀ i, UlRapid (fun x => σ x i) := fun i => by
      rw [← hφ i]; exact ult_schwartz_rapid (φ i)
    obtain ⟨C2, hC20, hC2⟩ := ul6_L_step (by omega) hs0 hsd ν Q hρr hσr hc μ
    refine ⟨C2 * K, by positivity, fun f => ?_⟩
    rw [Function.iterate_succ_apply']
    obtain ⟨hcd, hdec, -⟩ := orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ (fun i => ⟨φ i, hφ i⟩) c hc f a
    have hsym : UlSym (-(s + 1))
        ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f) := by
      refine ⟨hcd, fun m => ?_⟩
      obtain ⟨C, hC0, hC⟩ := hdec m
      refine ⟨C, hC0, fun x => ?_⟩
      have e : -(s + 1 + (m : ℝ)) = -(s + 1) - (m : ℝ) := by ring
      simpa [e] using hC x
    have := hC2 _ _ hsym (by
      have h := hK f
      have e : μ + 2 + 2 * a = μ + 2 * (a + 1) := by ring
      rw [e] at h
      exact h)
    have e2 : C2 * (K * oscNorm (s103_nstar d s (μ + 2 * (a + 1)) : ℝ) f) =
        C2 * K * oscNorm (s103_nstar d s (μ + 2 * (a + 1)) : ℝ) f := by ring
    rw [e2] at this
    exact this

end HRS.MS.R2WinOrb

end
