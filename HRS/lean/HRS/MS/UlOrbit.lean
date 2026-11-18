import HRS.MS.UlOrbitAux3
import HRS.MS.UlTailTie

/-!
# UL-6 (S5.1 part 2, orbit data), part 4: assembly of the orbit bounds

Infrastructure packet UL-6; not a manuscript row.  Helper lemmas carry the prefix `ul6_`.

Standing data `O : UlOrb d s ν ρ σ c θ` (part 2 of S5.1), `Cf = fixedViscosityCoeff s (-1) Q ν c ρ`,
`g_a = L^a f`, `K = max (⌊4 + d/2⌋ + 1) (⌊k + d/2⌋ + 1)` the common level and `k₁ ≥ K` the level of the statement.

* `ul6_exists_F`: for every Schwartz `f` the family `F a t = u_a^t(0)` exists (`ul_evolution_exists` at level `k₁`).
* `ul6_cb_sum`: every family `F` compatible with the evolutions satisfies `MemCb k (F a t)` and
  `∑_a ‖F a t‖_{C_b^k} ≤ C ‖f‖_{Σ^J}` (the level-`k₁` evolution is a level-`K` evolution, `ul6_cb_bound`; the data
  `L^a f` are bounded in `H^K_ul` by `oscNorm J f`, `ul6_orbit_ul`).
* `ul6_main_diff`: the difference quotients `h⁻¹ (F a (t+h) - F a t) → F (a+1) t` in `C_b^k` (time homogeneity
  `ul6_homog`, the time-integral identity `ul6_duhamel_time` and `ul6_dq`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Ul

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

section Main
variable {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}

/-- the iterates of the generator, as a function of the order -/
abbrev ul6L (s : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : Euc d → Euc d) (ρ : Euc d → ℝ)
    (f : SchwartzMap (Euc d) ℝ) (a : ℕ) : Euc d → ℝ :=
  (fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f

theorem ul6L_succ (Q : Matrix (Fin d) (Fin d) ℝ) (f : SchwartzMap (Euc d) ℝ) (a : ℕ) :
    ul6L s Q ν c ρ f (a + 1) = fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0
      (ul6L s Q ν c ρ f a) x := by
  unfold ul6L
  rw [Function.iterate_succ_apply']

theorem ul6_closure (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) (f : SchwartzMap (Euc d) ℝ)
    (a k : ℕ) : UlClosure k θ (ul6L s Q ν c ρ f a) :=
  orbitData_ulClosure O.hd O.hs0 O.hsd ν Q ρ O.hρ σ O.hσ c O.hc f a k θ O.hθ

/-- existence of the family `F` -/
theorem ul6_exists_F (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) {k₁ : ℕ}
    (hk₁ : (4 : ℝ) + (d : ℝ) / 2 < k₁) {T : ℝ} (hT : 0 ≤ T) (f : SchwartzMap (Euc d) ℝ) :
    ∃ F : Fin 4 → ℝ → Euc d → ℝ, ∀ a : Fin 4, ∀ t ∈ Icc (0 : ℝ) T, ∃ u,
      IsUlBackwardEvolution θ k₁ (fixedViscosityCoeff s (-1) Q ν c ρ) t (ul6L s Q ν c ρ f (a : ℕ)) u ∧
        F a t = u 0 := by
  obtain ⟨Cev, hCev⟩ := ul_evolution_exists O.hs0 O.hsd θ O.hθ k₁ hk₁ T ν hT O.hν Q (-1) ρ O.hρ c O.smooth
  have hex : ∀ (a : Fin 4) (t : ℝ), t ∈ Icc (0 : ℝ) T → ∃ u : ℝ → Euc d → ℝ,
      IsUlBackwardEvolution θ k₁ (fixedViscosityCoeff s (-1) Q ν c ρ) t (ul6L s Q ν c ρ f (a : ℕ)) u :=
    fun a t ht => by
      obtain ⟨u, hu, _⟩ := hCev t ht _ (ul6_closure O Q f (a : ℕ) k₁)
      exact ⟨u, hu⟩
  choose! U hU using hex
  exact ⟨fun a t => U a t 0, fun a t ht => ⟨U a t, hU a t ht, rfl⟩⟩

/-- the `C_b^k` bounds of the values -/
theorem ul6_cb_sum (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) {K k J : ℕ}
    (hK : (4 : ℝ) + (d : ℝ) / 2 < K) (hkK : (k : ℝ) + (d : ℝ) / 2 < K) {Cfin : ℝ} (hCfin0 : 0 ≤ Cfin)
    (hJ : ∀ (f : SchwartzMap (Euc d) ℝ) (a : ℕ), a ≤ 3 →
      ulNormE K θ (ul6L s Q ν c ρ f a) ≤ ENNReal.ofReal (Cfin * oscNorm (J : ℝ) f))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (F : Fin 4 → ℝ → Euc d → ℝ) (k₁ : ℕ), K ≤ k₁ →
      (∀ a : Fin 4, ∀ t ∈ Icc (0 : ℝ) T, ∃ u,
        IsUlBackwardEvolution θ k₁ (fixedViscosityCoeff s (-1) Q ν c ρ) t (ul6L s Q ν c ρ f (a : ℕ)) u ∧
          F a t = u 0) →
      ∀ t ∈ Icc (0 : ℝ) T, (∀ a, HRS.MemCb k (F a t)) ∧
        ∑ a : Fin 4, HRS.cbNorm k (F a t) ≤ C * oscNorm (J : ℝ) f := by
  obtain ⟨Ccb, hCcb0, hCcb⟩ := ul6_cb_bound O Q hK hkK T hT
  refine ⟨4 * (Ccb * Cfin), by positivity, fun f F k₁ hKk₁ hF t ht => ?_⟩
  have hone : ∀ a : Fin 4, HRS.MemCb k (F a t) ∧
      HRS.cbNorm k (F a t) ≤ Ccb * (Cfin * oscNorm (J : ℝ) f) := fun a => by
    obtain ⟨u, hu, hFu⟩ := hF a t ht
    obtain ⟨_, hm, hn⟩ := hCcb t ht (ul6L s Q ν c ρ f (a : ℕ)) (ul6_closure O Q f (a : ℕ) K) k₁ hKk₁ u hu
    rw [hFu]
    refine ⟨hm, hn.trans ?_⟩
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hJ f (a : ℕ) (by have := a.2; omega))
    have hos : 0 ≤ oscNorm (J : ℝ) f := Real.sqrt_nonneg _
    rw [ENNReal.toReal_ofReal (mul_nonneg hCfin0 hos)] at h1
    exact mul_le_mul_of_nonneg_left h1 hCcb0
  refine ⟨fun a => (hone a).1, ?_⟩
  calc ∑ a : Fin 4, HRS.cbNorm k (F a t) ≤ ∑ _a : Fin 4, Ccb * (Cfin * oscNorm (J : ℝ) f) :=
        Finset.sum_le_sum fun a _ => (hone a).2
    _ = 4 * (Ccb * Cfin) * oscNorm (J : ℝ) f := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- the difference quotients in `C_b^k` -/
theorem ul6_main_diff (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) {K k k₁ : ℕ}
    (hK : (4 : ℝ) + (d : ℝ) / 2 < K) (hkK : (k : ℝ) + (d : ℝ) / 2 < K) (hKk₁ : K ≤ k₁) {T : ℝ}
    (hT : 0 ≤ T) (f : SchwartzMap (Euc d) ℝ) (F : Fin 4 → ℝ → Euc d → ℝ)
    (hF : ∀ a : Fin 4, ∀ t ∈ Icc (0 : ℝ) T, ∃ u,
      IsUlBackwardEvolution θ k₁ (fixedViscosityCoeff s (-1) Q ν c ρ) t (ul6L s Q ν c ρ f (a : ℕ)) u ∧
        F a t = u 0)
    (a : Fin 4) (ha3 : (a : ℕ) < 3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ → t + h ∈ Icc (0 : ℝ) T →
      ∀ j ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ j
        (fun y => h⁻¹ * (F a (t + h) y - F a t y) - F ⟨(a : ℕ) + 1, by omega⟩ t y) x‖ ≤ ε := by
  have H := O.hyp hK
  obtain ⟨Cev, hCev⟩ := ul_evolution_exists O.hs0 O.hsd θ O.hθ K hK T ν hT O.hν Q (-1) ρ O.hρ c O.smooth
  obtain ⟨ua, hua, -⟩ := hCev T ⟨hT, le_rfl⟩ _ (ul6_closure O Q f (a : ℕ) K)
  obtain ⟨uw, huw, -⟩ := hCev T ⟨hT, le_rfl⟩ _ (ul6_closure O Q f ((a : ℕ) + 1) K)
  have huw' : IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) T
      (fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 (ul6L s Q ν c ρ f (a : ℕ)) x) uw := by
    rw [← ul6L_succ]; exact huw
  have Duh := ul6_duhamel_time O Q hK hT (ul6_closure O Q f (a : ℕ) K) hua huw'
  have hreg : UlReg K θ T uw := ⟨huw.mem, huw.cont⟩
  -- the values of `F` along the horizon-`T` evolutions
  have hFh : ∀ (b : Fin 4) (ub : ℝ → Euc d → ℝ),
      IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) T (ul6L s Q ν c ρ f (b : ℕ)) ub →
        ∀ σ' ∈ Icc (0 : ℝ) T, F b σ' = ub (T - σ') := by
    intro b ub hub σ' hσ'
    obtain ⟨u', hu', hFu'⟩ := hF b σ' hσ'
    have hδ : T - σ' ∈ Icc (0 : ℝ) T := ⟨sub_nonneg.2 hσ'.2, sub_le_self T hσ'.1⟩
    have hu'' : IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) (T - (T - σ'))
        (ul6L s Q ν c ρ f (b : ℕ)) u' := by
      rw [show T - (T - σ') = σ' by ring]; exact ul6_mono_level hKk₁ hu'
    have hhom := ul6_homog O Q hK hδ hub hu''
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (T - (T - σ')) := ⟨le_rfl, by linarith [hσ'.1]⟩
    have := hhom 0 h0
    rw [hFu', this, zero_add]
  have hua' : ∀ σ' ∈ Icc (0 : ℝ) T, F a σ' = ua (T - σ') := hFh a ua hua
  have hwa : ∀ σ' ∈ Icc (0 : ℝ) T, F ⟨(a : ℕ) + 1, by omega⟩ σ' = uw (T - σ') := by
    refine hFh ⟨(a : ℕ) + 1, by omega⟩ uw ?_
    exact huw
  obtain ⟨δ, hδ, hdq⟩ := ul6_dq H hT hreg Duh hkK ε hε
  refine ⟨δ, hδ, fun h hh hhδ hth j hj x => ?_⟩
  have hr : T - t ∈ Icc (0 : ℝ) T := ⟨sub_nonneg.2 ht.2, sub_le_self T ht.1⟩
  have hr' : T - (t + h) ∈ Icc (0 : ℝ) T := ⟨sub_nonneg.2 hth.2, sub_le_self T hth.1⟩
  have hd : |(T - t) - (T - (t + h))| < δ := by
    have : (T - t) - (T - (t + h)) = h := by ring
    rw [this]; exact hhδ
  have hne : T - (t + h) ≠ T - t := by
    intro heq; apply hh; linarith
  have := hdq (T - t) hr (T - (t + h)) hr' hd hne j hj x
  have e : (fun y => h⁻¹ * (F a (t + h) y - F a t y) - F ⟨(a : ℕ) + 1, by omega⟩ t y) =
      fun y => ((T - t) - (T - (t + h)))⁻¹ * (ua (T - (t + h)) y - ua (T - t) y) - uw (T - t) y := by
    funext y
    rw [hua' (t + h) hth, hua' t ht, hwa t ht]
    have : (T - t) - (T - (t + h)) = h := by ring
    rw [this]
  rw [e]
  exact this

end Main

end HRS.MS.Ul
