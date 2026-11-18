import HRS.MS.UlOrbitAux1
import HRS.MS.UlClass

/-!
# UL-6 (S5.1 part 2, orbit data), part 2: levels, time shifts, `C_b^k` bound

Infrastructure packet UL-6; not a manuscript row.  Helper lemmas carry the prefix `ul6_`.

* `ul6_mono_level`: an evolution at level `k₁` is an evolution at every level `k ≤ k₁` (same datum, same family).
* `ul6_shift`: for the (autonomous) generator of `fixedViscosityCoeff`, `r ↦ u (r + δ)` is an evolution with terminal
  time `t - δ` and the same datum (time homogeneity); `ul6_homog` combines it with `ul_evolution_unique`.
* `ul6_cb_bound`: for an evolution `u` at a level `k₁ ≥ K` (`k + d/2 < K`, `4 + d/2 < K`) with datum `g ∈ UlClosure K`,
  `‖u 0‖_{C_b^k} ≤ C ‖g‖_{H^K_ul}`, `C` depending on `T` and the data only (not on `g`, `t`, `k₁`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Ul

open HRS HRS.Whole

variable {d : ℕ}

/-- The standing hypotheses of part 2 of S5.1 (the data of `ul_adjoint_orbit_bounds`). -/
structure UlOrb (d : ℕ) (s ν : ℝ) (ρ : Euc d → ℝ) (σ : Euc d → Euc d) (c : Euc d → Euc d)
    (θ : Euc d → ℝ) : Prop where
  hd : 2 ≤ d
  hs0 : 0 ≤ s
  hsd : s < (d : ℝ)
  hν : 0 < ν
  hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ
  hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i
  hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x
  hθ : IsUlCutoff θ

theorem UlOrb.smooth {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}
    (O : UlOrb d s ν ρ σ c θ) : IsSmoothBounded c := by
  rw [O.hc]
  exact part2_c_smoothBounded O.hd O.hs0 O.hsd ρ O.hρ σ O.hσ

theorem UlOrb.hyp {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d} {θ : Euc d → ℝ}
    (O : UlOrb d s ν ρ σ c θ) {K : ℕ} (hK : (4 : ℝ) + (d : ℝ) / 2 < K) :
    UlHyp s (-1 : Matrix (Fin d) (Fin d) ℝ) ρ c ν K θ :=
  ⟨O.hs0, O.hsd, O.hρ, O.smooth, O.hν, hK, O.hθ⟩

section Level
variable {θ : Euc d → ℝ}

theorem ul6_mono_level {k k₁ : ℕ} (hk : k ≤ k₁) {C : WholeCoeff d} {t : ℝ} {g : Euc d → ℝ}
    {u : ℝ → Euc d → ℝ} (hu : IsUlBackwardEvolution θ k₁ C t g u) :
    IsUlBackwardEvolution θ k C t g u :=
  ⟨hu.classicalSol, fun r hr => ulClosure_mono hk θ _ (hu.mem r hr), fun r₀ h0 ε hε => by
    obtain ⟨δ, hδ, h⟩ := hu.cont r₀ h0 ε hε
    exact ⟨δ, hδ, fun r hr hd => (ul0_ulNormE_mono hk θ _).trans (h r hr hd)⟩⟩

theorem ul6_gen_const (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : Euc d → Euc d) (ρ : Euc d → ℝ)
    (r r' : ℝ) (φ : Euc d → ℝ) (x : Euc d) :
    generatorW (fixedViscosityCoeff s M Q ν c ρ) r φ x = generatorW (fixedViscosityCoeff s M Q ν c ρ) r' φ x :=
  rfl

theorem ul6_shift (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : Euc d → Euc d) (ρ : Euc d → ℝ)
    {k : ℕ} {t δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) t) {g : Euc d → ℝ} {u : ℝ → Euc d → ℝ}
    (hu : IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) t g u) :
    IsUlBackwardEvolution θ k (fixedViscosityCoeff s M Q ν c ρ) (t - δ) g (fun r => u (r + δ)) := by
  have hsh : ∀ r ∈ Icc (0 : ℝ) (t - δ), r + δ ∈ Icc (0 : ℝ) t := fun r hr =>
    ⟨by linarith [hr.1, hδ.1], by linarith [hr.2]⟩
  have hmap : Continuous (fun p : Icc (0 : ℝ) (t - δ) × Euc d =>
      ((⟨p.1.1 + δ, hsh p.1.1 p.1.2⟩ : Icc (0 : ℝ) t), p.2)) :=
    (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add continuous_const) _).prodMk
      continuous_snd
  have hcl := hu.classicalSol
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => hu.mem _ (hsh r hr), fun r₀ h0 ε hε => ?_⟩
  · exact fun r hr => hcl.c2 _ (hsh r hr)
  · intro j hj
    obtain ⟨B, hB⟩ := hcl.bdd j hj
    exact ⟨B, fun r hr x => hB _ (hsh r hr) x⟩
  · intro j hj
    exact (hcl.cont_c2 j hj).comp hmap
  · show u (t - δ + δ) = g
    rw [sub_add_cancel]; exact hcl.terminal
  · intro x r hr
    have hr' : r + δ ∈ Ioo (0 : ℝ) t := ⟨by linarith [hr.1, hδ.1], by linarith [hr.2]⟩
    refine ((hcl.time_deriv x (r + δ) hr').comp_add_const r δ).congr_deriv ?_
    rw [ul6_gen_const s M Q ν c ρ (r + δ) r]
  · have e : (fun p : Icc (0 : ℝ) (t - δ) × Euc d => generatorW (fixedViscosityCoeff s M Q ν c ρ) p.1.1
        (u (p.1.1 + δ)) p.2) = (fun p : Icc (0 : ℝ) t × Euc d => generatorW (fixedViscosityCoeff s M Q ν c ρ) p.1.1
        (u p.1.1) p.2) ∘ (fun p : Icc (0 : ℝ) (t - δ) × Euc d =>
          ((⟨p.1.1 + δ, hsh p.1.1 p.1.2⟩ : Icc (0 : ℝ) t), p.2)) := by
      funext p
      exact ul6_gen_const s M Q ν c ρ _ _ _ _
    show Continuous (fun p : Icc (0 : ℝ) (t - δ) × Euc d => generatorW (fixedViscosityCoeff s M Q ν c ρ) p.1.1
        (u (p.1.1 + δ)) p.2)
    rw [e]
    exact hcl.cont_time_deriv.comp hmap
  · obtain ⟨B, hB⟩ := hcl.bdd_time_deriv
    refine ⟨B, fun r hr x => ?_⟩
    rw [ul6_gen_const s M Q ν c ρ r (r + δ)]
    exact hB _ (hsh r hr) x
  · obtain ⟨δ', hδ', h⟩ := hu.cont (r₀ + δ) (hsh r₀ h0) ε hε
    refine ⟨δ', hδ', fun r hr hd => h (r + δ) (hsh r hr) ?_⟩
    rwa [add_sub_add_right_eq_sub]

/-- time homogeneity: two evolutions with the same datum, terminal times `t` and `t - δ`, are related by the shift -/
theorem ul6_homog {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d}
    (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) {K : ℕ} (hK : (4 : ℝ) + (d : ℝ) / 2 < K)
    {t δ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) t) {g : Euc d → ℝ} {u u' : ℝ → Euc d → ℝ}
    (hu : IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) t g u)
    (hu' : IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) (t - δ) g u') :
    ∀ r ∈ Icc (0 : ℝ) (t - δ), u' r = u (r + δ) := fun r hr =>
  ul_evolution_unique O.hs0 O.hsd θ O.hθ K hK ν O.hν Q (-1) ρ O.hρ c O.smooth (sub_nonneg.2 hδ.2) hu'
    (ul6_shift s (-1) Q ν c ρ hδ hu) r hr

/-- **the `C_b^k` bound of the orbit values** -/
theorem ul6_cb_bound {s ν : ℝ} {ρ : Euc d → ℝ} {σ c : Euc d → Euc d}
    (O : UlOrb d s ν ρ σ c θ) (Q : Matrix (Fin d) (Fin d) ℝ) {K k : ℕ} (hK : (4 : ℝ) + (d : ℝ) / 2 < K)
    (hkK : (k : ℝ) + (d : ℝ) / 2 < K) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ g : Euc d → ℝ, UlClosure K θ g → ∀ k₁ : ℕ, K ≤ k₁ →
      ∀ u, IsUlBackwardEvolution θ k₁ (fixedViscosityCoeff s (-1) Q ν c ρ) t g u →
        UlClosure K θ (u 0) ∧ HRS.MemCb k (u 0) ∧
          HRS.cbNorm k (u 0) ≤ C * (ulNormE K θ g).toReal := by
  obtain ⟨Cev, hCev⟩ := ul_evolution_exists O.hs0 O.hsd θ O.hθ K hK T ν hT O.hν Q (-1) ρ O.hρ c O.smooth
  obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb K k hkK θ O.hθ
  refine ⟨Ccb * max Cev 0, by positivity, fun t ht g hg k₁ hk₁ u hu => ?_⟩
  obtain ⟨u₀, hu₀, hb₀⟩ := hCev t ht g hg
  have hu1 : IsUlBackwardEvolution θ K (fixedViscosityCoeff s (-1) Q ν c ρ) t g u := ul6_mono_level hk₁ hu
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht.1⟩
  have heq : u 0 = u₀ 0 :=
    ul_evolution_unique O.hs0 O.hsd θ O.hθ K hK ν O.hν Q (-1) ρ O.hρ c O.smooth ht.1 hu1 hu₀ 0 h0
  have hcl : UlClosure K θ (u 0) := hu1.mem 0 h0
  obtain ⟨hm, hn⟩ := hcb _ hcl
  refine ⟨hcl, hm, hn.trans ?_⟩
  have hfin := ul0_ulNormE_lt_top_of_closure K θ O.hθ hg
  have h1 : ulNormE K θ (u 0) ≤ ENNReal.ofReal Cev * ulNormE K θ g := by rw [heq]; exact hb₀ 0 h0
  have h2 : (ulNormE K θ (u 0)).toReal ≤ max Cev 0 * (ulNormE K θ g).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    exact this
  calc Ccb * (ulNormE K θ (u 0)).toReal ≤ Ccb * (max Cev 0 * (ulNormE K θ g).toReal) :=
        mul_le_mul_of_nonneg_left h2 hCcb.le
    _ = _ := by ring

end Level

end HRS.MS.Ul
