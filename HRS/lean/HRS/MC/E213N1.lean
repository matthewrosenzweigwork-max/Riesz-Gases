import HRS.MC.E213K
import HRS.Main.ThermLinAux4

/-!
# E213N1 (e3): the global stochastic convolution of the half-line Gaussian martingale

For a smooth positive trajectory `htr`, the half-line Gaussian Hilbert martingale `G` of `E213K` (covariation
`noiseDens` on every window `[0,S]`) and the dual evolution `Vev` of `adjk_evolution_moment_proof`, there is ONE
process `Zs : ℝ → Ω_G → E_m` with measurable sections, a.s. continuous on every `[0,n]`, which is the
stochastic convolution `∫_0^t Vev(t,σ) dG(σ)` at every time `t ≥ 0` (per-horizon convolutions glued with
`t25p_stochConv_unique`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213N

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.ThermLin

variable {d : ℕ}

/-- The global covariation density of the noise: `σ ↦ 1_{σ ≥ 0} covForm m q (ρ_σ)`. -/
def noiseDens (m q : ℝ) (ρ : ℝ → Torus d → ℝ) :
    ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ :=
  fun σ => if 0 ≤ σ then covForm m q (withDensityReal (ρ σ)) else 0

/-- The data of the global noise: continuous Gaussian Hilbert martingale `G` (covariation `noiseDens` on
every window), and its stochastic convolution `Zs` against `Vev`. -/
structure IsGlobalNoise (m q : ℝ) (ρ : ℝ → Torus d → ℝ)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (G Zs : ℝ → Ω → NegSobolev d m) : Prop where
  cont : ∀ ω, Continuous fun τ => G τ ω
  zero : ∀ ω, G 0 ω = 0
  mart : ∀ S : ℝ, 0 ≤ S →
    IsHilbertMartingaleWithCovariation P ℱ S G (fun r _ => noiseDens m q ρ r)
  meas : ∀ t, Measurable (Zs t)
  contOn : ∀ n : ℕ, ∀ᵐ ω ∂P, ContinuousOn (fun t => Zs t ω) (Icc 0 (n : ℝ))
  conv : ∀ t : ℝ, 0 ≤ t →
    IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t)
  zero_Zs : Zs 0 =ᵐ[P] fun _ => 0

theorem e213n_exists_global_noise {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) :
    ∃ (Cr : ℝ) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ℱ : Filtration ℝ mΩ) (G Zs : ℝ → Ω → NegSobolev d m),
      0 ≤ Cr ∧ IsDualEvolution htr.dyn ρ m Vev ∧ (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
      (∀ r t : ℝ, 0 ≤ r → r ≤ t → ‖Vev t r‖ ≤ Cr) ∧
      IsGlobalNoise m β⁻¹ ρ Vev P ℱ G Zs := by
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ := adjk_evolution_along_trajectory hd htr m
  obtain ⟨Vev, hdual, hplain, hB1⟩ := adjk_evolution_moment_proof hd htr m 2 le_rfl
  have hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → ‖Vev t r‖ ≤ Cr := by
    intro r t hr hrt
    rw [t25p_dual_unique hdual hdualA hr hrt]
    refine (hdecA r t hr hrt).trans ?_
    have h1 : Real.exp (-cr * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sub_nonneg.2 hrt]
    nlinarith
  obtain ⟨Ωg, mΩg, Pg, hPg, ℱ, G, hGc, hGz, hmart⟩ :=
    E213K.exists_gaussian_martingale_top (noiseDens m β⁻¹ ρ)
      (E213K.e213k_isDetCovDensity_global_traj hd htr hm)
  haveI := hPg
  have hGm : ∀ t, Measurable (G t) := fun t =>
    HRS.Uniform.Q07c.measurable_of_isHM (hmart 0 le_rfl) t
  -- per-horizon convolutions
  have hper : ∀ n : ℕ, ∃ Zm : ℝ → Ωg → NegSobolev d m, (∀ t, Measurable (Zm t)) ∧
      (∀ᵐ ω ∂Pg, ContinuousOn (fun t => Zm t ω) (Icc 0 ((n : ℝ) + 1))) ∧
      ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
        IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zm t) := by
    intro n
    have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    obtain ⟨C, hC0, hC⟩ := hB1 ((n : ℝ) + 1) hT
    have hG' : IsHilbertMartingaleWithCovariation Pg ℱ (0 + ((n : ℝ) + 1)) G
        (fun r _ => noiseDens m β⁻¹ ρ r) := by
      rw [zero_add]; exact hmart _ hT.le
    obtain ⟨Zs, hZS, hZc, hZm, -⟩ := hC Ωg Pg ℱ 0 ((n : ℝ) + 1) le_rfl hT le_rfl G _ hG'
    simp only [zero_add] at hZS hZc hZm
    obtain ⟨Zm, hZmm, hZmc, hZmae⟩ := thermlin_measurable_version (P := Pg) hT.le Zs hZm hZc
    exact ⟨Zm, hZmm, hZmc, fun t ht => thermlin_isStochConv_congr (hZS t ht) (hZmae t ht)⟩
  choose Zm hZmm hZmc hZmS using hper
  -- consistency of the per-horizon convolutions
  have hagree : ∀ n k : ℕ, ∀ᵐ ω ∂Pg, ∀ t ∈ Icc (0 : ℝ) (min (n : ℝ) k + 1), Zm n t ω = Zm k t ω := by
    intro n k
    have hmn : min (n : ℝ) k + 1 ≤ (n : ℝ) + 1 := by gcongr; exact min_le_left _ _
    have hmk : min (n : ℝ) k + 1 ≤ (k : ℝ) + 1 := by gcongr; exact min_le_right _ _
    have hlt : (0 : ℝ) < min (n : ℝ) k + 1 :=
      lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (le_min (Nat.cast_nonneg n) (Nat.cast_nonneg k)))
    refine t25p_ae_forall_Icc Pg hlt (Zm n) (Zm k) ?_ ?_ ?_
    · filter_upwards [hZmc n] with ω hω using hω.mono (Icc_subset_Icc_right hmn)
    · filter_upwards [hZmc k] with ω hω using hω.mono (Icc_subset_Icc_right hmk)
    · intro t ht
      exact t25p_stochConv_unique Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) hGm ht.1
        (hZmm n t).aemeasurable (hZmm k t).aemeasurable
        (hZmS n t ⟨ht.1, ht.2.trans hmn⟩) (hZmS k t ⟨ht.1, ht.2.trans hmk⟩)
  have hall : ∀ᵐ ω ∂Pg, ∀ n k : ℕ, ∀ t ∈ Icc (0 : ℝ) (min (n : ℝ) k + 1), Zm n t ω = Zm k t ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hagree n k
  have hglue : ∀ ω, (∀ n k : ℕ, ∀ t ∈ Icc (0 : ℝ) (min (n : ℝ) k + 1), Zm n t ω = Zm k t ω) →
      ∀ N : ℕ, ∀ t ∈ Icc (0 : ℝ) ((N : ℝ) + 1), Zm ⌈t⌉₊ t ω = Zm N t ω := by
    intro ω hω N t ht
    refine hω ⌈t⌉₊ N t ⟨ht.1, ?_⟩
    rw [← min_add_add_right]
    exact le_min ((Nat.le_ceil t).trans (le_add_of_nonneg_right zero_le_one)) ht.2
  have hconv : ∀ t : ℝ, 0 ≤ t →
      IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zm ⌈t⌉₊ t) := fun t ht =>
    hZmS ⌈t⌉₊ t ⟨ht, (Nat.le_ceil t).trans (le_add_of_nonneg_right zero_le_one)⟩
  refine ⟨Cr, Vev, Ωg, mΩg, Pg, hPg, ℱ, G, fun t ω => Zm ⌈t⌉₊ t ω, hCr.le, hdual, hplain, hKb,
    ⟨hGc, hGz, hmart, fun t => hZmm _ t, ?_, hconv, ?_⟩⟩
  · intro n
    filter_upwards [hall, hZmc n] with ω hω hc
    refine (hc.mono (Icc_subset_Icc_right (by linarith))).congr fun t ht => ?_
    exact hglue ω hω n t ⟨ht.1, ht.2.trans (by linarith)⟩
  · exact thermlin_stochConv_zero (by simpa using hconv 0 le_rfl) (hZmm _ 0)

end HRS.MC.E213N

end
