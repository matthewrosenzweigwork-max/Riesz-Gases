import HRS.MC.E214D2
import HRS.MC.E213N3
import HRS.Sections.AllTimeAux1

/-!
# E214D3: feasibility prototype of P1, part 3: the stationary trajectory, global convolutions, the target

* `stationary_traj`: `IsSmoothPositiveTrajectory d s β V ρβ (fun _ => ρβ)` for the thermal density of a regime.
* `e214d_global_conv`: for ANY continuous Gaussian Hilbert martingale `G` with covariation `noiseDens m β⁻¹ ρ` on
  every window there is ONE global stochastic convolution `Zs` against the dual evolution of the trajectory
  (`IsGlobalNoise`); copy of the construction of `E213N.e213n_exists_global_noise` with `G` as an input.  Applied to
  `G = (block martingale).fst`, `.snd` this produces the two noise convolutions driven by the SAME martingale.
* `isStochConv_of_map`, `pairEvol`, `pullbackVec_pairEvol_fstL`: the convolution against `G ∈ E×E` through `fst` is
  the convolution of `fst ∘ G`, and its pull-back vector is `inl2` of the single-field pull-back vector; this is what
  allows `gfb4_vec_gaussian` (on `H2`) to be applied to the joint vector of the two fields.
* `exists_coupled_pair`: the target statement of P1 (sorry).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214D

open HRS HRS.Sec7 HRS.Uniform HRS.Uniform.Q14 HRS.Uniform.Q45 HRS.GF HRS.T25P HRS.AdjK HRS.ThermLin HRS.MC.E213N

variable {d : ℕ}

/-- The stationary trajectory `ρ^t ≡ ρβ` of a regime. -/
theorem stationary_traj (R : Regime d) :
    IsSmoothPositiveTrajectory d R.D.s R.β R.D.V R.ρβ (fun _ => R.ρβ) := by
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  have hρs : SmoothPosDensity R.ρβ := ⟨hth.1, hsm, hpos⟩
  refine ⟨R.D.hs0, R.D.hsd, R.hβ, R.hV, hρs, fun K _ => ⟨fun _ => PDE.coeffOf R.ρβ, ?_, ?_⟩⟩
  · exact HRS.Uniform.Q48b.q48b_isMFSolutionHK (by have := R.hd; omega) R.D.s R.D.hs0 R.D.hsd R.β R.hβ
      R.D.V R.hV R.ρβ hth hρs.smooth hρs.pos K
  · exact fun t _ => congrFun (HRS.Uniform.Q48b.q48b_mfPath_const R.ρβ hρs.smooth) t

theorem stationary_traj_dyn (R : Regime d) : (stationary_traj R).dyn = R.D :=
  (alltime_D_eq R).symm

/-- One global stochastic convolution against the dual evolution, for a given Gaussian martingale. -/
theorem e214d_global_conv {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → NegSobolev d m}
    (hGc : ∀ ω, Continuous fun τ => G τ ω) (hGz : ∀ ω, G 0 ω = 0)
    (hmart : ∀ S : ℝ, 0 ≤ S →
      IsHilbertMartingaleWithCovariation P ℱ S G (fun r _ => noiseDens m β⁻¹ ρ r)) :
    ∃ (Cr : ℝ) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (Zs : ℝ → Ω → NegSobolev d m),
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
  have hGm : ∀ t, Measurable (G t) := fun t =>
    HRS.Uniform.Q07c.measurable_of_isHM (hmart 0 le_rfl) t
  -- per-horizon convolutions
  have hper : ∀ n : ℕ, ∃ Zm : ℝ → Ω → NegSobolev d m, (∀ t, Measurable (Zm t)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => Zm t ω) (Icc 0 ((n : ℝ) + 1))) ∧
      ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
        IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zm t) := by
    intro n
    have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    obtain ⟨C, hC0, hC⟩ := hB1 ((n : ℝ) + 1) hT
    have hG' : IsHilbertMartingaleWithCovariation P ℱ (0 + ((n : ℝ) + 1)) G
        (fun r _ => noiseDens m β⁻¹ ρ r) := by
      rw [zero_add]; exact hmart _ hT.le
    obtain ⟨Zs, hZS, hZc, hZm, -⟩ := hC Ω P ℱ 0 ((n : ℝ) + 1) le_rfl hT le_rfl G _ hG'
    simp only [zero_add] at hZS hZc hZm
    obtain ⟨Zm, hZmm, hZmc, hZmae⟩ := thermlin_measurable_version (P := P) hT.le Zs hZm hZc
    exact ⟨Zm, hZmm, hZmc, fun t ht => thermlin_isStochConv_congr (hZS t ht) (hZmae t ht)⟩
  choose Zm hZmm hZmc hZmS using hper
  -- consistency of the per-horizon convolutions
  have hagree : ∀ n k : ℕ, ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) (min (n : ℝ) k + 1), Zm n t ω = Zm k t ω := by
    intro n k
    have hmn : min (n : ℝ) k + 1 ≤ (n : ℝ) + 1 := by gcongr; exact min_le_left _ _
    have hmk : min (n : ℝ) k + 1 ≤ (k : ℝ) + 1 := by gcongr; exact min_le_right _ _
    have hlt : (0 : ℝ) < min (n : ℝ) k + 1 :=
      lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (le_min (Nat.cast_nonneg n) (Nat.cast_nonneg k)))
    refine t25p_ae_forall_Icc P hlt (Zm n) (Zm k) ?_ ?_ ?_
    · filter_upwards [hZmc n] with ω hω using hω.mono (Icc_subset_Icc_right hmn)
    · filter_upwards [hZmc k] with ω hω using hω.mono (Icc_subset_Icc_right hmk)
    · intro t ht
      exact t25p_stochConv_unique P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) hGm ht.1
        (hZmm n t).aemeasurable (hZmm k t).aemeasurable
        (hZmS n t ⟨ht.1, ht.2.trans hmn⟩) (hZmS k t ⟨ht.1, ht.2.trans hmk⟩)
  have hall : ∀ᵐ ω ∂P, ∀ n k : ℕ, ∀ t ∈ Icc (0 : ℝ) (min (n : ℝ) k + 1), Zm n t ω = Zm k t ω :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hagree n k
  have hglue : ∀ ω, (∀ n k : ℕ, ∀ t ∈ Icc (0 : ℝ) (min (n : ℝ) k + 1), Zm n t ω = Zm k t ω) →
      ∀ N : ℕ, ∀ t ∈ Icc (0 : ℝ) ((N : ℝ) + 1), Zm ⌈t⌉₊ t ω = Zm N t ω := by
    intro ω hω N t ht
    refine hω ⌈t⌉₊ N t ⟨ht.1, ?_⟩
    rw [← min_add_add_right]
    exact le_min ((Nat.le_ceil t).trans (le_add_of_nonneg_right zero_le_one)) ht.2
  have hconv : ∀ t : ℝ, 0 ≤ t →
      IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zm ⌈t⌉₊ t) := fun t ht =>
    hZmS ⌈t⌉₊ t ⟨ht, (Nat.le_ceil t).trans (le_add_of_nonneg_right zero_le_one)⟩
  refine ⟨Cr, Vev, fun t ω => Zm ⌈t⌉₊ t ω, hCr.le, hdual, hplain, hKb,
    ⟨hGc, hGz, hmart, fun t => hZmm _ t, ?_, hconv, ?_⟩⟩
  · intro n
    filter_upwards [hall, hZmc n] with ω hω hc
    refine (hc.mono (Icc_subset_Icc_right (by linarith))).congr fun t ht => ?_
    exact hglue ω hω n t ⟨ht.1, ht.2.trans (by linarith)⟩
  · exact thermlin_stochConv_zero (by simpa using hconv 0 le_rfl) (hZmm _ 0)


/-! ### Convolution through a projection -/

theorem isStochConv_of_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {VE : ℝ → ℝ → E →L[ℝ] E} (L : H →L[ℝ] E) {M : ℝ → Ω → H} {a t : ℝ} {Z : Ω → E}
    (h : IsStochConv P VE (ContinuousLinearMap.id ℝ E) (fun τ ω => L (M τ ω)) a t Z) :
    IsStochConv P VE L M a t Z := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  have e : riemannSum VE L M t r = riemannSum VE (ContinuousLinearMap.id ℝ E) (fun τ ω => L (M τ ω)) t r := by
    funext ω
    simp [riemannSum, map_sub]
  rw [e]
  exact hh n r h0 hn hmono hmesh

/-- The evolution data with `j = L : E×E → E` and `V` on the `E` factor (only `j` and `VE` are used by the
convolution machinery). -/
def pairEvol {γ : ℝ} (L : H2 d γ →L[ℝ] NegSobolev d γ)
    (V : ℝ → ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ) : EvolData (H2 d γ) (NegSobolev d γ) where
  j := L
  VH := fun _ _ => 0
  VE := V
  D := ⊥
  A := fun _ => 0

theorem pullbackVec_pairEvol_fstL {γ : ℝ} (V : ℝ → ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ) (t r : ℝ)
    (ℓ : NegSobolev d γ →L[ℝ] ℝ) :
    pullbackVec (pairEvol (WithLp.fstL 2 ℝ (NegSobolev d γ) (NegSobolev d γ)) V) t r ℓ =
      inl2 γ (pullbackVec (HRS.Uniform.Comp28.plainData V) t r ℓ) := by
  refine ext_inner_right ℝ fun z => ?_
  rw [pullback_inner]
  simp [pairEvol, inl2, WithLp.prod_inner_apply, pullback_inner]

theorem pullbackVec_pairEvol_sndL {γ : ℝ} (V : ℝ → ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ) (t r : ℝ)
    (ℓ : NegSobolev d γ →L[ℝ] ℝ) :
    pullbackVec (pairEvol (WithLp.sndL 2 ℝ (NegSobolev d γ) (NegSobolev d γ)) V) t r ℓ =
      inr2 γ (pullbackVec (HRS.Uniform.Comp28.plainData V) t r ℓ) := by
  refine ext_inner_right ℝ fun z => ?_
  rw [pullback_inner]
  simp [pairEvol, inr2, WithLp.prod_inner_apply, pullback_inner]

end HRS.MC.E214D

end
