import HRS.MS.R2WinErrNL1
import HRS.MS.R2WinErrAux24

/-!
# S10.4, nonlinear branch, part 2: the terminal-time regularity input `S104nOrbit` and the evolution inequality

`S104nOrbit C φ T0` is the (only) analytic input about the adjoint orbit of a time dependent coefficient that the nonlinear branch of S10.4 needs, in
terms of `propagatorW` alone: for the terminal data `φ` and `L_tφ`,
* classical adjoint solutions exist for every terminal time `t ∈ [0,T0]` (`ex0`, `ex1`),
* for every initial time `r ∈ [0,T0]` the families `τ ↦ U(r,r+τ)φ` and `τ ↦ U(r,r+τ)L_{r+τ}φ` are `C_b²`-differentiable in `τ`
  (`diff01`, `diff12`; the generalisation of `S103nTermReg` to a general initial time `r`),
* `(t,r,x) ↦ ∇U(r,t)L_tφ(x)` is jointly continuous on `{0 ≤ r ≤ t ≤ T0}` (`jcont`).
For the stationary coefficient it is proved (`s104_stat_orbit`, `s104_prop_shift`); for the nonlinear trajectories it is the missing terminal-time
regularity of S10.3 (`S103nTermReg`).  `s104n_hevol` is the integrated evolution inequality for the pair functional.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.S53

variable {d N : ℕ}

/-- The terminal-time regularity input for the nonlinear branch (see the module docstring). -/
structure S104nOrbit (C : WholeCoeff d) (φ : Euc d → ℝ) (T0 : ℝ) : Prop where
  ex0 : ∀ t ∈ Icc (0 : ℝ) T0, ∃ f, IsClassicalAdjointW C t φ f
  ex1 : ∀ t ∈ Icc (0 : ℝ) T0, ∃ f, IsClassicalAdjointW C t (generatorW C t φ) f
  diff01 : ∀ r ∈ Icc (0 : ℝ) T0, S53Diff (T0 - r) (fun τ => propagatorW C r (r + τ) φ)
    (fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) φ))
  diff12 : ∀ r ∈ Icc (0 : ℝ) T0, ∃ G2 : ℝ → Euc d → ℝ, (∀ τ ∈ Icc (0 : ℝ) (T0 - r), MemCb 2 (G2 τ)) ∧
    S53Diff (T0 - r) (fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) φ)) G2
  jcont : ContinuousOn (fun q : ℝ × ℝ × Euc d => gradient (propagatorW C q.2.1 q.1 (generatorW C q.1 φ)) q.2.2)
    {q : ℝ × ℝ × Euc d | 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ T0}

open Classical in
lemma s104n_prop_cl {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} (hex : ∃ f, IsClassicalAdjointW C t φ f) :
    IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ) := by
  have : (fun r => propagatorW C r t φ) = hex.choose := by
    funext r; simp [propagatorW, hex]
  rw [this]; exact hex.choose_spec

lemma s104n_memCb_prop {C : WholeCoeff d} {t r : ℝ} {φ : Euc d → ℝ} (hex : ∃ f, IsClassicalAdjointW C t φ f)
    (hr : r ∈ Icc (0 : ℝ) t) : MemCb 2 (propagatorW C r t φ) := by
  have hu := s104n_prop_cl hex
  refine ⟨hu.c2 r hr, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hu.bdd j hj
  exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩

section Evol

variable {C : WholeCoeff d} {φ : Euc d → ℝ} {T0 : ℝ}

lemma S104nOrbit.cb0 (h : S104nOrbit C φ T0) {r τ : ℝ} (hr : r ∈ Icc (0 : ℝ) T0) (hτ : τ ∈ Icc (0 : ℝ) (T0 - r)) :
    MemCb 2 (propagatorW C r (r + τ) φ) :=
  s104n_memCb_prop (h.ex0 (r + τ) ⟨by linarith [hr.1, hτ.1], by linarith [hτ.2]⟩) ⟨hr.1, by linarith [hτ.1]⟩

lemma S104nOrbit.cb1 (h : S104nOrbit C φ T0) {r τ : ℝ} (hr : r ∈ Icc (0 : ℝ) T0) (hτ : τ ∈ Icc (0 : ℝ) (T0 - r)) :
    MemCb 2 (propagatorW C r (r + τ) (generatorW C (r + τ) φ)) :=
  s104n_memCb_prop (h.ex1 (r + τ) ⟨by linarith [hr.1, hτ.1], by linarith [hτ.2]⟩) ⟨hr.1, by linarith [hτ.1]⟩

end Evol

/-- The integrated evolution inequality for the commutator forcing along a nonlinear trajectory. -/
theorem s104n_hevol {Ω : Type*} {s m : ℝ} {C : WholeCoeff d} {ρ : ℝ → Euc d → ℝ} (hN : 0 < N)
    {α : MultiIndex d} {T0 : ℝ} (horb : S104nOrbit C (oscTestFun m α) T0)
    (hctx : ∀ r : ℝ, 0 ≤ r → ∃ Mρ, S53Ctx s (ρ r) Mρ)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {r t0 t : ℝ} (hr0 : 0 ≤ r) (hrt0 : r ≤ t0) (ht0t : t0 ≤ t)
    (htT : t ≤ T0) :
    ENNReal.ofReal |r2CommForcingMov C s m ρ X α t r ζ| ≤
      ENNReal.ofReal |r2CommForcingMov C s m ρ X α t0 r ζ| +
      ∫⁻ s' in Ioc t0 t, ENNReal.ofReal |s104_F2 C s m ρ X α (s', r) ζ| := by
  obtain ⟨Mρ, ctx⟩ := hctx r hr0
  have hrT : r ∈ Icc (0 : ℝ) T0 := ⟨hr0, hrt0.trans (ht0t.trans htT)⟩
  obtain ⟨G2, hG2, hd12⟩ := horb.diff12 r hrT
  have hc1 : S53Cont (T0 - r) (fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) (oscTestFun m α))) :=
    s53_cont_of_diff (fun τ hτ => horb.cb1 hrT hτ) hG2 hd12
  have hFm : ∀ u : ℝ, r ≤ u →
      r2CommForcingMov C s m ρ X α u r ζ = s53_Dk s (ρ r) (propagatorW C r (r + (u - r)) (oscTestFun m α))
        (X r.toNNReal ζ) := by
    intro u _
    unfold r2CommForcingMov s53_Dk
    rw [add_sub_cancel]
  have hF2 : ∀ u : ℝ, r ≤ u →
      s104_F2 C s m ρ X α (u, r) ζ = s53_Dk s (ρ r)
        (propagatorW C r (r + (u - r)) (generatorW C (r + (u - r)) (oscTestFun m α))) (X r.toNNReal ζ) := by
    intro u hu
    unfold s104_F2 s53_Dk
    simp only [if_pos hu, add_sub_cancel]
  rw [hFm t (hrt0.trans ht0t), hFm t0 hrt0]
  set Z := X r.toNNReal ζ with hZ
  have hft := s104_stat_ftc ctx hN (T0 := T0 - r) (G0 := fun τ => propagatorW C r (r + τ) (oscTestFun m α))
    (G1 := fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) (oscTestFun m α)))
    (fun τ hτ => horb.cb0 hrT hτ) (fun τ hτ => horb.cb1 hrT hτ) (horb.diff01 r hrT) hc1 Z (τ0 := t0 - r)
    (τ := t - r) (by linarith) (by linarith) (by linarith)
  beta_reduce at hft
  rw [hft]
  have hint : ∫⁻ s' in Ioc t0 t, ENNReal.ofReal |s104_F2 C s m ρ X α (s', r) ζ| =
      ∫⁻ σ in Ioc (t0 - r) (t - r), ENNReal.ofReal |s53_Dk s (ρ r)
        (propagatorW C r (r + σ) (generatorW C (r + σ) (oscTestFun m α))) Z| := by
    rw [s104_lintegral_Ioc_sub (fun σ => ENNReal.ofReal |s53_Dk s (ρ r)
        (propagatorW C r (r + σ) (generatorW C (r + σ) (oscTestFun m α))) Z|) t0 t r]
    refine setLIntegral_congr_fun measurableSet_Ioc fun s' hs' => ?_
    rw [hF2 s' (by linarith [hs'.1])]
  rw [hint]
  calc ENNReal.ofReal |s53_Dk s (ρ r) (propagatorW C r (r + (t0 - r)) (oscTestFun m α)) Z +
        ∫ σ in Ioc (t0 - r) (t - r), s53_Dk s (ρ r)
          (propagatorW C r (r + σ) (generatorW C (r + σ) (oscTestFun m α))) Z|
      ≤ ENNReal.ofReal (|s53_Dk s (ρ r) (propagatorW C r (r + (t0 - r)) (oscTestFun m α)) Z| +
        |∫ σ in Ioc (t0 - r) (t - r), s53_Dk s (ρ r)
          (propagatorW C r (r + σ) (generatorW C (r + σ) (oscTestFun m α))) Z|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ ≤ ENNReal.ofReal |s53_Dk s (ρ r) (propagatorW C r (r + (t0 - r)) (oscTestFun m α)) Z| +
        ENNReal.ofReal |∫ σ in Ioc (t0 - r) (t - r), s53_Dk s (ρ r)
          (propagatorW C r (r + σ) (generatorW C (r + σ) (oscTestFun m α))) Z| := ENNReal.ofReal_add_le
    _ ≤ _ := by
        refine add_le_add le_rfl ?_
        have := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioc (t0 - r) (t - r)))
          (fun σ => s53_Dk s (ρ r) (propagatorW C r (r + σ) (generatorW C (r + σ) (oscTestFun m α))) Z)
        simpa [Real.enorm_eq_ofReal_abs] using this

end HRS.MS.R2WinErr
