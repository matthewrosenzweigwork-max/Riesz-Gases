import HRS.MC.E214K1
import HRS.Sections.Q40bAux2
import HRS.Main.T25Aux1

/-!
# Packet E214K, part 2: the operator comparison `V - V̄` on `E_j` for even `j` (duality from `adjoint_decay_comparison`)

`compare_level`: for every even `j > d/2 + 4`, every pair of dual evolutions `VR` (along the prepared trajectory `S.ρ`)
and `Wc` (along the constant thermal density `ρβ`) on `E_j` satisfies
`‖VR t u - Wc t u‖ ≤ C e^{-c(t-u)} e^{-κu}` on `E_j → E_j`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214K

open HRS HRS.PDE HRS.Uniform HRS.Uniform.Q48b

variable {d : ℕ}

/-- `projMean` is idempotent for a probability measure. -/
theorem projMean_idem' (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (f : Torus d → ℝ) :
    projMean μ (projMean μ f) = projMean μ f := by
  funext x
  have := PDE.MFSemigroup.pair_projMean μ f
  simp only [projMean] at this ⊢
  rw [this, sub_zero]

/-- `eval` does not see the `μ`-mean of the test function. -/
theorem eval_projMean' {m : ℝ} (μ : Measure (Torus d)) (F : NegSobolev d m) {g : Torus d → ℝ}
    (hg : MemLp (projMean μ g) 2 volume) :
    NegSobolev.eval F (projMean μ g) = NegSobolev.eval F g := by
  unfold NegSobolev.eval
  exact tsum_congr fun k => by rw [← q48b_funRealCoeff_projMean μ hg k]

theorem isSmooth_projMean' (μ : Measure (Torus d)) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Torus.IsSmooth (projMean μ f) :=
  HRS.Uniform.Q54.isSmooth_sub' hf (HRS.Uniform.Q54.isSmooth_const' _)

theorem exists_dual (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (hth : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (a : ℝ) :
    ∃ VR Wc : ℝ → ℝ → NegSobolev d a →L[ℝ] NegSobolev d a,
      IsDualEvolution S.dyn S.ρ a VR ∧ IsDualEvolution S.dyn (fun _ => ρβ) a Wc := by
  obtain ⟨-, -, -, -, VR, hVR, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd (HRS.MC.E213A.isSmoothPositiveTrajectory_of_prepared S) a
  obtain ⟨-, -, -, -, Wc, hWc, -⟩ := HRS.ThermLin.thermlin_stationary_evolution S hth a
  exact ⟨VR, Wc, hVR, hWc⟩

/-- **Operator comparison on `E_j`, `j` even.** -/
theorem compare_level (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (hth : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (j : ℕ) (hj : Even j)
    (hjd : (d : ℝ) / 2 + 4 < j) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t →
      ∀ VR Wc : ℝ → ℝ → NegSobolev d (j : ℝ) →L[ℝ] NegSobolev d (j : ℝ),
        IsDualEvolution S.dyn S.ρ (j : ℝ) VR → IsDualEvolution S.dyn (fun _ => ρβ) (j : ℝ) Wc →
        ‖VR t u - Wc t u‖ ≤ C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) := by
  obtain ⟨hsm, hpos⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S hth
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hprob : IsProbDensity ρβ := hth.1
  haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) :=
    HRS.PDE.MFSemigroup.isProb_withDensityReal hprob
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set K : ℕ := 2 * j + 4 * d + 20 with hKdef
  have hK6 : (d : ℝ) / 2 + 6 < K := by
    have : (K : ℝ) = 2 * j + 4 * d + 20 := by rw [hKdef]; push_cast; ring
    rw [this]; linarith
  have H := HRS.Q40b.q40b_finiteRegHyp (HRS.T25.t25_traj S) hK6
  obtain ⟨Cp, cp, κp, hCp, hcp, hκp, hcmp⟩ :=
    adjoint_decay_comparison hd1 S.s S.β S.β K S.V S.ρ0 H j hj hjd le_rfl
  obtain ⟨ρc, hρc, hρ⟩ := S.hρ K hK6
  obtain ⟨Kp, hKp0, hKp⟩ := q48b_proj_test_bound ρβ hprob (j : ℝ) (by linarith)
  obtain ⟨Cf, cf, hCf, hcf, hfro⟩ :=
    q48b_prop52 hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hth hsm hpos j hj hjd
  refine ⟨Cp * (Kp + 1), cp, κp, by positivity, hcp, hκp, fun u t hu hut VR Wc hVR hWc => ?_⟩
  set μ := withDensityReal ρβ with hμdef
  set Cdec : ℝ := Cp * Real.exp (-cp * (t - u)) * Real.exp (-κp * u) with hCdec
  have hCdec0 : 0 ≤ Cdec := by positivity
  -- the dual-side coefficient sequence
  set χ : Finset (NonzeroLattice d) → (NonzeroLattice d → ℝ) → NonzeroLattice d → ℝ := fun T c k =>
    Torus.funRealCoeff (propagator S.dyn S.ρ u t (projMean μ (q48bTest T c))) k -
      Torus.funRealCoeff (propagator S.dyn (fun _ => ρβ) u t (projMean μ (q48bTest T c))) k with hχ
  have hMop : ‖VR t u - Wc t u‖ ≤ Cdec * Kp := by
    refine q48b_opNorm_le (VR t u - Wc t u) (Cdec * Kp) (mul_nonneg hCdec0 hKp0) ?_
    refine wbound_of_duality2 (a := (j : ℝ)) (VR t u - Wc t u) χ ?_ (Cdec * Kp)
      (mul_nonneg hCdec0 hKp0) ?_
    · -- duality
      intro S' T ζ c
      set z := q48bFin (j : ℝ) S' ζ with hz
      have hφs : Torus.IsSmooth (q48bTest T c) := q48bTest_smooth T c
      have hφ's : Torus.IsSmooth (projMean μ (q48bTest T c)) := isSmooth_projMean' μ hφs
      have hmemL : MemLp (projMean μ (q48bTest T c)) 2 volume :=
        (PDE.MFSemigroup.memSobolev_of_isSmooth hφ's (j : ℝ)).1
      have hsub : NegSobolev.eval ((VR t u - Wc t u) z) (q48bTest T c) =
          NegSobolev.eval (VR t u z) (q48bTest T c) - NegSobolev.eval (Wc t u z) (q48bTest T c) := by
        rw [sub_apply]
        exact HRS.Main.A9.a9_eval_sub _ _ (HRS.A33.a33_ws_of_memSobolev (q48bTest_memSobolev T c (j : ℝ)))
      rw [hsub, ← eval_projMean' μ (VR t u z) hmemL, ← eval_projMean' μ (Wc t u z) hmemL,
        hVR u t hu hut z _ hφ's, hWc u t hu hut z _ hφ's, hz, q48b_eval_fin, q48b_eval_fin,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hχ]; ring
    · -- decay
      intro S' T c
      set φ' := projMean μ (q48bTest T c) with hφ'
      have hφ's : Torus.IsSmooth φ' := isSmooth_projMean' μ (q48bTest_smooth T c)
      have hφ'c : Continuous φ' := q48b_continuous_of_isSmooth hφ's
      have hφ'm : MemSobolev (j : ℝ) φ' := PDE.MFSemigroup.memSobolev_of_isSmooth hφ's (j : ℝ)
      -- comparison of Proposition 5.2 at `φ'`
      have hc3 := hcmp S.β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ hth (q48b_continuous_of_isSmooth hsm) hpos φ' hφ'c hφ'm
        u t hu hut
      rw [hρ] at hc3
      obtain ⟨hP1raw, -, hP3raw⟩ := hc3
      have hP1 : MemSobolev (j : ℝ) (projMean μ (propagator S.dyn S.ρ u t φ')) := hP1raw
      have hP3 : sobolevNorm (j : ℝ) (fun x => projMean μ (propagator S.dyn S.ρ u t φ') x -
            equilibriumSemigroup S.dyn ρβ (t - u) (projMean μ φ') x) ≤
          Cp * Real.exp (-cp * (t - u)) * Real.exp (-κp * u) * sobolevNorm (j : ℝ) (projMean μ φ') := hP3raw
      have hP2 : MemSobolev (j : ℝ) (projMean μ (propagator S.dyn (fun _ => ρβ) u t φ')) :=
        (hfro φ' hφ'c hφ'm u t hu hut).1
      set P1 := projMean μ (propagator S.dyn S.ρ u t φ') with hP1def
      set P2 := projMean μ (propagator S.dyn (fun _ => ρβ) u t φ') with hP2def
      have hidem : projMean μ φ' = φ' := projMean_idem' μ _
      have heq : (fun x => projMean μ (propagator S.dyn S.ρ u t φ') x -
            equilibriumSemigroup S.dyn ρβ (t - u) (projMean μ φ') x) = fun x => P1 x - P2 x := by
        funext x
        simp only [equilibriumSemigroup, hidem, hP1def, hP2def]
        rw [← frozen_shift S hth hφ's hu hut]
      have hP3' : sobolevNorm (j : ℝ) (fun x => P1 x - P2 x) ≤
          Cp * Real.exp (-cp * (t - u)) * Real.exp (-κp * u) * sobolevNorm (j : ℝ) φ' := by
        have := hP3
        rw [heq, hidem] at this
        exact this
      -- the coefficients of `P1 - P2`
      have hcoef : ∀ k, χ T c k = Torus.funRealCoeff P1 k - Torus.funRealCoeff P2 k := by
        intro k
        simp only [hχ]
        rw [q48b_funRealCoeff_projMean μ hP1.1 k, q48b_funRealCoeff_projMean μ hP2.1 k]
      have hsubc : ∀ k, Torus.funRealCoeff (fun x => P1 x - P2 x) k = χ T c k := by
        intro k
        rw [HRS.Uniform.Q54.funRealCoeff_sub' hP1.1 hP2.1 k, hcoef k]
      -- summability
      have hsum : Summable fun k : NonzeroLattice d =>
          Lattice.jp k.1 ^ (2 * (j : ℝ)) * Torus.funRealCoeff (fun x => P1 x - P2 x) k ^ 2 := by
        have hb : Summable fun k : NonzeroLattice d =>
            2 * (Lattice.jp k.1 ^ (2 * (j : ℝ)) * Torus.funRealCoeff P1 k ^ 2) +
              2 * (Lattice.jp k.1 ^ (2 * (j : ℝ)) * Torus.funRealCoeff P2 k ^ 2) :=
          (hP1.2.mul_left 2).add (hP2.2.mul_left 2)
        refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
          (sq_nonneg _)) (fun k => ?_) hb
        rw [hsubc k, hcoef k]
        have hw := Real.rpow_nonneg (Torus.jp_pos k.1).le (2 * (j : ℝ))
        nlinarith [mul_nonneg hw (sq_nonneg (Torus.funRealCoeff P1 k + Torus.funRealCoeff P2 k))]
      have hle : ∑ k ∈ S', q48bW k ^ (2 * (j : ℝ)) * χ T c k ^ 2 ≤
          sobolevNorm (j : ℝ) (fun x => P1 x - P2 x) ^ 2 := by
        have h1 : ∑ k ∈ S', q48bW k ^ (2 * (j : ℝ)) * χ T c k ^ 2 ≤
            ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * (j : ℝ)) *
              Torus.funRealCoeff (fun x => P1 x - P2 x) k ^ 2 := by
          have := Summable.sum_le_tsum S' (fun k _ => mul_nonneg
            (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)) hsum
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) this
          rw [hsubc k]; rfl
        have hpos2 : 0 ≤ Torus.mean (fun x => P1 x - P2 x) ^ 2 + ∑' k : NonzeroLattice d,
            Lattice.jp k.1 ^ (2 * (j : ℝ)) * Torus.funRealCoeff (fun x => P1 x - P2 x) k ^ 2 :=
          add_nonneg (sq_nonneg _) (tsum_nonneg fun k => mul_nonneg
            (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
        unfold sobolevNorm
        rw [Real.sq_sqrt hpos2]
        exact h1.trans (le_add_of_nonneg_left (sq_nonneg _))
      have hnorm0 : 0 ≤ sobolevNorm (j : ℝ) (fun x => P1 x - P2 x) := Real.sqrt_nonneg _
      have hKb := hKp T c
      have hN0 : 0 ≤ ∑ l ∈ T, q48bW l ^ (2 * (j : ℝ)) * c l ^ 2 :=
        Finset.sum_nonneg fun l _ => mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
      have hb2 : sobolevNorm (j : ℝ) (fun x => P1 x - P2 x) ≤
          Cdec * (Kp * Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * (j : ℝ)) * c l ^ 2)) :=
        hP3'.trans (mul_le_mul_of_nonneg_left hKb hCdec0)
      calc ∑ k ∈ S', q48bW k ^ (2 * (j : ℝ)) * χ T c k ^ 2
          ≤ sobolevNorm (j : ℝ) (fun x => P1 x - P2 x) ^ 2 := hle
        _ ≤ (Cdec * (Kp * Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * (j : ℝ)) * c l ^ 2))) ^ 2 :=
            pow_le_pow_left₀ hnorm0 hb2 2
        _ = (Cdec * Kp) ^ 2 * ∑ l ∈ T, q48bW l ^ (2 * (j : ℝ)) * c l ^ 2 := by
            rw [show Cdec * (Kp * Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * (j : ℝ)) * c l ^ 2)) =
              (Cdec * Kp) * Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * (j : ℝ)) * c l ^ 2) by ring, mul_pow,
              Real.sq_sqrt hN0]
  refine hMop.trans ?_
  have : Cdec * Kp ≤ Cp * (Kp + 1) * Real.exp (-cp * (t - u)) * Real.exp (-κp * u) := by
    simp only [hCdec]
    have h1 : 0 ≤ Cp * Real.exp (-cp * (t - u)) * Real.exp (-κp * u) := by positivity
    nlinarith [mul_nonneg h1 hKp0]
  exact this

/-- `compare_level` at a real level `a` that is an even integer `j`. -/
theorem compare_level_at (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (hth : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (a : ℝ) (j : ℕ) (hj : Even j)
    (hjd : (d : ℝ) / 2 + 4 < j) (ha : a = (j : ℝ)) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t →
      ∀ VR Wc : ℝ → ℝ → NegSobolev d a →L[ℝ] NegSobolev d a,
        IsDualEvolution S.dyn S.ρ a VR → IsDualEvolution S.dyn (fun _ => ρβ) a Wc →
        ‖VR t u - Wc t u‖ ≤ C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) := by
  subst ha
  exact compare_level S hth j hj hjd

/-- Vprop at a higher level on an embedded vector is the embedding of the dual evolution. -/
theorem vprop_embed {a m : ℝ} (hma : a ≤ m) (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (Vev : ℝ → ℝ → NegSobolev d a →L[ℝ] NegSobolev d a) (hdual : IsDualEvolution D ρ a Vev)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (F : NegSobolev d a) :
    HRS.Sec7.Vprop D ρ m t u (NegSobolev.embed m F) = NegSobolev.embed m (Vev t u F) := by
  unfold HRS.Sec7.Vprop
  show NegSobolev.ofSeq m _ = NegSobolev.ofSeq m _
  congr 1
  funext k
  rw [HRS.MD.EQGaussLift.eqgl_eval_embed hma F, ← hdual u t hu hut F _ (q48b_isSmooth_realMode k),
    q38b_eval_realMode]

end HRS.MC.E214K

end
