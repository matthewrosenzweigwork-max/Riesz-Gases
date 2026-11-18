import HRS.MS.R26T8AB07b3
import HRS.MS.R26T8AD01
import HRS.MS.R26T8AO03a

/-!
# S8.2 observed-time layer, packet T8A.B07b: actual recent and old scalar blocks have continuous paths

Along a canonical path (continuous, collision-free up to the horizon `a0 + T`) the centered integrand is
`Ψ (b - r) (X_r)` with `Ψ v y = scalarForcing (projectedOrbit v φ_α) y` (B07c pointwise, orbit shift, constants do not
change the gradient).  B07b2 gives domination by `B * env` and continuity in the age `v`, B07b3 gives the dominated
convergence with moving endpoint and the continuity of `env` along the collision-free compact path.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b07b_sf_const {d N : ℕ} (a beta : ℝ) (rho : Euc d → ℝ) (f : Euc d → ℝ) (k : ℝ) :
    (scalarForcing (d := d) (N := N) a beta rho (fun x => f x - k)) =
      scalarForcing (d := d) (N := N) a beta rho f := by
  have hg : gradient (fun x => f x - k) = gradient f := by
    funext z; unfold gradient; rw [fderiv_sub_const]
  have h : hSource (fun x => f x - k) = hSource f := by unfold hSource; rw [hg]
  unfold scalarForcing
  rw [h]

theorem r26t8a_actual_block_continuity (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (T a0 : ℝ) (hT : 0<T) (ha0 : 0≤a0) :
    ∀ᵐ w ∂P, ∀ alpha : MultiIndex d,
      ContinuousOn (fun t => HRS.MS.S82BD.s82Recent (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 t alpha w)
        (Set.Icc 0 T) ∧
      ∀ j : ℕ, ContinuousOn (fun t => HRS.MS.S82BD.s82Past (HRS.MS.S82BD.s82Centered d N a beta m rho P X) a0 j t alpha w)
        (Set.Icc 0 T) := by
  classical
  obtain ⟨C0, hC0, hCb⟩ := r26t8a_b07a1_int_bound' d hd a beta ha hbeta
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := (hCb rho hrho).1
  obtain ⟨c0, K, hc0, hK, hm, henv1, hL2, hE⟩ := r26t8a_b07a_explicit d N hd hN a beta ha hbeta rho hrho
  filter_upwards [(hX.solution (a0 + T)).cont, (hX.solution (a0 + T)).no_collision] with w hw hnc
  intro alpha
  obtain ⟨hdom, hcont⟩ := r26t8a_b07b2_orbit d N hd hN a beta m Cf c ha hbeta rho hrho horb alpha
  obtain ⟨B, hB0, hB⟩ := hdom (a0 + T) (by linarith)
  set x : ℝ → EucConfig d N := fun r => X r.toNNReal w with hxdef
  have hx : Continuous x := (continuous_pi hw).comp continuous_real_toNNReal
  have hclosed : IsClosed (eucCollisionSet d N) := by
    have : eucCollisionSet d N = ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {X : EucConfig d N | X i = X j} := by
      ext X; simp [eucCollisionSet]
    rw [this]
    exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
      isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)
  have hxU : ∀ r ∈ Set.Icc (0 : ℝ) (a0 + T), x r ∈ (eucCollisionSet d N)ᶜ := fun r hr => by
    show X r.toNNReal w ∉ eucCollisionSet d N
    refine hnc _ ?_
    rw [Real.coe_toNNReal _ hr.1]; exact hr.2
  set Ψ : ℝ → EucConfig d N → ℝ := fun v y => scalarForcing a beta rho
    (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v
      (oscTestFun m alpha)) y with hΨ
  have hΨeq : ∀ b r : ℝ, 0 ≤ r → r ≤ b →
      HRS.MS.S82BD.s82Centered d N a beta m rho P X alpha b r w = Ψ (b - r) (x r) := by
    intro b r hr hrb
    rw [r26t8a_b07c_pointwise d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X
      hX alpha b r hr hrb w, horb.shift alpha r b hr hrb]
    have := congrFun (r26t8a_b07b_sf_const (N := N) a beta rho
      (propagatorW (critCoeff d a beta rho) 0 (b - r) (oscTestFun m alpha))
      (HRS.Whole.pair (HRS.Whole.withDensityReal rho)
        (propagatorW (critCoeff d a beta rho) 0 (b - r) (oscTestFun m alpha)))) (x r)
    exact this.symm
  have hcore : ∀ (lo : ℝ) (hi : ℝ → ℝ), 0 ≤ lo → Continuous hi →
      (∀ t ∈ Set.Icc (0 : ℝ) T, hi t ≤ a0 + t) →
      ContinuousOn (fun t => ∫ r in Set.Icc lo (hi t), Ψ (a0 + t - r) (x r)) (Set.Icc 0 T) :=
    fun lo hi hlo hhi hhiH => r26t8a_b07b3_core x hx (eucCollisionSet d N)ᶜ hclosed.measurableSet.compl
      (a0 + T) hxU (r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d))
      (r26t8a_b07b3_env_cont d N _) (fun y _ => by linarith [henv1 y]) Ψ
      (fun v => r26t8a_b07b2_meas d N a beta rho _) (fun y hy v0 hv0 => hcont y hy v0 hv0)
      B hB0 hB T a0 lo hT.le ha0 rfl hlo hi hhi hhiH
  refine ⟨?_, fun j => ?_⟩
  · refine (hcore a0 (fun t => a0 + t) ha0 (continuous_const.add continuous_id)
      (fun t _ => le_rfl)).congr fun t ht => ?_
    show ∫ r in Set.Icc a0 (a0 + t), HRS.MS.S82BD.s82Centered d N a beta m rho P X alpha (a0 + t) r w = _
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    exact (hΨeq (a0 + t) r (ha0.trans hr.1) hr.2)
  · refine (hcore (max 0 (a0 - ((j : ℝ) + 1))) (fun _ => max 0 (a0 - (j : ℝ))) (le_max_left _ _)
      continuous_const (fun t ht => ?_)).congr fun t ht => ?_
    · exact max_le (by linarith [ht.1]) (by linarith [ht.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
    · show ∫ r in Set.Icc (max 0 (a0 - ((j : ℝ) + 1))) (max 0 (a0 - (j : ℝ))),
        HRS.MS.S82BD.s82Centered d N a beta m rho P X alpha (a0 + t) r w = _
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      exact hΨeq (a0 + t) r ((le_max_left _ _).trans hr.1)
        (hr.2.trans (max_le (by linarith [ht.1]) (by linarith [ht.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)])))

end HRS.MS.R26T8A
