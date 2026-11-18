import HRS.MS.FinNoiseAux2
import HRS.Prob.HilbertMartingale

/-!
# S8.6 `finite_noise`, packet P1b (S86): joint measurability of the orbit feature in `(r, x)`

Hypotheses are bundled in `S86Feat C m Hz` (all of them hold for the critical model by S8.5,
`HRS.MS.S85.feature_decay_proof`, `s85_uniq`, `s85_exists_adjoint`).  The result is the Borel
measurability of `(r, x) ↦ gradFeature C m Hz i (max r 0) x ∈ 𝒦_Hz` on `ℝ × ℝ^d`: continuity in `x` (S8.5),
and measurability in `r` for fixed `x` through time homogeneity (`s86_prop_shift`): the `H¹`-component is
the shift `t ↦ 1_{r<t} G(t - r)` of one `L²` profile `G`, whose pairings with `L²` functions are measurable
in `r` by Fubini.  Raw negative times are avoided by the `max r 0` of the repaired statement.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole HRS.MS.S52B

variable {d : ℕ} {m T : ℝ}

theorem s86_inner_mk (b : KSpace d m T) (a₀ : OscDual d m) (a' : L2Path d m T) (c : OscDual d m) :
    inner ℝ b (KSpace.mk a₀ a' c) = inner ℝ b.A₀ a₀ + inner ℝ b.A' a' + inner ℝ b.B c := by
  have : inner ℝ b (KSpace.mk a₀ a' c) = inner ℝ
      (show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from b)
      (WithLp.toLp 2 (a₀, WithLp.toLp 2 (a', c))) := rfl
  rw [this, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  rw [add_assoc]
  rfl

/-- The hypotheses of the measurability of the features (all supplied by S8.5 for the critical model). -/
structure S86Feat (C : WholeCoeff d) (m Hz : ℝ) : Prop where
  gen : ∀ t φ, generatorW C t φ = generatorW C 0 φ
  uniq : S52bUniq C Hz
  ex : ∀ (α : MultiIndex d), ∀ t ∈ Icc (0 : ℝ) Hz,
    ∃ f, IsClassicalAdjointW C t (generatorW C t (oscTestFun m α)) f
  feat : ∀ (i : Fin d), ∀ r ∈ Icc (0 : ℝ) Hz, ∀ x, IsKFeature C m Hz (gradComp i) r x
  cont : ∀ (i : Fin d), ∀ r ∈ Icc (0 : ℝ) Hz, Continuous fun x => gradFeature C m Hz i r x

/-- For `r ≥ Hz` the `H¹` part of the feature vanishes, so the feature is constant in `r`. -/
theorem s86_feat_clamp (C : WholeCoeff d) (m Hz : ℝ) (i : Fin d) (x : Euc d) (r : ℝ)
    (hr : Hz ≤ r) : gradFeature C m Hz i r x = gradFeature C m Hz i Hz x := by
  classical
  have key : ∀ r' : ℝ, Hz ≤ r' → gradFeature C m Hz i r' x =
      KSpace.mk (ellVec m fun α => gradComp i (oscTestFun m α) x) 0
        (ellVec m fun α => gradComp i (oscTestFun m α) x) := by
    intro r' hr'
    unfold gradFeature orbitFeature
    dsimp only
    congr 1
    split_ifs with h
    · refine Lp.ext ?_
      have hf0 : (fun t : ℝ => if r' < t then ellVec (d := d) m (fun α => gradComp i
          (propagatorW C r' t (generatorW C t (oscTestFun m α))) x) else 0)
          =ᵐ[volume.restrict (Icc (0 : ℝ) Hz)] fun _ => 0 := by
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
        refine Filter.Eventually.of_forall fun t ht => ?_
        have : ¬ r' < t := not_lt.2 (ht.2.trans hr')
        simp [this]
      exact h.coeFn_toLp.trans (hf0.trans (Lp.coeFn_zero _ _ _).symm)
    · rfl
  rw [key r hr, key Hz le_rfl]

variable (C : WholeCoeff d) (Hz : ℝ)

/-- The `L²` profile at fixed `x`. -/
def s86_prof (m : ℝ) (i : Fin d) (x : Euc d) (s : ℝ) : OscDual d m :=
  ellVec m fun α => gradComp i (propagatorW C 0 s (generatorW C 0 (oscTestFun m α))) x

theorem s86_orbit_ae (h : S86Feat C m Hz) (i : Fin d) (x : Euc d) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Hz) :
    (fun t : ℝ => if r < t then ellVec (d := d) m (fun α => gradComp i
        (propagatorW C r t (generatorW C t (oscTestFun m α))) x) else 0)
      =ᵐ[volume.restrict (Icc (0 : ℝ) Hz)] fun t => if r < t then s86_prof C m i x (t - r) else 0 := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  by_cases hrt : r < t
  · simp only [hrt, ite_true]
    unfold s86_prof
    congr 1
    funext α
    have hg : generatorW C t (oscTestFun m α) = generatorW C 0 (oscTestFun m α) := h.gen t _
    rw [hg]
    have hex := h.ex α t ht
    rw [hg] at hex
    rw [s86_prop_shift C h.gen Hz h.uniq t ht _ hex r ⟨hr.1, hrt.le⟩]
  · simp [hrt]

end HRS.MS.FinNoise
