import HRS.MS.R26T8AO05b1
import HRS.MS.R26T8AO05b2

/-!
# S8.2 observed-time layer, packet T8A.O05b: extend a local `C^{1,2}` test by collision and spatial cutoffs

Packet statement `r26t8a_c12_cutoffs`.  The cutoffs `fn n t X = θ_n X * f t X` with the graph cutoffs `θ_n` of `G01`
are `C^{1,2}` on all of configuration space (`O05b1`), and on a compact collision-free set `K` they agree with `f`
together with their first and second spatial derivatives and their time derivative, for all large `n` (`O05b2`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_c12_cutoffs (d N : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → EucConfig d N → ℝ) (hf : IsC12On T (eucCollisionSet d N)ᶜ f) :
    ∃ fn : ℕ → ℝ → EucConfig d N → ℝ,
      (∀ n, IsC12On T Set.univ (fn n)) ∧
      ∀ K : Set (EucConfig d N), IsCompact K → K ⊆ (eucCollisionSet d N)ᶜ →
        ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc 0 T, ∀ X ∈ K,
          fn n t X = f t X ∧ fderiv ℝ (fn n t) X = fderiv ℝ (f t) X ∧
          fderiv ℝ (fderiv ℝ (fn n t)) X = fderiv ℝ (fderiv ℝ (f t)) X ∧
          derivWithin (fun r => fn n r X) (Set.Icc 0 T) t =
            derivWithin (fun r => f r X) (Set.Icc 0 T) t := by
  refine ⟨fun n t X => r26t8a_g01_theta d N n X * f t X, fun n => ?_, fun K hK hKD => ?_⟩
  · exact r26t8a_o05b_c12_mul T (eucCollisionSet d N)ᶜ (r26t8a_o05b2_coll_closed d N).isOpen_compl
      (r26t8a_g01_theta d N n) (r26t8a_g01_theta_contDiff d N n) (r26t8a_g01_theta_tsupport d N n) f hf
  · filter_upwards [r26t8a_o05b2_eventually d N K hK hKD] with n hn
    intro t _ X hX
    have h1 : r26t8a_g01_theta d N n X = 1 := (hn X hX).eq_of_nhds
    have hfe : (fun Y => r26t8a_g01_theta d N n Y * f t Y) =ᶠ[𝓝 X] f t := by
      filter_upwards [hn X hX] with Y hY
      simp [hY]
    refine ⟨by simp [h1], hfe.fderiv_eq, hfe.fderiv.fderiv_eq, ?_⟩
    simp only [h1, one_mul]

end HRS.MS.R26T8A

end
