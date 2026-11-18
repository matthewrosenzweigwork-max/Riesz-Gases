import HRS.Main.GFEVAux18

/-!
# Packet GFEVG, part 19: the abstract data `GFAbs` for the concrete evolution
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfev_embed_sub {m m' : ℝ} (hmm' : m ≤ m') (F G : NegSobolev d m) :
    NegSobolev.embed m' (F - G) = NegSobolev.embed m' F - NegSobolev.embed m' G := by
  have h := gfev_embed_add hmm' F (-G)
  have h2 : NegSobolev.embed m' (-G) = -NegSobolev.embed m' G := by
    have := gfev_embed_smul hmm' (-1) G
    simpa using this
  rw [sub_eq_add_neg, h, h2, sub_eq_add_neg]

/-- continuity into `E_{γ-2}` from continuity into `E_γ` and boundedness in `E_{γ-4}` -/
theorem gfev_cont_interp {γ : ℕ} {X : Type*} [TopologicalSpace X] {S : Set X} {x₀ : X}
    (y : X → NegSobolev d ((γ : ℝ) - 4)) (Bd : ℝ) (hb : ∀ x ∈ S, ‖y x‖ ≤ Bd)
    (hc : ContinuousWithinAt (fun x => NegSobolev.embed (γ : ℝ) (y x)) S x₀) (hx₀ : x₀ ∈ S) :
    ContinuousWithinAt (fun x => NegSobolev.embed ((γ : ℝ) - 2) (y x)) S x₀ := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at hc
  have hBd : 0 ≤ Bd := (norm_nonneg _).trans (hb x₀ hx₀)
  have h1 : Tendsto (fun x => 2 * Bd * ‖NegSobolev.embed (γ : ℝ) (y x) - NegSobolev.embed (γ : ℝ) (y x₀)‖)
      (𝓝[S] x₀) (𝓝 0) := by simpa using hc.const_mul (2 * Bd)
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
  simp only [Real.sqrt_zero] at h2
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ h2
  filter_upwards [self_mem_nhdsWithin] with x hx
  have e1 : NegSobolev.embed ((γ : ℝ) - 2) (y x) - NegSobolev.embed ((γ : ℝ) - 2) (y x₀) =
      NegSobolev.embed ((γ : ℝ) - 2) (y x - y x₀) := (gfev_embed_sub (gfev_le42 γ) _ _).symm
  have e2 : NegSobolev.embed (γ : ℝ) (y x) - NegSobolev.embed (γ : ℝ) (y x₀) =
      NegSobolev.embed (γ : ℝ) (y x - y x₀) := (gfev_embed_sub (gfev_le4 γ) _ _).symm
  have hI := gfev_interp (a := (γ : ℝ) - 4) (b := (γ : ℝ) - 2) (c := γ) (by ring) (gfev_le4 γ) (y x - y x₀)
  simp only [Function.comp]
  rw [e1, e2]
  have hn : ‖y x - y x₀‖ ≤ 2 * Bd := by
    calc ‖y x - y x₀‖ ≤ ‖y x‖ + ‖y x₀‖ := norm_sub_le _ _
      _ ≤ 2 * Bd := by linarith [hb x hx, hb x₀ hx₀]
  have hs : 0 ≤ 2 * Bd * ‖NegSobolev.embed (γ : ℝ) (y x - y x₀)‖ :=
    mul_nonneg (by positivity) (norm_nonneg _)
  refine Real.le_sqrt_of_sq_le ?_
  calc ‖NegSobolev.embed ((γ : ℝ) - 2) (y x - y x₀)‖ ^ 2
      ≤ ‖y x - y x₀‖ * ‖NegSobolev.embed (γ : ℝ) (y x - y x₀)‖ := hI
    _ ≤ 2 * Bd * ‖NegSobolev.embed (γ : ℝ) (y x - y x₀)‖ :=
        mul_le_mul_of_nonneg_right hn (norm_nonneg _)

end HRS.GF
