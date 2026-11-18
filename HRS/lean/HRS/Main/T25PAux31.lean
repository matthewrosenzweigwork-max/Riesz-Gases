import HRS.Main.T25PAux30
import HRS.Main.T25Aux8

/-!
# T25P, part 31: window laws of re-based linear solutions are `(κ ⊗ γ)`-push-forwards

`t25p_L`: the window of the initial path `x ↦ (s ↦ V^{a+s,0} x)` as a bounded linear map `E_m → 𝒳_{m,T}`.
`t25p_rebase_law`: the window law of the re-based solution `Ȳ_κ` is `(κ ⊗ γ)` pushed forward by `(x, z) ↦ Lx + z`, with
`γ` (the law of the window of `Y - V Y₀`) independent of `κ`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45 HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The window `s ↦ V^{a+s,0} x` as a bounded linear map `E_m → C([0,T]; E_m)`. -/
def t25p_L {m : ℝ} {a T Cr : ℝ} (ha : 0 ≤ a) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ a + T}) (hCr : 0 ≤ Cr)
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Vev t 0‖ ≤ Cr) :
    NegSobolev d m →L[ℝ] PathSp T (NegSobolev d m) :=
  LinearMap.mkContinuous
    { toFun := fun x => (⟨fun s : Set.Icc (0 : ℝ) T => Vev (a + (s : ℝ)) 0 x, by
        have h1 := HRS.Uniform.Comp28.continuousOn_V_zero Vev hc x
        exact h1.comp_continuous (by fun_prop) (fun s => ⟨by linarith [s.2.1], by linarith [s.2.2]⟩)⟩ :
          C(Set.Icc (0 : ℝ) T, NegSobolev d m))
      map_add' := fun x y => pcm_ext fun s => by
        show Vev (a + (s : ℝ)) 0 (x + y) = Vev (a + (s : ℝ)) 0 x + Vev (a + (s : ℝ)) 0 y
        simp
      map_smul' := fun r x => pcm_ext fun s => by
        show Vev (a + (s : ℝ)) 0 (r • x) = r • Vev (a + (s : ℝ)) 0 x
        simp } Cr
    (fun x => by
      refine norm_pcm_le _ (mul_nonneg hCr (norm_nonneg _)) fun s => ?_
      show ‖Vev (a + (s : ℝ)) 0 x‖ ≤ _
      exact ((Vev _ 0).le_opNorm x).trans (mul_le_mul_of_nonneg_right
        (hb _ (by linarith [s.2.1]) (by linarith [s.2.2])) (norm_nonneg _)))

lemma t25p_pcm_L {m : ℝ} {a T Cr : ℝ} (ha : 0 ≤ a) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ a + T}) (hCr : 0 ≤ Cr)
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Vev t 0‖ ≤ Cr) (x : NegSobolev d m) (s : Set.Icc (0 : ℝ) T) :
    pcm (t25p_L ha Vev hc hCr hb x) s = Vev (a + (s : ℝ)) 0 x := rfl

lemma t25p_norm_L_le {m : ℝ} {a T Cr : ℝ} (ha : 0 ≤ a) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ a + T}) (hCr : 0 ≤ Cr)
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Vev t 0‖ ≤ Cr) :
    ‖(t25p_L (T := T) ha Vev hc hCr hb)‖ ≤ Cr :=
  LinearMap.mkContinuous_norm_le _ hCr _

/-- Window of `x`-part plus continuous part. -/
lemma t25p_win_add {m : ℝ} {a T Cr : ℝ} (ha : 0 ≤ a) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ a + T}) (hCr : 0 ≤ Cr)
    (hb : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Vev t 0‖ ≤ Cr) (hT : 0 ≤ T) (x : NegSobolev d m)
    {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) {ω : Ω}
    (hω : ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T))) :
    Uniform.windowPath a T (fun t ω => Vev t 0 x + Z t ω) ω =
      t25p_L ha Vev hc hCr hb x + Uniform.windowPath a T Z ω := by
  have hV := HRS.Uniform.Comp28.continuousOn_V_zero Vev hc x
  have hsum : ContinuousOn (fun t => Vev t 0 x + Z t ω) (Set.Icc 0 (a + T)) := hV.add hω
  refine pcm_ext fun s => ?_
  rw [HRS.Uniform.Comp28.pcm_windowPath_a ha hT _ hsum, pcm_add, t25p_pcm_L,
    HRS.Uniform.Comp28.pcm_windowPath_a ha hT _ hω]

end HRS.T25P
