import HRS.MC.CepN5Aux2
import HRS.MC.CepN5Aux4

/-!
# Packet N5, helper 5: the shifted gap process `H`, the drift remainder `Z`, and its density process

`H s = G (t₁ + max s 0)` is continuous and adapted to the shifted filtration `n5_shF ℱ t₁`;
`Z s = H s - H 0 - σ (B (t₁ + s) - B t₁)` (so `Z = ∫ β` on the good region) is continuous adapted and vanishes
for `s ≤ 0`.  The clipped backward-difference-quotient limit of `Z` is a progressive process.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The shifted gap process. -/
def n5_H (G : ℝ → Ω → ℝ) (t₁ : ℝ≥0) (s : ℝ) (ω : Ω) : ℝ := G ((t₁ : ℝ) + max s 0) ω

/-- The shifted remainder `H - H₀ - σ ΔB`. -/
def n5_Zp (G : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (t₁ : ℝ≥0) (σ : ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  n5_H G t₁ s ω - n5_H G t₁ 0 ω - σ * (B (t₁ + s.toNNReal) ω - B t₁ ω)

theorem n5_H_cont {G : ℝ → Ω → ℝ} (hG : ∀ ω, Continuous fun t => G t ω) (t₁ : ℝ≥0) (ω : Ω) :
    Continuous fun s => n5_H G t₁ s ω :=
  (hG ω).comp (continuous_const.add (continuous_id.max continuous_const))

theorem n5_H_adapted {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → ℝ}
    (hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t)) (t₁ : ℝ≥0) (s : ℝ) :
    Measurable[n5_shF ℱ (t₁ : ℝ) s] (n5_H G t₁ s) :=
  hGad _ (add_nonneg t₁.2 (le_max_right _ _))

theorem n5_H_zero (G : ℝ → Ω → ℝ) (t₁ : ℝ≥0) (ω : Ω) : n5_H G t₁ 0 ω = G t₁ ω := by
  simp [n5_H]

theorem n5_Zp_neg (G : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (t₁ : ℝ≥0) (σ : ℝ) {s : ℝ} (hs : s ≤ 0) (ω : Ω) :
    n5_Zp G B t₁ σ s ω = 0 := by
  have h1 : max s 0 = 0 := max_eq_right hs
  have h2 : s.toNNReal = 0 := Real.toNNReal_of_nonpos hs
  simp [n5_Zp, n5_H, h1, h2]

theorem n5_Zp_cont {G : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} (hG : ∀ ω, Continuous fun t => G t ω)
    (hBc : ∀ ω, Continuous fun t => B t ω) (t₁ : ℝ≥0) (σ : ℝ) (ω : Ω) :
    Continuous fun s => n5_Zp G B t₁ σ s ω := by
  unfold n5_Zp
  refine ((n5_H_cont hG t₁ ω).sub continuous_const).sub (continuous_const.mul ?_)
  exact ((hBc ω).comp (continuous_const.add continuous_real_toNNReal)).sub continuous_const

theorem n5_Zp_adapted {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t)) (hBad : ∀ t : ℝ≥0, Measurable[ℱ t] (B t))
    (t₁ : ℝ≥0) (σ : ℝ) (s : ℝ) : Measurable[n5_shF ℱ (t₁ : ℝ) s] (n5_Zp G B t₁ σ s) := by
  have hmono : ∀ {a b : ℝ}, a ≤ b → ℱ a ≤ ℱ b := fun h => ℱ.mono h
  have hs : (t₁ : ℝ) ≤ (t₁ : ℝ) + max s 0 := le_add_of_nonneg_right (le_max_right _ _)
  have h1 : Measurable[n5_shF ℱ (t₁ : ℝ) s] (n5_H G t₁ s) := n5_H_adapted hGad t₁ s
  have h2 : Measurable[n5_shF ℱ (t₁ : ℝ) s] (n5_H G t₁ 0) :=
    (n5_H_adapted hGad t₁ 0).mono (ℱ.mono (by simp [n5_shF_apply])) le_rfl
  have h3 : Measurable[n5_shF ℱ (t₁ : ℝ) s] (fun ω => B (t₁ + s.toNNReal) ω) := by
    refine (hBad _).mono ?_ le_rfl
    rw [n5_shF_apply]
    refine ℱ.mono ?_
    have : ((t₁ + s.toNNReal : ℝ≥0) : ℝ) = (t₁ : ℝ) + max s 0 := by
      push_cast; rw [Real.coe_toNNReal']
    rw [this]
  have h4 : Measurable[n5_shF ℱ (t₁ : ℝ) s] (fun ω => B t₁ ω) :=
    (hBad t₁).mono (ℱ.mono hs) le_rfl
  exact (h1.sub h2).sub ((h3.sub h4).const_mul σ)

/-- The clipped difference-quotient limit of a progressive process is progressive. -/
theorem n5_isProgressive_bcl {ℱ : Filtration ℝ mΩ} {Zp : ℝ → Ω → ℝ} (hZ : IsProgressive ℱ Zp) (M₀ : ℝ) :
    IsProgressive ℱ (fun s ω => n5_bcl M₀ (n5_dq (fun u => Zp u ω) s)) := by
  intro i
  have hd : ∀ n : ℕ, Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
      fun p : Set.Iic i × Ω => ((n : ℝ) + 1) * (Zp p.1 p.2 - Zp (p.1 - 1 / ((n : ℝ) + 1)) p.2) := by
    intro n
    have hT : IsProgressive ℱ (fun (s : ℝ) (_ : Ω) => s - 1 / ((n : ℝ) + 1)) := fun j =>
      (measurable_subtype_coe.comp measurable_fst).sub_const _
    have hc : IsProgressive ℱ (fun (s : ℝ) (ω : Ω) => Zp (s - 1 / ((n : ℝ) + 1)) ω) :=
      hZ.comp hT (fun s _ => by have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
                                linarith)
    exact (measurable_const.mul ((hZ i).sub (hc i)))
  have hl := Measurable.limsup hd
  have : (fun p : Set.Iic i × Ω => n5_bcl M₀ (n5_dq (fun u => Zp u p.2) p.1)) =
      fun p => max 0 (min (limsup (fun n : ℕ => ((n : ℝ) + 1) *
        (Zp p.1 p.2 - Zp (p.1 - 1 / ((n : ℝ) + 1)) p.2)) atTop) M₀) := rfl
  show Measurable[Subtype.instMeasurableSpace.prod (ℱ i)] fun p : Set.Iic i × Ω =>
    n5_bcl M₀ (n5_dq (fun u => Zp u p.2) p.1)
  rw [this]
  exact measurable_const.max (hl.min measurable_const)

end HRS.MC.CepN5
