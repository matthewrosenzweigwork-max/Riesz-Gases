import HRS.Uniform.Q12P2
import HRS.Uniform.Q12W5

/-!
# Q12, Peyre part 3: weak functionals, torus maps from lifts, weak closeness
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- `∫ Φ(rep x) dμ(x)` for a periodic function `Φ` on `ℝ^d`. -/
def Iw (μ : Measure (Torus d)) (Φ : Euc d → ℝ) : ℝ := ∫ x, Φ (Torus.rep x) ∂μ

/-- `ν` and `μ` are `b`-close against `C²_b` test functions. -/
def WeakClose (ν μ : Measure (Torus d)) (b : ℝ) : Prop :=
  ∀ (Φ : Euc d → ℝ) (B : ℝ), Torus.Per Φ → C2b B Φ → |Iw ν Φ - Iw μ Φ| ≤ b * B

/-- The map of the torus induced by a map `T` of `ℝ^d` commuting with integer translations. -/
def torusMap (T : Euc d → Euc d) (x : Torus d) : Torus d := Torus.mk (T (Torus.rep x))

def PerEquiv (T : Euc d → Euc d) : Prop :=
  ∀ (y : Euc d) (n : Lattice d), T (y + Lattice.toEuc n) = T y + Lattice.toEuc n

lemma q12_torusMap_mk {T : Euc d → Euc d} (hT : PerEquiv T) (y : Euc d) :
    torusMap T (Torus.mk y) = Torus.mk (T y) := by
  obtain ⟨n, hn⟩ := Torus.rep_mk y
  unfold torusMap
  rw [hn, hT, Torus.mk_add, Torus.mk_toEuc, add_zero]

lemma q12_perEquiv_per_comp {T : Euc d → Euc d} (hT : PerEquiv T) {Φ : Euc d → ℝ} (hΦ : Torus.Per Φ) :
    Torus.Per (fun y => Φ (T y)) := by
  intro y n
  show Φ (T (y + Lattice.toEuc n)) = Φ (T y)
  rw [hT]; exact hΦ _ _

lemma q12_continuous_torusMap {T : Euc d → Euc d} (hT : PerEquiv T) (hc : Continuous T) :
    Continuous (torusMap T) := by
  have hper : Torus.Per (fun y => Torus.mk (T y)) := by
    intro y n
    show Torus.mk (T (y + Lattice.toEuc n)) = Torus.mk (T y)
    rw [hT, Torus.mk_add, Torus.mk_toEuc, add_zero]
  have := Torus.continuous_descend hper (Torus.continuous_mk.comp hc)
  exact this

lemma q12_Iw_map {T : Euc d → Euc d} (hT : PerEquiv T) (hc : Continuous T) (μ : Measure (Torus d))
    {Φ : Euc d → ℝ} (hΦ : Torus.Per Φ) (hΦc : Continuous Φ) :
    Iw (μ.map (torusMap T)) Φ = Iw μ (fun y => Φ (T y)) := by
  have hdc : Continuous (Torus.descend Φ) := Torus.continuous_descend hΦ hΦc
  have hm := q12_continuous_torusMap hT hc
  unfold Iw
  have e : (fun x => Φ (Torus.rep x)) = Torus.descend Φ := rfl
  rw [e, integral_map hm.measurable.aemeasurable hdc.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Torus.descend Φ (torusMap T x) = Φ (T (Torus.rep x))
  unfold torusMap
  rw [Torus.descend_mk hΦ]


lemma q12_perEquiv_shift {w : Euc d → Euc d} (hwp : Torus.Per w) (τ : ℝ) :
    PerEquiv (fun y => y + τ • w y) := by
  intro y n
  show y + Lattice.toEuc n + τ • w (y + Lattice.toEuc n) = y + τ • w y + Lattice.toEuc n
  rw [hwp]; abel

/-- One Euler step is stable in the weak norm. -/
lemma q12_weakClose_step {ν μ : Measure (Torus d)} {b τ V₁ V₂ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {w : Euc d → Euc d} (hwp : Torus.Per w) (hw : ContDiff ℝ 2 w)
    (hw1 : ∀ y, ‖fderiv ℝ w y‖ ≤ V₁) (hw2 : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ V₂)
    (h : WeakClose ν μ b) :
    WeakClose (ν.map (torusMap (fun y => y + τ • w y))) (μ.map (torusMap (fun y => y + τ • w y)))
      (b * (1 + (2 * V₁ + V₁ ^ 2 + V₂) * τ)) := by
  intro Φ B hΦp hC
  have hT := q12_perEquiv_shift hwp τ
  have hcT : Continuous (fun y : Euc d => y + τ • w y) :=
    continuous_id.add (hw.continuous.const_smul τ)
  have hΦc : Continuous Φ := hC.1.continuous
  rw [q12_Iw_map hT hcT ν hΦp hΦc, q12_Iw_map hT hcT μ hΦp hΦc]
  have hC' := q12_C2b_comp hτ hτ1 hC hw hw1 hw2
  have := h _ _ (q12_perEquiv_per_comp hT hΦp) hC'
  calc _ ≤ b * (B * (1 + (2 * V₁ + V₁ ^ 2 + V₂) * τ)) := this
    _ = _ := by ring

end HRS.Uniform.Q12
