import HRS.MS.S104eC0
import HRS.MS.UlClassAux2

/-!
# S104E route C, packet C4 part A: the Duhamel integral of an abstract perturbation family

Forward time `τ`.  `Dd Q ν g τ t0 x = ∫_0^τ P_{t0-σ} (g σ) (x) dσ` (`P = ouSg Q ν`), for a family `g` with `C²` bounded slices that is uniformly
continuous in `σ` in the sup norm (`GFam`).  Adapts `ulD`, `ul5_shift`, `ul4b_tail` (autonomous S5.1) to an abstract family (no `ulPert`, no `UlHyp`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

def Dd (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (g : ℝ → Euc d → ℝ) (τ t0 : ℝ) (x : Euc d) : ℝ :=
  ∫ σ in (0 : ℝ)..τ, ouSg Q ν (t0 - σ) (g σ) x

structure GFam (T K : ℝ) (g : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ σ ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (g σ)
  bd : ∀ σ ∈ Icc (0 : ℝ) T, ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i (g σ) y‖ ≤ K
  cont : ∀ σ₀ ∈ Icc (0 : ℝ) T, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Icc (0 : ℝ) T, |σ - σ₀| < δ →
    ∀ y, |g σ y - g σ₀ y| ≤ ε

theorem GFam.abs {T K : ℝ} {g : ℝ → Euc d → ℝ} (hG : GFam T K g) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T) (y : Euc d) :
    |g σ y| ≤ K := by
  have := hG.bd σ hσ 0 (Nat.zero_le _) y
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

theorem GFam.mono {T T' K : ℝ} {g : ℝ → Euc d → ℝ} (hG : GFam T K g) (h : T' ≤ T) : GFam T' K g :=
  ⟨fun σ hσ => hG.c2 σ ⟨hσ.1, hσ.2.trans h⟩, fun σ hσ => hG.bd σ ⟨hσ.1, hσ.2.trans h⟩,
    fun σ₀ h0 ε hε => by
      obtain ⟨δ, hδ, hd⟩ := hG.cont σ₀ ⟨h0.1, h0.2.trans h⟩ ε hε
      exact ⟨δ, hδ, fun σ hσ => hd σ ⟨hσ.1, hσ.2.trans h⟩⟩⟩

theorem GFam.shift {T K a : ℝ} {g : ℝ → Euc d → ℝ} (hG : GFam (T + a) K g) (ha : 0 ≤ a) :
    GFam T K (fun σ => g (σ + a)) :=
  ⟨fun σ hσ => hG.c2 (σ + a) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩,
    fun σ hσ => hG.bd (σ + a) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩,
    fun σ₀ h0 ε hε => by
      obtain ⟨δ, hδ, hd⟩ := hG.cont (σ₀ + a) ⟨by linarith [h0.1], by linarith [h0.2]⟩ ε hε
      exact ⟨δ, hδ, fun σ hσ hσδ => hd (σ + a) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
        (by rwa [add_sub_add_right_eq_sub])⟩⟩

/-- continuity of the integrand `σ ↦ P_{t0-σ} (g σ) (x)` -/
theorem c4_phi_cont (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {T K : ℝ} {g : ℝ → Euc d → ℝ}
    (hG : GFam T K g) (x : Euc d) {τ t0 : ℝ} (hτT : τ ≤ T) (hτt : τ ≤ t0) :
    ContinuousOn (fun σ => ouSg Q ν (t0 - σ) (g σ) x) (Icc 0 τ) := by
  intro σ₀ hσ₀
  have hσ₀T : σ₀ ∈ Icc (0 : ℝ) T := ⟨hσ₀.1, hσ₀.2.trans hτT⟩
  have hc := ul4_ouSg_cont_time Q hν (hG.c2 σ₀ hσ₀T) (M := K) (hG.bd σ₀ hσ₀T) x
  have hmaps : MapsTo (fun σ : ℝ => t0 - σ) (Icc 0 τ) (Ici 0) := fun σ hσ =>
    mem_Ici.2 (by linarith [hσ.2])
  have hcomp : ContinuousWithinAt (fun σ => ouSg Q ν (t0 - σ) (g σ₀) x) (Icc 0 τ) σ₀ :=
    (hc.comp (continuous_const.sub continuous_id).continuousOn hmaps) σ₀ hσ₀
  rw [Metric.continuousWithinAt_iff] at hcomp ⊢
  intro ε hε
  obtain ⟨δ₁, hδ₁, h1⟩ := hcomp (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h2⟩ := hG.cont σ₀ hσ₀T (ε / 4) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun σ hσ hd => ?_⟩
  have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans hτT⟩
  have hd1 : dist σ σ₀ < δ₁ := hd.trans_le (min_le_left _ _)
  have hd2 : |σ - σ₀| < δ₂ := by
    rw [← Real.dist_eq]; exact hd.trans_le (min_le_right _ _)
  have hsub : ouSg Q ν (t0 - σ) (fun y => g σ y - g σ₀ y) x =
      ouSg Q ν (t0 - σ) (g σ) x - ouSg Q ν (t0 - σ) (g σ₀) x :=
    congrFun (ul3C_sub_lin Q ν (t0 - σ) (hG.c2 σ hσT).continuous.measurable
      (hG.c2 σ₀ hσ₀T).continuous.measurable (fun y => hG.abs hσT y) (fun y => hG.abs hσ₀T y)) x
  have hab : |ouSg Q ν (t0 - σ) (fun y => g σ y - g σ₀ y) x| ≤ ε / 4 :=
    ul4_ouSg_abs_le Q ν _ (fun y => h2 σ hσT hd2 y) x
  have h1' := h1 hσ hd1
  rw [Real.dist_eq] at h1' ⊢
  have : ouSg Q ν (t0 - σ) (g σ) x - ouSg Q ν (t0 - σ₀) (g σ₀) x =
      ouSg Q ν (t0 - σ) (fun y => g σ y - g σ₀ y) x +
        (ouSg Q ν (t0 - σ) (g σ₀) x - ouSg Q ν (t0 - σ₀) (g σ₀) x) := by rw [hsub]; ring
  rw [this]
  calc _ ≤ |ouSg Q ν (t0 - σ) (fun y => g σ y - g σ₀ y) x| +
        |ouSg Q ν (t0 - σ) (g σ₀) x - ouSg Q ν (t0 - σ₀) (g σ₀) x| := abs_add_le _ _
    _ < ε := by linarith

/-- the Duhamel integrand is jointly measurable (on `σ ∈ [0,τ]`, extended by clamping) -/
def clampT (τ σ : ℝ) : ℝ := max 0 (min σ τ)

theorem clampT_cont (τ : ℝ) : Continuous (clampT τ) := by
  unfold clampT; fun_prop

theorem clampT_mem {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) : clampT τ σ ∈ Icc 0 τ :=
  ⟨le_max_left _ _, max_le hτ (min_le_right _ _)⟩

theorem clampT_eq {τ σ : ℝ} (hσ : σ ∈ Icc 0 τ) : clampT τ σ = σ := by
  unfold clampT
  rw [min_eq_left hσ.2, max_eq_right hσ.1]

end HRS.MS.S104e.C
