import HRS.MS.SA12X5D5C

/-!
# S.A.12 X5 D5: the difference of two periodic solutions is a periodic solution with source `sa12x5_src`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_grad_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (y : Euc d) :
    gradient (fun y => f y - g y) y = gradient f y - gradient g y := by
  have hfd : DifferentiableAt ℝ f y := (hf.differentiable (by simp)) y
  have hgd : DifferentiableAt ℝ g y := (hg.differentiable (by simp)) y
  have h : HasFDerivAt (fun y => f y - g y) (fderiv ℝ f y - fderiv ℝ g y) y :=
    hfd.hasFDerivAt.sub hgd.hasFDerivAt
  show (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (fun y => f y - g y) y) =
    (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f y) - (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ g y)
  rw [h.fderiv, map_sub]

theorem sa12x5_lap_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (y : Euc d) :
    Laplacian.laplacian (fun y => f y - g y) y = Laplacian.laplacian f y - Laplacian.laplacian g y := by
  rw [HRS.MS.UniqT3.lap_eq ((hf.sub hg).of_le (by simp)) y, HRS.MS.UniqT3.lap_eq (hf.of_le (by simp)) y,
    HRS.MS.UniqT3.lap_eq (hg.of_le (by simp)) y, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sa12x5_D1_sub hf hg i, sa12x5_D1_sub (sa12y_D1_contDiff hf i) (sa12y_D1_contDiff hg i) i]

theorem sa12x5_lap_smooth {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => Laplacian.laplacian f y) := by
  have h : ContDiff ℝ ∞ (fun y => ∑ i : Fin d, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i f) y) :=
    ContDiff.sum fun i _ => sa12y_D1_contDiff (sa12y_D1_contDiff hf i) i
  have e : (fun y => Laplacian.laplacian f y) =
      fun y => ∑ i : Fin d, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i f) y :=
    funext fun y => HRS.MS.UniqT3.lap_eq (hf.of_le (by simp)) y
  rw [e]
  exact h

theorem sa12x5_E_smooth {F : Euc d → ℝ} {b : Euc d → Euc d} {g : Euc d → ℝ} (ν : ℝ)
    (hF : ContDiff ℝ ∞ F) (hb : ContDiff ℝ ∞ b) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + g y) := by
  have h1 := (contDiff_const (c := ν)).mul (sa12x5_lap_smooth hF)
  have h2 : ContDiff ℝ ∞ (fun y => inner ℝ (b y) (gradient F y)) := hb.inner ℝ (sa12y_grad_contDiff hF)
  exact (h1.add h2).add hg

theorem sa12x5_inner_eq (v : Euc d) (f : Euc d → ℝ) (x : Euc d) :
    inner ℝ v (gradient f x) = ∑ i, v i * HRS.MS.UniqT3.D1 i f x := by
  simp only [PiLp.inner_apply, sa12x5_grad_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem sa12x5_diff_isPerSol (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m' : ℕ} {T L : ℝ}
    {γ : Euc d → ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν₁ ν₂ : ℝ} {μ₁ μ₂ : ℝ → Euc d → ℝ} {V : Euc d → ℝ}
    {b₁ b₂ : ℝ → Euc d → Euc d} (hP₁ : PerSmooth s T L γ M ν₁ μ₁ V b₁)
    (hP₂ : PerSmooth s T L γ M ν₂ μ₂ V b₂) (hT₁ : PeriodicTimeSmooth T μ₁) (hT₂ : PeriodicTimeSmooth T μ₂)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {F₁ F₂ : ℝ → Euc d → ℝ}
    (h₁ : IsPerSol m' L γ M ν₁ μ₁ b₁ (fun _ _ => 0) t F₁)
    (h₂ : IsPerSol m' L γ M ν₂ μ₂ b₂ (fun _ _ => 0) t F₂) :
    IsPerSol m' L γ M ν₁ μ₁ b₁ (sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂) t (fun τ x => F₁ τ x - F₂ τ x) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hP₁.hL
  have hmem : ∀ τ ∈ Icc (0 : ℝ) t, τ ∈ Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans ht.2⟩
  let g₁ : ℝ → Euc d → ℝ := fun τ y => -perNonlocal L γ M (μ₁ τ) (F₁ τ) y + 0
  let g₂ : ℝ → Euc d → ℝ := fun τ y => -perNonlocal L γ M (μ₂ τ) (F₂ τ) y + 0
  have sol₁ : IsClassicalSol m' ν₁ b₁ g₁ t F₁ := h₁.sol
  have sol₂ : IsClassicalSol m' ν₂ b₂ g₂ t F₂ := h₂.sol
  have JF₁ : sa12x5_PJC t F₁ := ⟨fun τ hτ => (sol₁.smooth τ hτ).1, fun n idx => sol₁.contF n idx⟩
  have JF₂ : sa12x5_PJC t F₂ := ⟨fun τ hτ => (sol₂.smooth τ hτ).1, fun n idx => sol₂.contF n idx⟩
  have JG₁ : sa12x5_PJC t g₁ := ⟨fun τ hτ => (sol₁.smooth τ hτ).2, fun n idx => sol₁.contG n idx⟩
  have JG₂ : sa12x5_PJC t g₂ := ⟨fun τ hτ => (sol₂.smooth τ hτ).2, fun n idx => sol₂.contG n idx⟩
  have Jdb : ∀ i : Fin d, sa12x5_PJC t (fun τ x => b₁ τ x i - b₂ τ x i) := fun i =>
    sa12x5_PJC_sub (sa12x5_drift_PJC hd hs0 hsd hP₁ hT₁ ht.2 i) (sa12x5_drift_PJC hd hs0 hsd hP₂ hT₂ ht.2 i)
  have hbs₁ : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (b₁ τ) := fun τ hτ =>
    sa12x5_drift_smooth hd hs0 hsd hP₁ hT₁ ht.2 hτ
  have hbs₂ : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (b₂ τ) := fun τ hτ =>
    sa12x5_drift_smooth hd hs0 hsd hP₂ hT₂ ht.2 hτ
  have Jtot : sa12x5_PJC t (fun τ y => (ν₁ - ν₂) * Laplacian.laplacian (F₂ τ) y +
      ∑ i, (b₁ τ y i - b₂ τ y i) * HRS.MS.UniqT3.D1 i (F₂ τ) y + g₁ τ y - g₂ τ y) :=
    sa12x5_PJC_sub (sa12x5_PJC_add (sa12x5_PJC_add (sa12x5_PJC_smul (sa12x5_PJC_lap JF₂) (ν₁ - ν₂))
      (sa12x5_PJC_sum (t := t) (Finset.univ : Finset (Fin d))
        (fun i τ y => (b₁ τ y i - b₂ τ y i) * HRS.MS.UniqT3.D1 i (F₂ τ) y)
        (fun i _ => sa12x5_PJC_mul (Jdb i) (sa12x5_PJC_D1 JF₂ i)))) JG₁) JG₂
  have hμs₁ := fun τ (hτ : τ ∈ Icc (0 : ℝ) t) => hP₁.μ_smooth τ (hmem τ hτ)
  have hμp₁ := fun τ (hτ : τ ∈ Icc (0 : ℝ) t) => hP₁.μ_periodic τ (hmem τ hτ)
  have hlin : ∀ τ ∈ Icc (0 : ℝ) t, ∀ y,
      perNonlocal L γ M (μ₁ τ) (fun x => F₁ τ x - F₂ τ x) y =
        perNonlocal L γ M (μ₁ τ) (F₁ τ) y - perNonlocal L γ M (μ₁ τ) (F₂ τ) y := fun τ hτ y =>
    sa12x5_perNonlocal_sub hL0 hP₁.hγ.locInt hP₁.hγ.periodic M (hμs₁ τ hτ) (sol₁.smooth τ hτ).1
      (sol₂.smooth τ hτ).1 (hμp₁ τ hτ) (h₁.periodic τ hτ) (h₂.periodic τ hτ) y
  have hid : ∀ τ ∈ Icc (0 : ℝ) t, ∀ y,
      (-perNonlocal L γ M (μ₁ τ) (fun x => F₁ τ x - F₂ τ x) y +
        sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂ τ y) =
      (ν₁ - ν₂) * Laplacian.laplacian (F₂ τ) y +
        ∑ i, (b₁ τ y i - b₂ τ y i) * HRS.MS.UniqT3.D1 i (F₂ τ) y + g₁ τ y - g₂ τ y := by
    intro τ hτ y
    rw [hlin τ hτ y]
    unfold sa12x5_src
    rw [sa12x5_inner_eq (b₁ τ y - b₂ τ y) (F₂ τ) y]
    simp only [g₁, g₂, PiLp.sub_apply]
    ring
  have JGG : sa12x5_PJC t (fun τ y => -perNonlocal L γ M (μ₁ τ) (fun x => F₁ τ x - F₂ τ x) y +
      sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂ τ y) :=
    sa12x5_PJC_congr (fun τ hτ => funext fun y => (hid τ hτ y).symm) Jtot
  refine ⟨⟨fun τ hτ => ⟨(JF₁.1 τ hτ).sub (JF₂.1 τ hτ), JGG.1 τ hτ⟩,
    fun n idx => (sa12x5_PJC_sub JF₁ JF₂).2 n idx, fun n idx => JGG.2 n idx, ?_⟩, ?_, ?_⟩
  · intro j hj idx x τ hτ
    have hd₁ := sol₁.deriv_t j hj idx x τ hτ
    have hd₂ := sol₂.deriv_t j hj idx x τ hτ
    have hF₁ := (sol₁.smooth τ hτ).1
    have hF₂ := (sol₂.smooth τ hτ).1
    have hE₁ := sa12x5_E_smooth (g := g₁ τ) ν₁ hF₁ (hbs₁ τ hτ) (sol₁.smooth τ hτ).2
    have hE₂ := sa12x5_E_smooth (g := g₂ τ) ν₂ hF₂ (hbs₂ τ hτ) (sol₂.smooth τ hτ).2
    have key : HasDerivWithinAt (fun τ' => partialDeriv idx (fun y => F₁ τ' y - F₂ τ' y) x)
        (partialDeriv idx (fun y => ν₁ * Laplacian.laplacian (F₁ τ) y +
            inner ℝ (b₁ τ y) (gradient (F₁ τ) y) + g₁ τ y) x -
          partialDeriv idx (fun y => ν₂ * Laplacian.laplacian (F₂ τ) y +
            inner ℝ (b₂ τ y) (gradient (F₂ τ) y) + g₂ τ y) x) (Icc (0 : ℝ) t) τ := by
      refine (hd₁.sub hd₂).congr (fun τ' hτ' => ?_) ?_
      · exact sa12x5_pd_sub (sol₁.smooth τ' hτ').1 (sol₂.smooth τ' hτ').1 idx x
      · exact sa12x5_pd_sub hF₁ hF₂ idx x
    have hval : partialDeriv idx (fun y => ν₁ * Laplacian.laplacian (F₁ τ) y +
            inner ℝ (b₁ τ y) (gradient (F₁ τ) y) + g₁ τ y) x -
          partialDeriv idx (fun y => ν₂ * Laplacian.laplacian (F₂ τ) y +
            inner ℝ (b₂ τ y) (gradient (F₂ τ) y) + g₂ τ y) x =
        partialDeriv idx (fun y => ν₁ * Laplacian.laplacian (fun x => F₁ τ x - F₂ τ x) y +
            inner ℝ (b₁ τ y) (gradient (fun x => F₁ τ x - F₂ τ x) y) +
            (-perNonlocal L γ M (μ₁ τ) (fun x => F₁ τ x - F₂ τ x) y +
              sa12x5_src L γ M ν₁ ν₂ μ₁ μ₂ b₁ b₂ F₂ τ y)) x := by
      rw [← sa12x5_pd_sub hE₁ hE₂ idx x]
      congr 1
      funext y
      rw [sa12x5_lap_sub hF₁ hF₂, sa12x5_grad_sub hF₁ hF₂, inner_sub_right, hlin τ hτ y]
      unfold sa12x5_src
      simp only [g₁, g₂, inner_sub_left]
      ring
    rw [hval] at key
    exact key
  · intro τ hτ x k
    simp only [h₁.periodic τ hτ x k, h₂.periodic τ hτ x k]
  · intro τ hτ
    refine ⟨(JF₁.1 τ hτ).sub (JF₂.1 τ hτ), fun j hj idx => ?_⟩
    obtain ⟨B₁, hB₁⟩ := (h₁.bdd τ hτ).2 j hj idx
    obtain ⟨B₂, hB₂⟩ := (h₂.bdd τ hτ).2 j hj idx
    refine ⟨B₁ + B₂, fun x => ?_⟩
    rw [sa12x5_pd_sub (JF₁.1 τ hτ) (JF₂.1 τ hτ) idx x]
    exact (abs_sub _ _).trans (add_le_add (hB₁ x) (hB₂ x))

end HRS.MH.AdjointRd.Phase2SA12X5
