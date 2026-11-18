import HRS.MS.SA12X2O

/-!
# S.A.12 N8 (SA12X2), part P: the telescoped Leibniz remainder

`R_j(idx) = ∑_q ∂^{σ_q}[(∂_{l_q} a) ∂_j ∂^{t_q} F]` with `idx = σ_q ++ (l_q :: t_q)` (as a list of `Term`s,
proved by the cons recursion `sa12x2_Rj_cons`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

structure SA12X2Term (d : ℕ) where
  r : ℕ
  s : ℕ
  σ : Fin r → Fin d
  t : Fin s → Fin d
  l : Fin d

/-- The value `∂^σ[(∂_l a) ∂_j ∂^t F]`. -/
def sa12x2_tv (a F : Euc d → ℝ) (j : Fin d) (τ : SA12X2Term d) (y : Euc d) : ℝ :=
  partialDeriv τ.σ (fun z => D1 τ.l a z * D1 j (partialDeriv τ.t F) z) y

theorem sa12x2_D1_list_sum {ι : Type*} (l : Fin d) (L : List ι) (f : ι → Euc d → ℝ) (y : Euc d)
    (hf : ∀ τ ∈ L, DifferentiableAt ℝ (f τ) y) :
    D1 l (fun z => (L.map (fun τ => f τ z)).sum) y = (L.map (fun τ => D1 l (f τ) y)).sum := by
  induction L with
  | nil => simp [D1]
  | cons τ L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : DifferentiableAt ℝ (f τ) y := hf τ (List.mem_cons_self)
    have h2 : DifferentiableAt ℝ (fun z => (L.map (fun τ => f τ z)).sum) y := by
      have : ∀ L' : List ι, (∀ τ ∈ L', DifferentiableAt ℝ (f τ) y) →
          DifferentiableAt ℝ (fun z => (L'.map (fun τ => f τ z)).sum) y := by
        intro L' hL'
        induction L' with
        | nil => simp
        | cons τ' L'' ih' =>
          simp only [List.map_cons, List.sum_cons]
          exact (hL' τ' List.mem_cons_self).add (ih' fun σ hσ => hL' σ (List.mem_cons_of_mem _ hσ))
      exact this L fun σ hσ => hf σ (List.mem_cons_of_mem _ hσ)
    have e := (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv
    unfold D1 at *
    rw [show (fun z => f τ z + (L.map (fun τ => f τ z)).sum) = (fun z => f τ z) +
      (fun z => (L.map (fun τ => f τ z)).sum) from rfl, fderiv_add h1 h2]
    simp only [ContinuousLinearMap.add_apply]
    rw [ih fun σ hσ => hf σ (List.mem_cons_of_mem _ hσ)]

theorem sa12x2_tel {m : ℕ} {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a) (hF : ContDiff ℝ ∞ F)
    (j : Fin d) :
    ∀ (n : ℕ), n ≤ m → ∀ (idx : Fin n → Fin d), ∃ L : List (SA12X2Term d),
      L.length = n ∧ (∀ τ ∈ L, τ.r + τ.s + 1 = n) ∧
      (∀ τ ∈ L, ∀ x, partialDeriv idx F x =
        partialDeriv τ.σ (D1 τ.l (partialDeriv τ.t F)) x) ∧
      (∀ y, sa12z3_Rj a F idx j y = (L.map (fun τ => sa12x2_tv a F j τ y)).sum) := by
  intro n
  induction n with
  | zero =>
    intro _ idx
    refine ⟨[], rfl, by simp, by simp, fun y => ?_⟩
    simp [sa12z3_Rj, sa12z3_pd_zero, sa12z3_pd_zero_fun]
  | succ n ih =>
    intro hn idx
    obtain ⟨l, t, rfl⟩ : ∃ l t, idx = (Fin.cons l t : Fin (n + 1) → Fin d) :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    obtain ⟨L, hlen, hrs, hF2, hR⟩ := ih (by omega) t
    let mapτ : SA12X2Term d → SA12X2Term d := fun τ =>
      ⟨τ.r + 1, τ.s, (Fin.cons l τ.σ : Fin (τ.r + 1) → Fin d), τ.t, τ.l⟩
    refine ⟨⟨0, n, (Fin.elim0 : Fin 0 → Fin d), t, l⟩ :: L.map mapτ, ?_, ?_, ?_, ?_⟩
    · simp [hlen]
    · intro τ hτ
      simp only [List.mem_cons, List.mem_map] at hτ
      rcases hτ with rfl | ⟨τ', hτ', rfl⟩
      · simp
      · have := hrs τ' hτ'
        simp only [mapτ]; omega
    · have e1 : partialDeriv (Fin.cons l t : Fin (n + 1) → Fin d) F = D1 l (partialDeriv t F) :=
        funext fun z => sa12z3_pd_cons t l (sa12z3_cd_of_inf hF _) z
      intro τ hτ x
      simp only [List.mem_cons, List.mem_map] at hτ
      rcases hτ with rfl | ⟨τ', hτ', rfl⟩
      · simp only [sa12z3_pd_zero_fun]
        rw [e1]
      · simp only [mapτ]
        rw [e1]
        have hG : partialDeriv t F = partialDeriv τ'.σ (D1 τ'.l (partialDeriv τ'.t F)) :=
          funext fun z => hF2 τ' hτ' z
        rw [hG]
        have hsm : ContDiff ℝ ∞ (D1 τ'.l (partialDeriv τ'.t F)) :=
          ((sa12z3_pd_contDiff_inf hF τ'.t).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
        rw [sa12z3_pd_cons τ'.σ l (sa12z3_cd_of_inf hsm _) x]
    · intro y
      have hGcd : ∀ (l' : Fin d) {s' : ℕ} (t' : Fin s' → Fin d),
          ContDiff ℝ m (fun z => D1 l' a z * D1 j (partialDeriv t' F) z) := by
        intro l' s' t'
        have hDa : ContDiff ℝ m (D1 l' a) :=
          (ha.fderiv_right (m := m) (by push_cast; rfl)).clm_apply contDiff_const
        have hK : ContDiff ℝ ∞ (D1 j (partialDeriv t' F)) :=
          ((sa12z3_pd_contDiff_inf hF t').fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
        exact hDa.mul (sa12z3_cd_of_inf hK _)
      have hdiff : ∀ τ ∈ L, DifferentiableAt ℝ (sa12x2_tv a F j τ) y := by
        intro τ hτ
        have hr := hrs τ hτ
        have h1 := sa12z3_pd_contDiff (k := m) (n := τ.r) (hGcd τ.l τ.t) (by omega) τ.σ
        exact (h1.differentiable (by
          have : ((m - τ.r : ℕ) : WithTop ℕ∞) ≠ 0 := by
            have : m - τ.r ≠ 0 := by omega
            exact_mod_cast this
          exact this) y)
      rw [sa12x2_Rj_cons hn ha hF j l t y]
      have hfun : sa12z3_Rj a F t j = fun z => (L.map (fun τ => sa12x2_tv a F j τ z)).sum :=
        funext hR
      rw [hfun, sa12x2_D1_list_sum l L (fun τ => sa12x2_tv a F j τ) y hdiff]
      simp only [List.map_cons, List.sum_cons, List.map_map]
      have hmap : ∀ τ ∈ L, sa12x2_tv a F j (mapτ τ) y = D1 l (sa12x2_tv a F j τ) y := by
        intro τ hτ
        have hr := hrs τ hτ
        show partialDeriv (Fin.cons l τ.σ : Fin (τ.r + 1) → Fin d) _ y = _
        exact sa12z3_pd_cons τ.σ l ((hGcd τ.l τ.t).of_le (by exact_mod_cast (by omega : τ.r + 1 ≤ m))) y
      have hsum : (L.map (fun τ => sa12x2_tv a F j (mapτ τ) y)).sum =
          (L.map (fun τ => D1 l (sa12x2_tv a F j τ) y)).sum :=
        congrArg List.sum (List.map_congr_left hmap)
      have hhead : sa12x2_tv a F j ⟨0, n, (Fin.elim0 : Fin 0 → Fin d), t, l⟩ y =
          D1 l a y * D1 j (partialDeriv t F) y := by
        unfold sa12x2_tv
        simp only [sa12z3_pd_zero_fun]
      rw [Function.comp_def, hsum, hhead]
      ring

end HRS.MH.AdjointRd.Phase2SA12Near
