import HRS.MS.WadAux102

/-!
# S8.3, packet S8F-3: Leibniz decomposition of the source of an iterated difference

`s8f_term a ρ w I J s y = 𝓑_{Δ_I ρ}(w_J(· + Σ z_I))(y)`, with `Δ_I ρ = s8f_Dif a I ρ` and `w_J = s8f_Dif a J w`.
`s8f_Sr ξs`: the list of pairs `(I, J)` (`I ≠ []`, `I ++ J ~ ξs`) of the nonlocal terms.
`s8f_term_step`: `Δ_ξ (term I J) = term I (ξ :: J) + term (ξ :: I) J` (from `s8e_qu_decomp`).
`s8f_Dif_source`: `Δ_{ξs} (𝓑_ρ w) = 𝓑_ρ (Δ_{ξs} w) + Σ_{(I,J) ∈ Sr ξs} term I J`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

def s8f_term (a : ℝ) (ρ : Euc d → ℝ) (w : ℝ → Euc d → ℝ) (I J : List (Euc d)) (s : ℝ) (y : Euc d) : ℝ :=
  s84_Bop (fun y' => s8f_Dif a I (fun _ => ρ) s y')
    (fun y' => s8f_Dif a J w s (y' + s8e_zs a I.sum s)) y

def s8f_Sr : List (Euc d) → List (List (Euc d) × List (Euc d))
  | [] => []
  | ξ :: rest => ([ξ], rest) :: (s8f_Sr rest).flatMap (fun p => [(p.1, ξ :: p.2), (ξ :: p.1, p.2)])

theorem s8f_term_nil (a : ℝ) (ρ : Euc d → ℝ) (w : ℝ → Euc d → ℝ) (J : List (Euc d)) (s : ℝ) (y : Euc d) :
    s8f_term a ρ w [] J s y = s84_Bop ρ (fun y' => s8f_Dif a J w s y') y := by
  simp [s8f_term, s8f_Dif, s8e_zs]

theorem s8f_zs_add (a : ℝ) (ξ η : Euc d) (s : ℝ) : s8e_zs a (ξ + η) s = s8e_zs a ξ s + s8e_zs a η s := by
  unfold s8e_zs; rw [smul_add]

theorem s8f_term_step (hd : 2 ≤ d) (a : ℝ) (ρ : Euc d → ℝ) (w : ℝ → Euc d → ℝ) {s : ℝ} (y : Euc d)
    (ξ : Euc d) (I J : List (Euc d))
    (hσ : s84_GaussReg (fun y' => s8f_Dif a I (fun _ => ρ) s y')) {B : ℝ}
    (hh : s84_C2b (fun y' => s8f_Dif a J w s (y' + s8e_zs a I.sum s)) B) (hz : ‖s8e_zs a ξ s‖ ≤ 1) :
    s8e_u a ξ (s8f_term a ρ w I J) s y = s8f_term a ρ w I (ξ :: J) s y + s8f_term a ρ w (ξ :: I) J s y := by
  have hdec := s8e_qu_decomp hd hσ hh hz y
  set z : Euc d := s8e_zs a ξ s with hzdef
  set ζ : Euc d := s8e_zs a I.sum s with hζ
  have e1 : (fun y' => s8f_Dif a (ξ :: J) w s (y' + ζ)) =
      fun y' => (fun y' => s8f_Dif a J w s (y' + ζ)) (y' + z) - (fun y' => s8f_Dif a J w s (y' + ζ)) y' := by
    funext y'
    simp only [s8f_Dif_cons]
    rw [add_right_comm]
  have e2 : (fun y' => s8f_Dif a (ξ :: I) (fun _ => ρ) s y') =
      fun y' => (fun y' => s8f_Dif a I (fun _ => ρ) s y') (y' + z) - (fun y' => s8f_Dif a I (fun _ => ρ) s y') y' := by
    funext y'
    simp only [s8f_Dif_cons]
    rfl
  have e3 : (fun y' => s8f_Dif a J w s (y' + s8e_zs a (ξ :: I).sum s)) =
      fun y' => (fun y' => s8f_Dif a J w s (y' + ζ)) (y' + z) := by
    funext y'
    simp only [List.sum_cons, s8f_zs_add]
    rw [← add_assoc]
  unfold s8e_u s8f_term
  rw [e1, e2, e3]
  exact hdec

theorem s8f_Sr_perm : ∀ (ξs : List (Euc d)), ∀ p ∈ s8f_Sr ξs, (p.1 ++ p.2).Perm ξs ∧ p.1 ≠ []
  | [] => by simp [s8f_Sr]
  | ξ :: rest => by
    intro p hp
    simp only [s8f_Sr, List.mem_cons, List.mem_flatMap] at hp
    rcases hp with rfl | ⟨q, hq, hp⟩
    · exact ⟨by simp, by simp⟩
    · have := s8f_Sr_perm rest q hq
      simp only [List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨(List.perm_middle).trans (this.1.cons ξ), this.2⟩
      · exact ⟨by simpa using this.1.cons ξ, by simp⟩

theorem s8f_flatMap_pair_length {α : Type} (l : List α) (p1 p2 : α → α) :
    (l.flatMap (fun p => [p1 p, p2 p])).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons p l ih => simp [List.flatMap_cons, ih]; omega

theorem s8f_Sr_length : ∀ (ξs : List (Euc d)), (s8f_Sr ξs).length + 1 ≤ 2 ^ ξs.length
  | [] => by simp [s8f_Sr]
  | ξ :: rest => by
    have ih := s8f_Sr_length rest
    simp only [s8f_Sr, List.length_cons, s8f_flatMap_pair_length, pow_succ]
    omega

theorem s8f_sum_flatMap_pair {α : Type} (l : List α) (p1 p2 : α → α) (f : α → ℝ) :
    ((l.flatMap (fun p => [p1 p, p2 p])).map f).sum = (l.map (fun p => f (p1 p) + f (p2 p))).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp [List.flatMap_cons, ih]; ring

def s8f_small (N : ℕ) (ξs : List (Euc d)) : Prop :=
  ξs.length ≤ N ∧ (ξs.map (fun e => ‖e‖)).sum ≤ 1 / 8

theorem s8f_sum_nonneg (ξs : List (Euc d)) : 0 ≤ (ξs.map (fun e => ‖e‖)).sum :=
  List.sum_nonneg (by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg a)

theorem s8f_prod_nonneg (ξs : List (Euc d)) : 0 ≤ (ξs.map (fun e => ‖e‖)).prod :=
  List.prod_nonneg (by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg a)

theorem s8f_small_cons {N : ℕ} {ξ : Euc d} {rest : List (Euc d)} (h : s8f_small N (ξ :: rest)) :
    s8f_small N rest ∧ ‖ξ‖ ≤ 1 / 8 := by
  obtain ⟨h1, h2⟩ := h
  simp only [List.length_cons, List.map_cons, List.sum_cons] at h1 h2
  have := s8f_sum_nonneg rest
  exact ⟨⟨by omega, by linarith [norm_nonneg ξ]⟩, by linarith⟩

theorem s8f_small_perm {N : ℕ} {ξs I J : List (Euc d)} (h : s8f_small N ξs) (hp : (I ++ J).Perm ξs) :
    s8f_small N I ∧ s8f_small N J := by
  obtain ⟨h1, h2⟩ := h
  have hl := hp.length_eq
  have hs : ((I ++ J).map (fun e => ‖e‖)).sum = (ξs.map (fun e => ‖e‖)).sum := (hp.map _).sum_eq
  rw [List.map_append, List.sum_append] at hs
  rw [List.length_append] at hl
  have a1 := s8f_sum_nonneg I
  have a2 := s8f_sum_nonneg J
  exact ⟨⟨by omega, by linarith⟩, ⟨by omega, by linarith⟩⟩

theorem s8f_sum_map_sub {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map (fun p => f p - g p)).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.map_cons, List.sum_cons]; linarith

theorem s8f_Dif_source (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) (ρ : Euc d → ℝ) (w : ℝ → Euc d → ℝ) (N : ℕ) {t : ℝ}
    (HG : ∀ I, s8f_small N I → ∀ s ∈ Set.Icc 0 t, s84_GaussReg (fun y => s8f_Dif a I (fun _ => ρ) s y))
    (HC : ∀ J, s8f_small N J → ∀ s ∈ Set.Icc 0 t, ∃ B, s84_C2b (fun y => s8f_Dif a J w s y) B) :
    ∀ ξs : List (Euc d), s8f_small N ξs → ∀ s ∈ Set.Icc 0 t, ∀ y,
      s8f_Dif a ξs (fun s y => s84_Bop ρ (w s) y) s y =
        s84_Bop ρ (fun y' => s8f_Dif a ξs w s y') y +
          ((s8f_Sr ξs).map (fun p => s8f_term a ρ w p.1 p.2 s y)).sum := by
  intro ξs
  induction ξs with
  | nil =>
    intro _ s _ y
    simp [s8f_Dif, s8f_Sr]
  | cons ξ rest ih =>
    intro hsm s hs y
    obtain ⟨hsr, hξ⟩ := s8f_small_cons hsm
    have hz : ‖s8e_zs a ξ s‖ ≤ 1 := (s8e_zs_norm ha hs.1 ξ).trans (by linarith)
    rw [s8f_Dif_cons, ih hsr s hs (y + s8e_zs a ξ s), ih hsr s hs y]
    have hS : s8f_Sr (ξ :: rest) = ([ξ], rest) :: (s8f_Sr rest).flatMap
        (fun p => [(p.1, ξ :: p.2), (ξ :: p.1, p.2)]) := rfl
    rw [hS, List.map_cons, List.sum_cons,
      s8f_sum_flatMap_pair (s8f_Sr rest) (fun p => (p.1, ξ :: p.2)) (fun p => (ξ :: p.1, p.2))]
    -- the main part
    obtain ⟨B0, hB0⟩ := HC rest hsr s hs
    have hstep0 := s8f_term_step hd a ρ w y ξ [] rest (HG [] ⟨by simp, by simp⟩ s hs)
      (by simpa [s8e_zs] using s8e_C2b_shift hB0 0) hz
    simp only [s8f_term_nil] at hstep0
    unfold s8e_u at hstep0
    simp only [s8f_term_nil] at hstep0
    -- the nonlocal part
    have hB : (((s8f_Sr rest).map (fun p => s8f_term a ρ w p.1 p.2 s (y + s8e_zs a ξ s))).sum -
        ((s8f_Sr rest).map (fun p => s8f_term a ρ w p.1 p.2 s y)).sum) =
        ((s8f_Sr rest).map (fun p => s8f_term a ρ w p.1 (ξ :: p.2) s y +
          s8f_term a ρ w (ξ :: p.1) p.2 s y)).sum := by
      rw [s8f_sum_map_sub]
      congr 1
      refine List.map_congr_left fun p hp => ?_
      obtain ⟨hperm, -⟩ := s8f_Sr_perm rest p hp
      obtain ⟨hI, hJ⟩ := s8f_small_perm hsr hperm
      obtain ⟨B, hBp⟩ := HC p.2 hJ s hs
      have := s8f_term_step hd a ρ w y ξ p.1 p.2 (HG p.1 hI s hs)
        (s8e_C2b_shift hBp (s8e_zs a p.1.sum s)) hz
      unfold s8e_u at this
      exact this
    simp only [] at hstep0 ⊢
    linarith

end HRS.MS.Wad
