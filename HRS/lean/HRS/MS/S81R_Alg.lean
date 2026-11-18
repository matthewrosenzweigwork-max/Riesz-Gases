import Mathlib

/-!
# S81R, packet R1: abstract reversal of Markov chain functionals

Let `μ` be a measure on `E`, `T t` operators on functions (a semigroup), `S` a class of test functions closed under
products and under `T t` (`t ≥ 0`), such that `μ` is `T`-stationary and `T t` is `μ`-symmetric on `S` (`ChainOp`).
For a time-stamped list `L = [(v₁,f₁),…,(vₙ,fₙ)]` and a start time `s`,
`s81r_foldT s L = T_{v₁-s}(f₁ · T_{v₂-v₁}(f₂ · ⋯ T_{vₙ-vₙ₋₁}(fₙ)))` (the Markov expectation of `∏ fₖ(Z_{vₖ})` from the state at time `s`).
`s81r_foldT_refl`: `∫ foldT s' (reflection of L) dμ = ∫ foldT s L dμ` (time reversal `v ↦ c - v` with the order reversed).
-/

noncomputable section

open MeasureTheory

namespace HRS.MS.S81R

section Alg

variable {E : Type*} [MeasurableSpace E]

/-- the time-stamped chain functional -/
def s81r_foldT (T : ℝ → (E → ℝ) → (E → ℝ)) : ℝ → List (ℝ × (E → ℝ)) → (E → ℝ)
  | _, [] => fun _ => 1
  | s, (v, f) :: r => T (v - s) (fun y => f y * s81r_foldT T v r y)

/-- reflection `v ↦ c - v` with reversed order -/
def s81r_refl (c : ℝ) (L : List (ℝ × (E → ℝ))) : List (ℝ × (E → ℝ)) :=
  (L.map (fun p => (c - p.1, p.2))).reverse

/-- the times of the list are nondecreasing -/
def s81r_Pw (L : List (ℝ × (E → ℝ))) : Prop := (L.map Prod.fst).Pairwise (· ≤ ·)

/-- the start time precedes all times of the list -/
def s81r_Ge (s : ℝ) (L : List (ℝ × (E → ℝ))) : Prop := ∀ p ∈ L, s ≤ p.1

/-- all functions of the list lie in `S` -/
def s81r_AllS (S : (E → ℝ) → Prop) (L : List (ℝ × (E → ℝ))) : Prop := ∀ p ∈ L, S p.2

/-- closure hypotheses: constants, products, `T t` for `t ≥ 0` -/
structure ClosOp (T : ℝ → (E → ℝ) → (E → ℝ)) (S : (E → ℝ) → Prop) : Prop where
  one : S (fun _ => 1)
  mul : ∀ f g, S f → S g → S (fun x => f x * g x)
  mem : ∀ t f, 0 ≤ t → S f → S (T t f)

/-- hypotheses of the abstract chain lemma -/
structure ChainOp (μ : Measure E) (T : ℝ → (E → ℝ) → (E → ℝ)) (S : (E → ℝ) → Prop) : Prop
    extends ClosOp T S where
  stat : ∀ t f, 0 ≤ t → S f → ∫ x, T t f x ∂μ = ∫ x, f x ∂μ
  symm : ∀ t f g, 0 ≤ t → S f → S g → ∫ x, T t f x * g x ∂μ = ∫ x, f x * T t g x ∂μ

variable {μ : Measure E} {T : ℝ → (E → ℝ) → (E → ℝ)} {S : (E → ℝ) → Prop}

theorem s81r_Pw_tail {v : ℝ} {f : E → ℝ} {r : List (ℝ × (E → ℝ))} (h : s81r_Pw ((v, f) :: r)) :
    s81r_Pw r ∧ s81r_Ge v r := by
  unfold s81r_Pw at h ⊢
  simp only [List.map_cons, List.pairwise_cons] at h
  refine ⟨h.2, fun p hp => h.1 p.1 (List.mem_map.2 ⟨p, hp, rfl⟩)⟩

theorem s81r_Pw_refl (c : ℝ) {L : List (ℝ × (E → ℝ))} (h : s81r_Pw L) : s81r_Pw (s81r_refl c L) := by
  unfold s81r_Pw at h
  unfold s81r_Pw s81r_refl
  rw [List.map_reverse, List.pairwise_reverse, List.map_map]
  rw [List.pairwise_map] at h ⊢
  refine h.imp fun {a b} hab => ?_
  simp only [Function.comp]
  linarith

theorem s81r_foldT_mem (h : ClosOp T S) :
    ∀ (L : List (ℝ × (E → ℝ))) (s : ℝ), s81r_Pw L → s81r_Ge s L → s81r_AllS S L →
      S (s81r_foldT T s L)
  | [], s, _, _, _ => h.one
  | (v, f) :: r, s, hP, hG, hA => by
    obtain ⟨hP', hG'⟩ := s81r_Pw_tail hP
    refine h.mem _ _ (sub_nonneg.2 (hG (v, f) (by simp))) (h.mul _ _ (hA (v, f) (by simp)) ?_)
    exact s81r_foldT_mem h r v hP' hG' (fun p hp => hA p (List.mem_cons_of_mem _ hp))

/-- the integral does not depend on the start time -/
theorem s81r_int_start (h : ChainOp μ T S) (L : List (ℝ × (E → ℝ))) {s s' : ℝ}
    (hP : s81r_Pw L) (hs : s81r_Ge s L) (hs' : s81r_Ge s' L) (hA : s81r_AllS S L) :
    ∫ x, s81r_foldT T s L x ∂μ = ∫ x, s81r_foldT T s' L x ∂μ := by
  cases L with
  | nil => simp [s81r_foldT]
  | cons p r =>
    obtain ⟨v, f⟩ := p
    obtain ⟨hP', hG'⟩ := s81r_Pw_tail hP
    have hφ : S (fun y => f y * s81r_foldT T v r y) :=
      h.mul _ _ (hA (v, f) (by simp))
        (s81r_foldT_mem h.toClosOp r v hP' hG' (fun q hq => hA q (List.mem_cons_of_mem _ hq)))
    simp only [s81r_foldT]
    rw [h.stat _ _ (sub_nonneg.2 (hs (v, f) (by simp))) hφ,
      h.stat _ _ (sub_nonneg.2 (hs' (v, f) (by simp))) hφ]

/-- back folding of the last two entries -/
theorem s81r_back (L : List (ℝ × (E → ℝ))) (s v₁ v₂ : ℝ) (a b : E → ℝ) :
    s81r_foldT T s (L ++ [(v₁, a), (v₂, b)]) =
      s81r_foldT T s (L ++ [(v₁, fun x => a x * T (v₂ - v₁) b x)]) := by
  induction L generalizing s with
  | nil =>
    simp [s81r_foldT]
  | cons p r ih =>
    obtain ⟨v, f⟩ := p
    simp only [List.cons_append, s81r_foldT]
    rw [ih v]

/-- forward folding of the first two entries (uses symmetry) -/
theorem s81r_forward (h : ChainOp μ T S) (s s' v₁ v₂ : ℝ) (f₁ f₂ : E → ℝ) (r : List (ℝ × (E → ℝ)))
    (hP : s81r_Pw ((v₁, f₁) :: (v₂, f₂) :: r))
    (hs : s ≤ v₁) (hs' : s' ≤ v₂)
    (hA : s81r_AllS S ((v₁, f₁) :: (v₂, f₂) :: r)) :
    ∫ x, s81r_foldT T s ((v₁, f₁) :: (v₂, f₂) :: r) x ∂μ =
      ∫ x, s81r_foldT T s' ((v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) :: r) x ∂μ := by
  obtain ⟨hP1, -⟩ := s81r_Pw_tail hP
  obtain ⟨hP2, hG2⟩ := s81r_Pw_tail hP1
  have h2 : v₁ ≤ v₂ := by
    unfold s81r_Pw at hP
    simp only [List.map_cons, List.pairwise_cons] at hP
    exact hP.1 v₂ (by simp)
  have hf₁ : S f₁ := hA (v₁, f₁) (by simp)
  have hf₂ : S f₂ := hA (v₂, f₂) (by simp)
  have hrA : s81r_AllS S r := fun q hq => hA q (by simp [hq])
  have hψ : S (s81r_foldT T v₂ r) := s81r_foldT_mem h.toClosOp r v₂ hP2 hG2 hrA
  have hφ : S (fun y => f₂ y * s81r_foldT T v₂ r y) := h.mul _ _ hf₂ hψ
  have hT : S (T (v₂ - v₁) f₁) := h.mem _ _ (sub_nonneg.2 h2) hf₁
  have hφ' : S (fun y => (f₂ y * T (v₂ - v₁) f₁ y) * s81r_foldT T v₂ r y) :=
    h.mul _ _ (h.mul _ _ hf₂ hT) hψ
  simp only [s81r_foldT]
  rw [h.stat _ _ (sub_nonneg.2 hs) (h.mul _ _ hf₁ (h.mem _ _ (sub_nonneg.2 h2) hφ))]
  rw [h.stat _ _ (sub_nonneg.2 hs') hφ']
  have := h.symm (v₂ - v₁) f₁ (fun y => f₂ y * s81r_foldT T v₂ r y) (sub_nonneg.2 h2) hf₁ hφ
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  ring

/-- **time reversal of the chain functional** -/
theorem s81r_foldT_refl (h : ChainOp μ T S) (c : ℝ) :
    ∀ (n : ℕ) (L : List (ℝ × (E → ℝ))), L.length = n → s81r_Pw L → s81r_AllS S L →
      ∀ s s' : ℝ, s81r_Ge s L → s81r_Ge s' (s81r_refl c L) →
        ∫ x, s81r_foldT T s' (s81r_refl c L) x ∂μ = ∫ x, s81r_foldT T s L x ∂μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hP hA s s' hs hs'
  match L, hn, hP, hA, hs, hs' with
  | [], _, _, _, _, _ => simp [s81r_refl, s81r_foldT]
  | [(v, f)], _, _, hA, hs, hs' =>
    have hf : S f := hA (v, f) (by simp)
    have h1 : s ≤ v := hs (v, f) (by simp)
    have h2 : s' ≤ c - v := hs' (c - v, f) (by simp [s81r_refl])
    simp only [s81r_refl, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, s81r_foldT]
    have hf1 : S (fun y => f y * 1) := by simpa using hf
    rw [h.stat _ _ (sub_nonneg.2 h2) hf1, h.stat _ _ (sub_nonneg.2 h1) hf1]
  | (v₁, f₁) :: (v₂, f₂) :: r, hn, hP, hA, hs, hs' =>
    obtain ⟨hP1, hG1⟩ := s81r_Pw_tail hP
    obtain ⟨hP2, hG2⟩ := s81r_Pw_tail hP1
    have h12 : v₁ ≤ v₂ := hG1 (v₂, f₂) (by simp)
    have hf₁ : S f₁ := hA (v₁, f₁) (by simp)
    have hf₂ : S f₂ := hA (v₂, f₂) (by simp)
    have hrA : s81r_AllS S r := fun q hq => hA q (by simp [hq])
    have hgS : S (fun x => f₂ x * T (v₂ - v₁) f₁ x) :=
      h.mul _ _ hf₂ (h.mem _ _ (sub_nonneg.2 h12) hf₁)
    have hA' : s81r_AllS S ((v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) :: r) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hgS
      · exact hrA p hp
    have hP' : s81r_Pw ((v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) :: r) := by
      unfold s81r_Pw at hP1 ⊢
      simpa using hP1
    have hrefl : s81r_refl c ((v₁, f₁) :: (v₂, f₂) :: r) =
        s81r_refl c r ++ [(c - v₂, f₂), (c - v₁, f₁)] := by
      simp [s81r_refl, List.reverse_cons]
    have hrefl' : s81r_refl c ((v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) :: r) =
        s81r_refl c r ++ [(c - v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x)] := by
      simp [s81r_refl, List.reverse_cons]
    have hstep : s81r_foldT T s' (s81r_refl c ((v₁, f₁) :: (v₂, f₂) :: r)) =
        s81r_foldT T s' (s81r_refl c ((v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) :: r)) := by
      rw [hrefl, hrefl', s81r_back]
      have e : (c - v₁) - (c - v₂) = v₂ - v₁ := by ring
      rw [e]
    have hGe' : s81r_Ge s' (s81r_refl c ((v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) :: r)) := by
      intro p hp
      rw [hrefl'] at hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hs' p (by rw [hrefl]; exact List.mem_append_left _ hp)
      · have : p = (c - v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) := by simpa using hp
        subst this
        exact hs' (c - v₂, f₂) (by rw [hrefl]; simp)
    have hlen : ((v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) :: r).length < n := by
      rw [← hn]; simp
    have hGe2 : s81r_Ge v₂ ((v₂, fun x => f₂ x * T (v₂ - v₁) f₁ x) :: r) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact le_rfl
      · exact hG2 p hp
    rw [hstep, ih _ hlen _ rfl hP' hA' v₂ s' hGe2 hGe']
    exact (s81r_forward h s v₂ v₁ v₂ f₁ f₂ r hP (hs (v₁, f₁) (by simp)) le_rfl hA).symm

end Alg

end HRS.MS.S81R
