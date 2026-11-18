import HRS.MD.EQLZVocab
import HRS.MD.EQLZDet

/-!
# EQ-LZ packet REV: reversal invariance of grid vectors (`eqlz_rev`), proof

For smooth `g_0,...,g_m`, `HasFDD` (first factor `1`, list `[(a,g_0),(δ,g_1),...,(δ,g_m)]`) and invariance give
`E ∏ g_i(Z_{a+iδ}) = ∫ g_0 P_δ(g_1 P_δ(⋯ P_δ g_m)) dπ =: R [g_0,...,g_m]`.  The symmetry of `P_δ` gives
`R (h_0 :: h_1 :: l) = R ((h_1 P_δ h_0) :: l)`, hence `R L.reverse = R L` (strong induction on the length).
Products of smooth functions determine finite measures on `(𝕋^n)^{m+1}` (`lzdet_ext`).
The hypotheses `hsm`, `hsemi`, `hsymm`, `hinv` are explicit hypotheses of the statement.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open HRS HRS.MD.EQLZ HRS.MD.EQLZDet

namespace HRS.MD.EQLZRev

variable {n : ℕ}

section Aux

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)

/-- `P_δ(h_1 P_δ(h_2 ⋯ P_δ(h_k)))` for the list `[h_1,...,h_k]`. -/
def lzrK (δ : ℝ) (L : List (Torus n → ℝ)) : Torus n → ℝ :=
  fddKer hn hκ hU (L.map fun h => (δ, h))

/-- `R [h_0,...,h_m] = ∫ h_0 · P_δ(h_1 · P_δ(⋯)) dπ` (`R [] = 0`). -/
def lzrR (δ : ℝ) : List (Torus n → ℝ) → ℝ
  | [] => 0
  | h :: l => ∫ x, h x * lzrK hn hκ hU δ l x ∂(d1_gibbsMeasure κ U)

theorem lzrK_nil (δ : ℝ) : lzrK hn hκ hU δ [] = fun _ => 1 := rfl

theorem lzrK_cons (δ : ℝ) (h : Torus n → ℝ) (l : List (Torus n → ℝ)) :
    lzrK hn hκ hU δ (h :: l) = d1_P hn hκ hU δ (fun x => h x * lzrK hn hκ hU δ l x) := rfl

theorem lzrK_snoc_swap (δ : ℝ) (h₀ h₁ : Torus n → ℝ) (X : List (Torus n → ℝ)) :
    lzrK hn hκ hU δ (X ++ [fun x => h₁ x * d1_P hn hκ hU δ h₀ x]) =
      lzrK hn hκ hU δ (X ++ [h₁, h₀]) := by
  induction X with
  | nil =>
    rw [List.nil_append, List.nil_append, lzrK_cons, lzrK_cons, lzrK_cons, lzrK_nil]
    simp only [mul_one]
  | cons h X ih =>
    rw [List.cons_append, List.cons_append, lzrK_cons, lzrK_cons, ih]

theorem lzrR_snoc_swap (δ : ℝ) (h₀ h₁ : Torus n → ℝ) (X : List (Torus n → ℝ)) :
    lzrR hn hκ hU δ (X ++ [fun x => h₁ x * d1_P hn hκ hU δ h₀ x]) =
      lzrR hn hκ hU δ (X ++ [h₁, h₀]) := by
  cases X with
  | nil =>
    simp only [List.nil_append, lzrR, lzrK_cons, lzrK_nil, mul_one]
  | cons h X =>
    simp only [List.cons_append, lzrR]
    rw [lzrK_snoc_swap]

theorem lzrK_smooth
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (d1_P hn hκ hU t φ))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ L : List (Torus n → ℝ), (∀ h ∈ L, Torus.IsSmooth h) → Torus.IsSmooth (lzrK hn hκ hU δ L) := by
  intro L
  induction L with
  | nil => intro _; exact lzdet_smooth_const 1
  | cons h L ih =>
    intro hL
    rw [lzrK_cons]
    exact hsm δ hδ _ (lzdet_smooth_mul (hL h (by simp)) (ih fun g hg => hL g (by simp [hg])))

theorem lzrR_swap
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (d1_P hn hκ hU t φ))
    (hsymm : ∀ t : ℝ, 0 ≤ t → ∀ φ ψ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
      ∫ x, ψ x * d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) =
        ∫ x, φ x * d1_P hn hκ hU t ψ x ∂(d1_gibbsMeasure κ U))
    {δ : ℝ} (hδ : 0 ≤ δ) {h₀ h₁ : Torus n → ℝ} (l : List (Torus n → ℝ))
    (h0 : Torus.IsSmooth h₀) (h1 : Torus.IsSmooth h₁) (hl : ∀ h ∈ l, Torus.IsSmooth h) :
    lzrR hn hκ hU δ (h₀ :: h₁ :: l) =
      lzrR hn hκ hU δ ((fun x => h₁ x * d1_P hn hκ hU δ h₀ x) :: l) := by
  have hK := lzrK_smooth hn hκ hU hsm hδ l hl
  simp only [lzrR, lzrK_cons]
  rw [hsymm δ hδ (fun x => h₁ x * lzrK hn hκ hU δ l x) h₀ (lzdet_smooth_mul h1 hK) h0]
  congr 1; funext x; ring

theorem lzrR_reverse
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (d1_P hn hκ hU t φ))
    (hsymm : ∀ t : ℝ, 0 ≤ t → ∀ φ ψ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
      ∫ x, ψ x * d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) =
        ∫ x, φ x * d1_P hn hκ hU t ψ x ∂(d1_gibbsMeasure κ U))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ (k : ℕ) (L : List (Torus n → ℝ)), L.length = k → (∀ h ∈ L, Torus.IsSmooth h) →
      lzrR hn hκ hU δ L.reverse = lzrR hn hκ hU δ L := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro L hk hL
    match L, hk with
    | [], _ => rfl
    | [h], _ => rfl
    | h₀ :: h₁ :: l, hk =>
      have h0 := hL h₀ (by simp)
      have h1 := hL h₁ (by simp)
      have hl : ∀ h ∈ l, Torus.IsSmooth h := fun h hh => hL h (by simp [hh])
      have hnew : ∀ h ∈ ((fun x => h₁ x * d1_P hn hκ hU δ h₀ x) :: l), Torus.IsSmooth h := by
        intro h hh
        rcases List.mem_cons.mp hh with rfl | hh
        · exact lzdet_smooth_mul h1 (hsm δ hδ h₀ h0)
        · exact hl h hh
      have e1 := ih (l.length + 1) (by simp at hk; omega)
        ((fun x => h₁ x * d1_P hn hκ hU δ h₀ x) :: l) (by simp) hnew
      rw [lzrR_swap hn hκ hU hsm hsymm hδ l h0 h1 hl, ← e1]
      simp only [List.reverse_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [lzrR_snoc_swap]

theorem lzr_ofFn_rev {α : Type} {m : ℕ} (g : Fin m → α) :
    List.ofFn (fun i => g (Fin.rev i)) = (List.ofFn g).reverse := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_reverse, Fin.rev]
    congr 1
    ext
    simp
    omega

theorem lzr_fddProd_grid {Ω : Type*} (Z : ℝ → Ω → Torus n) (δ : ℝ) :
    ∀ (m : ℕ) (G : Fin m → Torus n → ℝ) (t : ℝ) (ω : Ω),
      fddProd Z t (List.ofFn fun i => (δ, G i)) ω = ∏ i : Fin m, G i (Z (t + ((i : ℕ) + 1) * δ) ω) := by
  intro m
  induction m with
  | zero => intro G t ω; simp [fddProd]
  | succ m ih =>
    intro G t ω
    rw [List.ofFn_succ]
    simp only [fddProd]
    rw [ih (fun i => G i.succ) (t + δ), Fin.prod_univ_succ]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun i _ => ?_
      congr 2
      simp only [Fin.val_succ]
      push_cast
      ring

end Aux

theorem eqlz_rev_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (d1_P hn hκ hU t φ))
    (hsemi : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ →
      d1_P hn hκ hU (s + t) φ = d1_P hn hκ hU s (d1_P hn hκ hU t φ))
    (hsymm : ∀ t : ℝ, 0 ≤ t → ∀ φ ψ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
      ∫ x, ψ x * d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) =
        ∫ x, φ x * d1_P hn hκ hU t ψ x ∂(d1_gibbsMeasure κ U))
    (hinv : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ →
      ∫ x, d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) = ∫ x, φ x ∂(d1_gibbsMeasure κ U))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → Ω → Torus n)
    (hZ : ∀ t : ℝ, 0 ≤ t → Measurable (Z t)) (hfdd : HasFDD hn hκ hU P Z (d1_gibbsMeasure κ U))
    (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (m : ℕ) :
    (P.map fun ω (i : Fin (m + 1)) => Z (a + (i : ℕ) * δ) ω).map (fun z i => z (Fin.rev i)) =
      P.map fun ω (i : Fin (m + 1)) => Z (a + (i : ℕ) * δ) ω := by
  have hvec : Measurable fun ω (i : Fin (m + 1)) => Z (a + (i : ℕ) * δ) ω :=
    measurable_pi_iff.mpr fun i => hZ _ (by positivity)
  have hrev : Measurable (fun (z : Fin (m + 1) → Torus n) i => z (Fin.rev i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  -- the expectation of a product along the grid
  have hgrid : ∀ g : Fin (m + 1) → Torus n → ℝ, (∀ i, Torus.IsSmooth (g i)) →
      ∫ ω, ∏ i : Fin (m + 1), g i (Z (a + (i : ℕ) * δ) ω) ∂P = lzrR hn hκ hU δ (List.ofFn g) := by
    intro g hg
    have hadm : ∀ p ∈ (a, g 0) :: List.ofFn (fun i : Fin m => (δ, g i.succ)), 0 ≤ p.1 ∧ Torus.IsSmooth p.2 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨ha, hg 0⟩
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
        exact ⟨hδ, hg i.succ⟩
    have h := hfdd _ hadm (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
    have hmap : (List.ofFn fun i : Fin m => ((δ : ℝ), g i.succ)) =
        (List.ofFn fun i : Fin m => g i.succ).map (fun h => (δ, h)) := by
      rw [List.map_ofFn]; rfl
    have hL : ∀ h ∈ List.ofFn fun i : Fin m => g i.succ, Torus.IsSmooth h := by
      intro h hh
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hh
      exact hg i.succ
    have e1 : ∀ ω, 1 * fddProd Z 0 ((a, g 0) :: List.ofFn (fun i : Fin m => (δ, g i.succ))) ω =
        ∏ i : Fin (m + 1), g i (Z (a + (i : ℕ) * δ) ω) := by
      intro ω
      simp only [fddProd, one_mul, zero_add]
      rw [lzr_fddProd_grid Z δ m (fun i => g i.succ) a ω, Fin.prod_univ_succ]
      congr 1
      · simp
      · refine Finset.prod_congr rfl fun i _ => ?_
        congr 2
        simp only [Fin.val_succ]
        push_cast
        ring
    simp only [e1] at h
    rw [h]
    simp only [fddKer, one_mul]
    rw [List.ofFn_succ, lzrR]
    have := hinv a ha (fun x => g 0 x * fddKer hn hκ hU (List.ofFn fun i : Fin m => (δ, g i.succ)) x)
      (lzdet_smooth_mul (hg 0) (by rw [hmap]; exact lzrK_smooth hn hκ hU hsm hδ _ hL))
    rw [this]
    simp only [lzrK, hmap]
  apply lzdet_ext
  intro G hG
  have hc : Continuous (fun z : Fin (m + 1) → Torus n => ∏ i, G i (z i)) := lzdetProd_continuous hG
  have hc2 : Continuous (fun x : Fin (m + 1) → Torus n => ∏ i, G i (x (Fin.rev i))) :=
    continuous_finsetProd _ fun i _ => (lzdet_continuous (hG i)).comp (continuous_apply (Fin.rev i))
  rw [integral_map hrev.aemeasurable hc.aestronglyMeasurable,
    integral_map hvec.aemeasurable hc.aestronglyMeasurable]
  beta_reduce
  rw [integral_map hvec.aemeasurable hc2.aestronglyMeasurable]
  have e2 : ∀ ω, (∏ i : Fin (m + 1), G i (Z (a + ((Fin.rev i : Fin (m + 1)) : ℕ) * δ) ω)) =
      ∏ j : Fin (m + 1), G (Fin.rev j) (Z (a + (j : ℕ) * δ) ω) := by
    intro ω
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp)
  simp only [e2]
  rw [hgrid (fun j => G (Fin.rev j)) (fun j => hG _), hgrid G hG]
  rw [show (List.ofFn fun j => G (Fin.rev j)) = (List.ofFn G).reverse from lzr_ofFn_rev G]
  exact lzrR_reverse hn hκ hU hsm hsymm hδ _ _ rfl (fun h hh => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hh
    exact hG i)

end HRS.MD.EQLZRev

end
