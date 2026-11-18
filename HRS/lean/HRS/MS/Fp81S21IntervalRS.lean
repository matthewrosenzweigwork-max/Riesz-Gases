import HRS.MS.R2InterpAux15

/-!
# HRS S2.1(iii), packet 17: interval Riemann--Stieltjes adapters

The interval adapter uses the affine change of variables from `[q,r]` to
`[0,r-q]`.  The splitting result below is stated for tag-independent,
endpoint-additive summands.  For tag-dependent summands, endpoint additivity
alone does not justify replacing the tag on a crossing cell; a tag-regularity
argument is required for the drift and covariance applications.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2Interp

/- Exact exported type:
   fp81s21_IsRSOn (q r : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) : Prop
   := IsR2RS (r-q) (fun τ u v => S (q+τ) (q+u) (q+v)) I
-/
def fp81s21_IsRSOn (q r : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) : Prop :=
  IsR2RS (r - q) (fun τ u v => S (q + τ) (q + u) (q + v)) I

/- Exact exported type:
   fp81s21_isRSOn_iff_shifted (q r : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) :
     fp81s21_IsRSOn q r S I ↔
       IsR2RS (r-q) (fun τ u v => S (q+τ) (q+u) (q+v)) I
-/
theorem fp81s21_isRSOn_iff_shifted (q r : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) :
    fp81s21_IsRSOn q r S I ↔
      IsR2RS (r - q) (fun τ u v => S (q + τ) (q + u) (q + v)) I := Iff.rfl

/- Exact exported type:
   fp81s21_isRSOn_unique {q r : ℝ} (hqr : q < r)
     {S : ℝ → ℝ → ℝ → ℝ} {I I' : ℝ}
     (hI : fp81s21_IsRSOn q r S I) (hI' : fp81s21_IsRSOn q r S I') : I = I'
-/
theorem fp81s21_isRSOn_unique {q r : ℝ} (hqr : q < r)
    {S : ℝ → ℝ → ℝ → ℝ} {I I' : ℝ}
    (hI : fp81s21_IsRSOn q r S I) (hI' : fp81s21_IsRSOn q r S I') : I = I' := by
  apply s102_RS_unique (T := r - q) (by linarith)
  · exact hI
  · exact hI'

/- Exact exported type:
   fp81s21_IsR2RS_zero (S : ℝ → ℝ → ℝ → ℝ) : IsR2RS 0 S 0
-/
theorem fp81s21_IsR2RS_zero (S : ℝ → ℝ → ℝ → ℝ) : IsR2RS 0 S 0 := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro n u τ hu hu0 huT htag hmesh
  have hn : n = 0 := by
    by_contra hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hidx : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) < Fin.last n := by
      apply Fin.mk_lt_mk.mpr
      simpa using hnpos
    have hlt := hu hidx
    have hz : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := by
      apply Fin.ext
      rfl
    rw [hz, hu0, huT] at hlt
    exact (lt_irrefl 0 hlt)
  subst n
  simpa using hε

/- Exact exported type:
   fp81s21_isRSOn_zero (q : ℝ) (S : ℝ → ℝ → ℝ → ℝ) :
     fp81s21_IsRSOn q q S 0
-/
theorem fp81s21_isRSOn_zero (q : ℝ) (S : ℝ → ℝ → ℝ → ℝ) :
    fp81s21_IsRSOn q q S 0 := by
  simpa [fp81s21_IsRSOn] using
    (fp81s21_IsR2RS_zero (fun τ u v => S (q + τ) (q + u) (q + v)))

/- Exact exported type:
   fp81s21_isRSOn_zero_forces {q : ℝ} {S : ℝ → ℝ → ℝ → ℝ} {I : ℝ}
     (hI : fp81s21_IsRSOn q q S I) : I = 0
-/
theorem fp81s21_isRSOn_zero_forces {q : ℝ} {S : ℝ → ℝ → ℝ → ℝ} {I : ℝ}
    (hI : fp81s21_IsRSOn q q S I) : I = 0 := by
  have hI' : IsR2RS 0 (fun τ u v => S (q + τ) (q + u) (q + v)) I := by
    simpa [fp81s21_IsRSOn] using hI
  by_contra hne
  have hpos : 0 < |I| := abs_pos.mpr hne
  obtain ⟨δ, hδ, hsum⟩ := hI' |I| hpos
  let u : Fin (0 + 1) → ℝ := fun _ => 0
  have hu : StrictMono u := by
    intro i j hij
    fin_cases i
    fin_cases j
    norm_num at hij
  have hval := hsum 0 u Fin.elim0 hu rfl rfl
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
  have hcontra : |I| < |I| := by simpa [u] using hval
  exact (lt_irrefl |I| hcontra)

/- Exact exported type:
   fp81s21_isRSOn_value {q r : ℝ} (hqr : q < r)
     {S : ℝ → ℝ → ℝ → ℝ} {I : ℝ}
     (hTag : ∀ τ τ' u v, S τ u v = S τ' u v)
     (hAdd : ∀ u v w, u ≤ v → v ≤ w → S 0 u w = S 0 u v + S 0 v w)
     (hI : fp81s21_IsRSOn q r S I) : I = S 0 q r
-/
theorem fp81s21_isRSOn_value {q r : ℝ} (hqr : q < r)
    {S : ℝ → ℝ → ℝ → ℝ} {I : ℝ}
    (hTag : ∀ τ τ' u v, S τ u v = S τ' u v)
    (hAdd : ∀ u v w, u ≤ v → v ≤ w → S 0 u w = S 0 u v + S 0 v w)
    (hI : fp81s21_IsRSOn q r S I) : I = S 0 q r := by
  apply fp81s21_isRSOn_unique hqr hI
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro n u τ hu hu0 huT htag hmesh
  have huMono : Monotone u := hu.monotone
  have huNonneg : ∀ i : Fin (n + 1), 0 ≤ u i := by
    intro i
    rw [← hu0]
    exact huMono (Fin.zero_le i)
  have hterms : ∀ i : Fin n,
      S (q + τ i) (q + u i.castSucc) (q + u i.succ) =
        S 0 (q + u i.castSucc) (q + u i.succ) := by
    intro i
    rw [hTag (q + τ i) 0]

  have hterms' : ∀ i : Fin n,
      S 0 (q + u i.castSucc) (q + u i.succ) =
        S 0 q (q + u i.succ) - S 0 q (q + u i.castSucc) := by
    intro i
    have h := hAdd q (q + u i.castSucc) (q + u i.succ)
      (by linarith [huNonneg i.castSucc])
      (by have hs := hu (Fin.castSucc_lt_succ (i := i)); linarith)
    linarith
  let a : ℕ → ℝ := fun k => u ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hcast : ∀ i : Fin n, a i = u i.castSucc := by
    intro i
    simp only [a]
    congr 1
    ext
    simp [min_eq_left i.2.le]
  have hsucc : ∀ i : Fin n, a (i + 1) = u i.succ := by
    intro i
    simp only [a]
    congr 1
    ext
    simp [min_eq_left (Nat.succ_le_of_lt i.2)]
  let g : ℝ → ℝ := fun x => S 0 q (q + x)
  let f : ℕ → ℝ := fun k => g (a (k + 1)) - g (a k)
  have hsum : ∑ i : Fin n,
      S (q + τ i) (q + u i.castSucc) (q + u i.succ) =
        S 0 q (q + (r - q)) - S 0 q q := by
    calc
      ∑ i : Fin n, S (q + τ i) (q + u i.castSucc) (q + u i.succ) =
          ∑ i : Fin n, f i := Finset.sum_congr rfl (fun i _ => by
            calc
              S (q + τ i) (q + u i.castSucc) (q + u i.succ) =
                  S 0 (q + u i.castSucc) (q + u i.succ) := hterms i
              _ = S 0 q (q + u i.succ) - S 0 q (q + u i.castSucc) := hterms' i
              _ = f i := by simp [f, g, hcast i, hsucc i])
      _ = ∑ k ∈ Finset.range n, f k := Fin.sum_univ_eq_sum_range f n
      _ = g (a n) - g (a 0) := by
        change ∑ k ∈ Finset.range n, (g (a (k + 1)) - g (a k)) = _
        rw [Finset.sum_range_sub (fun k => g (a k)) n]
      _ = S 0 q (q + u (Fin.last n)) - S 0 q (q + u 0) := by
        have haN : a n = u (Fin.last n) := by
          dsimp [a]
          congr 1
          exact Fin.ext (by simp)
        have ha0 : a 0 = u 0 := by
          dsimp [a]
          congr 1
        simp [g, haN, ha0]
      _ = S 0 q (q + (r - q)) - S 0 q q := by
        rw [hu0, huT]
        simp
  have hqq : S 0 q q = 0 := by
    have h := hAdd q q q le_rfl le_rfl
    linarith
  have hval : ∑ i : Fin n,
      S (q + τ i) (q + u i.castSucc) (q + u i.succ) = S 0 q r := by
    rw [hsum, hqq]
    have hshift : q + (r - q) = r := by ring
    rw [hshift]
    simp
  rw [hval]
  simpa [sub_eq_add_neg, abs_sub_comm] using hε

/- Exact exported type:
   fp81s21_isRSOn_split_tagIndependent {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r)
     {S : ℝ → ℝ → ℝ → ℝ} {I I₁ I₂ : ℝ}
     (hTag : ∀ τ τ' u v, S τ u v = S τ' u v)
     (hAdd : ∀ u v w, u ≤ v → v ≤ w → S 0 u w = S 0 u v + S 0 v w)
     (hI : fp81s21_IsRSOn q r S I)
     (hI₁ : fp81s21_IsRSOn q s S I₁) (hI₂ : fp81s21_IsRSOn s r S I₂) :
     I = I₁ + I₂
-/
theorem fp81s21_isRSOn_split_tagIndependent {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r)
    {S : ℝ → ℝ → ℝ → ℝ} {I I₁ I₂ : ℝ}
    (hTag : ∀ τ τ' u v, S τ u v = S τ' u v)
    (hAdd : ∀ u v w, u ≤ v → v ≤ w → S 0 u w = S 0 u v + S 0 v w)
    (hI : fp81s21_IsRSOn q r S I)
    (hI₁ : fp81s21_IsRSOn q s S I₁) (hI₂ : fp81s21_IsRSOn s r S I₂) :
    I = I₁ + I₂ := by
  by_cases hqr : q = r
  · have hqs' : q = s := le_antisymm hqs (by simpa [hqr] using hsr)
    subst s
    subst r
    have hI0 := fp81s21_isRSOn_zero_forces hI
    have hI10 := fp81s21_isRSOn_zero_forces hI₁
    have hI20 := fp81s21_isRSOn_zero_forces hI₂
    rw [hI0, hI10, hI20]
    ring
  · have hqr' : q < r := lt_of_le_of_ne (hqs.trans hsr) (by
      intro hrq
      exact hqr hrq)
    by_cases hqs' : q = s
    · subst s
      have hI10 := fp81s21_isRSOn_zero_forces hI₁
      have huniq := fp81s21_isRSOn_unique hqr' hI hI₂
      rw [huniq, hI10]
      ring
    · by_cases hsr' : s = r
      · subst r
        have hI20 := fp81s21_isRSOn_zero_forces hI₂
        have huniq := fp81s21_isRSOn_unique hqr' hI hI₁
        rw [huniq, hI20]
        ring
      · have hqslt : q < s := lt_of_le_of_ne hqs (by
          intro hsq
          exact hqs' hsq)
        have hsrlT : s < r := lt_of_le_of_ne hsr (by
          intro hrs
          exact hsr' hrs)
        have hvI := fp81s21_isRSOn_value hqr' hTag hAdd hI
        have hvI₁ := fp81s21_isRSOn_value hqslt hTag hAdd hI₁
        have hvI₂ := fp81s21_isRSOn_value hsrlT hTag hAdd hI₂
        rw [hvI, hvI₁, hvI₂]
        exact hAdd q s r hqs hsr

/- Exact exported type:
   fp81s21_IsR2RS_shifted_iff (q r : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) :
     IsR2RS (r-q) (fun τ u v => S (q+τ) (q+u) (q+v)) I ↔
       fp81s21_IsRSOn q r S I
-/
theorem fp81s21_IsR2RS_shifted_iff (q r : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) :
    IsR2RS (r - q) (fun τ u v => S (q + τ) (q + u) (q + v)) I ↔
      fp81s21_IsRSOn q r S I := Iff.rfl.symm

#print axioms fp81s21_IsRSOn
#print axioms fp81s21_isRSOn_iff_shifted
#print axioms fp81s21_isRSOn_unique
#print axioms fp81s21_IsR2RS_zero
#print axioms fp81s21_isRSOn_zero
#print axioms fp81s21_isRSOn_zero_forces
#print axioms fp81s21_isRSOn_value
#print axioms fp81s21_isRSOn_split_tagIndependent
#print axioms fp81s21_IsR2RS_shifted_iff

end HRS.Fp81.S21

end
