import HRS.MS.Fp81S21IntervalRS

/-!
# HRS S2.1(iii), packet 17: unrestricted interval splitting

The value-additivity direction uses partitions that contain the splitting
point.  It needs neither tag independence nor additivity of the summand.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2Interp

/- Exact exported type:
   fp81s21_isRSOn_split_general {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r)
     {S : ℝ → ℝ → ℝ → ℝ} {I I₁ I₂ : ℝ}
     (hI : fp81s21_IsRSOn q r S I)
     (hI₁ : fp81s21_IsRSOn q s S I₁)
     (hI₂ : fp81s21_IsRSOn s r S I₂) : I = I₁ + I₂
-/
theorem fp81s21_isRSOn_split_general {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r)
    {S : ℝ → ℝ → ℝ → ℝ} {I I₁ I₂ : ℝ}
    (hI : fp81s21_IsRSOn q r S I)
    (hI₁ : fp81s21_IsRSOn q s S I₁)
    (hI₂ : fp81s21_IsRSOn s r S I₂) : I = I₁ + I₂ := by
  by_cases hqseq : q = s
  · subst s
    have hI₁zero := fp81s21_isRSOn_zero_forces hI₁
    by_cases hqreq : q = r
    · subst r
      have hIzero := fp81s21_isRSOn_zero_forces hI
      have hI₂zero := fp81s21_isRSOn_zero_forces hI₂
      rw [hIzero, hI₁zero, hI₂zero]
      ring
    · have hqr : q < r := lt_of_le_of_ne (le_trans hqs hsr) hqreq
      have hu := fp81s21_isRSOn_unique hqr hI hI₂
      rw [hu, hI₁zero]
      ring
  · by_cases hsreq : s = r
    · subst r
      have hsrzero := fp81s21_isRSOn_zero_forces hI₂
      have hqslt : q < s := lt_of_le_of_ne hqs hqseq
      have hu := fp81s21_isRSOn_unique hqslt hI hI₁
      rw [hu, hsrzero]
      ring
    · have hqslt : q < s := lt_of_le_of_ne hqs hqseq
      have hsrlT : s < r := lt_of_le_of_ne hsr hsreq
      have hT₁ : 0 < s - q := by linarith
      have hT₂ : 0 < r - s := by linarith
      have hwhole : IsR2RS (r - q)
          (fun τ u v => S (q + τ) (q + u) (q + v)) I := hI
      have hleft : IsR2RS (s - q)
          (fun τ u v => S (q + τ) (q + u) (q + v)) I₁ := hI₁
      have hright : IsR2RS (r - s)
          (fun τ u v => S (s + τ) (s + u) (s + v)) I₂ := hI₂
      by_contra hne
      have hpos : 0 < |I - (I₁ + I₂)| := abs_pos.mpr (sub_ne_zero.mpr hne)
      let ε : ℝ := |I - (I₁ + I₂)| / 4
      have hε : 0 < ε := by positivity
      obtain ⟨δ₀, hδ₀, H₀⟩ := hwhole ε hε
      obtain ⟨δ₁, hδ₁, H₁⟩ := hleft ε hε
      obtain ⟨δ₂, hδ₂, H₂⟩ := hright ε hε
      let δ : ℝ := min δ₀ (min δ₁ δ₂) / 2
      have hδ : 0 < δ := by dsimp [δ]; positivity
      have hmin : 0 < min δ₀ (min δ₁ δ₂) := by positivity
      have hδ₀' : δ < δ₀ := by
        dsimp [δ]
        exact lt_of_lt_of_le (half_lt_self hmin) (min_le_left _ _)
      have hδ₁' : δ < δ₁ := by
        dsimp [δ]
        exact lt_of_lt_of_le (half_lt_self hmin)
          (le_trans (min_le_right _ _) (min_le_left _ _))
      have hδ₂' : δ < δ₂ := by
        dsimp [δ]
        exact lt_of_lt_of_le (half_lt_self hmin)
          (le_trans (min_le_right _ _) (min_le_right _ _))
      obtain ⟨n₁, u₁, τ₁, hu₁, hu₁0, hu₁T, htag₁, hmesh₁⟩ :=
        HRS.MC.Sec7.S7PIS2.S7PIS2_exists_partition hT₁ hδ
      obtain ⟨n₂, u₂, τ₂, hu₂, hu₂0, hu₂T, htag₂, hmesh₂⟩ :=
        HRS.MC.Sec7.S7PIS2.S7PIS2_exists_partition hT₂ hδ
      have hn₁ : 0 < n₁ := by
        by_contra hn
        have hn0 : n₁ = 0 := Nat.eq_zero_of_not_pos hn
        subst n₁
        have hbad : (0 : ℝ) = s - q := by simpa [hu₁0] using hu₁T
        linarith
      let u : Fin (n₁ + (n₂ + 1)) → ℝ := Fin.append
        (fun i : Fin n₁ => u₁ i.castSucc)
        (fun j : Fin (n₂ + 1) => (s - q) + u₂ j)
      let τ : Fin (n₁ + n₂) → ℝ := Fin.append τ₁
        (fun j : Fin n₂ => (s - q) + τ₂ j)
      have hleftStart (i : Fin n₁) :
          u (Fin.castAdd n₂ i).castSucc = u₁ i.castSucc := by
        have hidx : (Fin.castAdd n₂ i).castSucc = Fin.castAdd (n₂ + 1) i := by
          apply Fin.ext
          simp [Fin.val_castSucc, Fin.val_castAdd]
        rw [hidx]
        simp [u, Fin.append_left]
      have hleftEnd (i : Fin n₁) :
          u (Fin.castAdd n₂ i).succ = u₁ i.succ := by
        by_cases hi : i.val + 1 < n₁
        · let k : Fin n₁ := ⟨i.val + 1, hi⟩
          have hidx : (Fin.castAdd n₂ i).succ = Fin.castAdd (n₂ + 1) k := by
            apply Fin.ext
            simp [k, Fin.val_succ, Fin.val_castAdd]
          have hk : k.castSucc = i.succ := by
            apply Fin.ext
            simp [k, Fin.val_castSucc, Fin.val_succ]
          rw [hidx]
          simpa [u, Fin.append_left, hk]
        · have hiVal : i.val + 1 = n₁ := by omega
          have hiSucc : i.succ = Fin.last n₁ := by
            apply Fin.ext
            simp [Fin.val_succ, hiVal]
          have hidx : (Fin.castAdd n₂ i).succ = Fin.natAdd n₁ (0 : Fin (n₂ + 1)) := by
            apply Fin.ext
            simp [Fin.val_succ, Fin.val_castAdd, Fin.val_natAdd]
            omega
          rw [hidx]
          rw [hiSucc]
          simp [u, Fin.append_right, hu₂0, hu₁T]
      have hrightStart (j : Fin n₂) :
          u (Fin.natAdd n₁ j).castSucc = (s - q) + u₂ j.castSucc := by
        have hidx : (Fin.natAdd n₁ j).castSucc = Fin.natAdd n₁ j.castSucc := by
          apply Fin.ext
          simp [Fin.val_castSucc, Fin.val_natAdd]
        rw [hidx]
        simp [u, Fin.append_right]
      have hrightEnd (j : Fin n₂) :
          u (Fin.natAdd n₁ j).succ = (s - q) + u₂ j.succ := by
        have hidx : (Fin.natAdd n₁ j).succ = Fin.natAdd n₁ j.succ := by
          apply Fin.ext
          simp [Fin.val_succ, Fin.val_natAdd]
          omega
        rw [hidx]
        simp [u, Fin.append_right]
      have hrightVertex (j : Fin (n₂ + 1)) :
          u (Fin.natAdd n₁ j) = (s - q) + u₂ j := by
        simp [u, Fin.append_right]
      have hτleft (i : Fin n₁) : τ (Fin.castAdd n₂ i) = τ₁ i := by
        simp [τ, Fin.append_left]
      have hτright (j : Fin n₂) :
          τ (Fin.natAdd n₁ j) = (s - q) + τ₂ j := by
        simp [τ, Fin.append_right]
      have huMono : StrictMono u := by
        intro i j hij
        have hij' : i.val < j.val := by exact_mod_cast hij
        by_cases hi : i.val < n₁
        · let i' : Fin n₁ := ⟨i.val, hi⟩
          have hiRep : i = Fin.castAdd (n₂ + 1) i' := by
            apply Fin.ext
            simp [i']
          by_cases hj : j.val < n₁
          · let j' : Fin n₁ := ⟨j.val, hj⟩
            have hjRep : j = Fin.castAdd (n₂ + 1) j' := by
              apply Fin.ext
              simp [j']
            rw [hiRep, hjRep]
            simp [u, Fin.append_left]
            exact hu₁ (by exact_mod_cast hij')
          · let j' : Fin (n₂ + 1) := ⟨j.val - n₁, by omega⟩
            have hjRep : j = Fin.natAdd n₁ j' := by
              apply Fin.ext
              simp [j', Fin.val_natAdd]
              omega
            rw [hiRep, hjRep]
            have hiEnd : u₁ i'.castSucc < s - q := by
              have hidx : i'.castSucc < Fin.last n₁ := by
                apply Fin.mk_lt_mk.mpr
                simpa [Fin.val_castSucc, Fin.val_last] using hi
              rw [← hu₁T]
              exact hu₁ hidx
            have hjNonneg : 0 ≤ u₂ j' := by
              rw [← hu₂0]
              exact hu₂.monotone (Fin.zero_le j')
            simp [u, Fin.append_left, Fin.append_right]
            linarith
        · let i' : Fin (n₂ + 1) := ⟨i.val - n₁, by omega⟩
          let j' : Fin (n₂ + 1) := ⟨j.val - n₁, by omega⟩
          have hiRep : i = Fin.natAdd n₁ i' := by
            apply Fin.ext
            simp [i', Fin.val_natAdd]
            omega
          have hjRep : j = Fin.natAdd n₁ j' := by
            apply Fin.ext
            simp [j', Fin.val_natAdd]
            omega
          rw [hiRep, hjRep]
          have hij'' : i' < j' := by
            apply Fin.mk_lt_mk.mpr
            change i.val - n₁ < j.val - n₁
            omega
          simpa [u, Fin.append_right] using add_lt_add_left (hu₂ hij'') (s - q)
      have hu0 : u 0 = 0 := by
        let i₀ : Fin n₁ := ⟨0, hn₁⟩
        have hidx : (0 : Fin (n₁ + (n₂ + 1))) = Fin.castAdd (n₂ + 1) i₀ := by
          apply Fin.ext
          simp [i₀]
        calc
          u 0 = u (Fin.castAdd (n₂ + 1) i₀) := by rw [hidx]
          _ = u₁ i₀.castSucc := by simp [u, Fin.append_left]
          _ = 0 := by
            have hi₀ : i₀.castSucc = (0 : Fin (n₁ + 1)) := by
              apply Fin.ext
              simp [i₀]
            rw [hi₀, hu₁0]
      have huT : u (Fin.last (n₁ + n₂)) = r - q := by
        have hidx : Fin.last (n₁ + n₂) = Fin.natAdd n₁ (Fin.last n₂) := by
          apply Fin.ext
          simp [Fin.val_natAdd]
        calc
          u (Fin.last (n₁ + n₂)) = u (Fin.natAdd n₁ (Fin.last n₂)) := by rw [hidx]
          _ = (s - q) + u₂ (Fin.last n₂) := hrightVertex _
          _ = r - q := by rw [hu₂T]; ring
      have htag : ∀ i : Fin (n₁ + n₂),
          u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ := by
        intro i
        by_cases hi : i.val < n₁
        · let i' : Fin n₁ := ⟨i.val, hi⟩
          have hiRep : i = Fin.castAdd n₂ i' := by
            apply Fin.ext
            simp [i']
          rw [hiRep, hleftStart i', hleftEnd i', hτleft i']
          exact htag₁ i'
        · let i' : Fin n₂ := ⟨i.val - n₁, by omega⟩
          have hiRep : i = Fin.natAdd n₁ i' := by
            apply Fin.ext
            simp [i', Fin.val_natAdd]
            omega
          rw [hiRep, hrightStart i', hrightEnd i', hτright i']
          have hp := htag₂ i'
          rcases hp with ⟨hp₁, hp₂⟩
          constructor <;> nlinarith
      have hmesh : ∀ i : Fin (n₁ + n₂), u i.succ - u i.castSucc < δ₀ := by
        intro i
        by_cases hi : i.val < n₁
        · let i' : Fin n₁ := ⟨i.val, hi⟩
          have hiRep : i = Fin.castAdd n₂ i' := by
            apply Fin.ext
            simp [i']
          rw [hiRep, hleftStart i', hleftEnd i']
          exact lt_trans (hmesh₁ i') hδ₀'
        · let i' : Fin n₂ := ⟨i.val - n₁, by omega⟩
          have hiRep : i = Fin.natAdd n₁ i' := by
            apply Fin.ext
            simp [i', Fin.val_natAdd]
            omega
          rw [hiRep, hrightStart i', hrightEnd i']
          have hm := hmesh₂ i'
          nlinarith [hm, hδ₀']
      let sumWhole : ℝ := ∑ i : Fin (n₁ + n₂),
        S (q + τ i) (q + u i.castSucc) (q + u i.succ)
      let sum₁ : ℝ := ∑ i : Fin n₁,
        S (q + τ₁ i) (q + u₁ i.castSucc) (q + u₁ i.succ)
      let sum₂ : ℝ := ∑ i : Fin n₂,
        S (s + τ₂ i) (s + u₂ i.castSucc) (s + u₂ i.succ)
      have hsum : sumWhole = sum₁ + sum₂ := by
        dsimp [sumWhole, sum₁, sum₂]
        rw [Fin.sum_univ_add]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [hleftStart i, hleftEnd i, hτleft i]
        · apply Finset.sum_congr rfl
          intro i _
          rw [hrightStart i, hrightEnd i, hτright i]
          congr 1 <;> ring
      have e₀ := H₀ (n₁ + n₂) u τ huMono hu0 huT htag hmesh
      have e₁ := H₁ n₁ u₁ τ₁ hu₁ hu₁0 hu₁T htag₁
        (fun i => lt_trans (hmesh₁ i) hδ₁')
      have e₂ := H₂ n₂ u₂ τ₂ hu₂ hu₂0 hu₂T htag₂
        (fun i => lt_trans (hmesh₂ i) hδ₂')
      have e₀' : |I - sumWhole| < ε := by
        simpa [sumWhole, abs_sub_comm] using e₀
      have e₁' : |sum₁ - I₁| < ε := by simpa [sum₁] using e₁
      have e₂' : |sum₂ - I₂| < ε := by simpa [sum₂] using e₂
      have htri : |I - (I₁ + I₂)| ≤
          |I - sumWhole| + (|sum₁ - I₁| + |sum₂ - I₂|) := by
        calc
          |I - (I₁ + I₂)| ≤ |I - sumWhole| + |sumWhole - (I₁ + I₂)| :=
            abs_sub_le I sumWhole (I₁ + I₂)
          _ = |I - sumWhole| + |(sum₁ - I₁) + (sum₂ - I₂)| := by
            rw [hsum]
            congr 1
            ring
          _ ≤ |I - sumWhole| + (|sum₁ - I₁| + |sum₂ - I₂|) := by
            have habs := abs_add_le (sum₁ - I₁) (sum₂ - I₂)
            exact add_le_add_right habs (|I - sumWhole|)
      have : |I - (I₁ + I₂)| < 3 * ε := by linarith
      dsimp [ε] at this
      linarith

#print axioms fp81s21_isRSOn_split_general

end HRS.Fp81.S21

end
