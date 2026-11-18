import HRS.MC.CepE4Aux1

/-!
# Packet CEPE6, auxiliary 1: the pair forces are controlled by `‖∇Φ‖₁` on the alcove

For `z` in the open alcove, `∑_{k<l} |π cot(π(z_l - z_k))| ≤ C (‖∇Φ(z)‖₁ + 1)` with `C = 4N²/a + 8πN⁴`, and
each single term obeys the same bound (the wrap-around pair `(0, N-1)` included).

Route.  `∑_i ∂_iΦ = 0` (translation invariance), so `⟨z - ρ, ∇Φ⟩ = ⟨(z - ρ) - (z_0 - ρ_0)·1, ∇Φ⟩ ≤ ‖∇Φ‖₁`
because `|(z_k - ρ_k) - (z_0 - ρ_0)| < 1`; the pairwise inequality of `e4_pair` sums to
`2 ∑_{k<l}|h₁(d_{kl})| ≤ 8N ⟨z - ρ, ∇Φ⟩ + 16πN³a`.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6

open HRS.MC.Cepa HRS.MC.CepE4

theorem e6_pair_sum_le {a : ℝ} (ha : 0 < a) {N : ℕ} {x : Ch N} (hx : x ∈ cep_Alcove N) :
    2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then |HRS.MC.CepE1.cepe1_h1 a N (x l - x k)| else 0) ≤
      8 * N * inner ℝ (x - e4_rho N) (gradient (cep_chamberPot a N) x) +
        16 * Real.pi * N * a * (N : ℝ) ^ 2 := by
  have hz : ∀ k l : Fin N, k < l → 0 < x l - x k ∧ x l - x k < 1 :=
    fun k l hkl => ⟨by linarith [hx.1 k l hkl], by linarith [hx.2 k l]⟩
  have hg : gradient (cep_chamberPot a N) x =
      HRS.MC.CepE1.cepe1_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) x :=
    (e4_Phi_hasGradient hz).gradient
  rw [hg, real_inner_comm, e4_inner_pairGrad]
  have hpair : ∀ k l : Fin N, k < l →
      2 * |HRS.MC.CepE1.cepe1_h1 a N (x l - x k)| ≤
        8 * N * (HRS.MC.CepE1.cepe1_h1 a N (x l - x k) * ((x - e4_rho N) l - (x - e4_rho N) k)) +
          16 * Real.pi * N * a := by
    intro k l hkl
    have hN : 2 ≤ N := by
      have := k.2; have := l.2; have : (k : ℕ) < l := hkl; omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hkl' : (k : ℕ) + 1 ≤ l := hkl
    have hlN : (l : ℕ) < N := l.2
    set e : ℝ := ((l : ℕ) - (k : ℕ) : ℝ) / N with he
    have hdiff : (x - e4_rho N) l - (x - e4_rho N) k = (x l - x k) - e := by
      simp only [e4_rho, WithLp.ofLp_sub, Pi.sub_apply, he]
      ring
    have h1 : (1 : ℝ) / N ≤ e := by
      rw [he]; apply div_le_div_of_nonneg_right _ hNr.le
      have : ((k : ℕ) : ℝ) + 1 ≤ (l : ℕ) := by exact_mod_cast hkl'
      linarith
    have h2 : e ≤ 1 - 1 / (N : ℝ) := by
      rw [he, show (1 : ℝ) - 1 / N = ((N : ℝ) - 1) / N by field_simp]
      apply div_le_div_of_nonneg_right _ hNr.le
      have : ((l : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hlN
      have : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
      linarith
    rw [hdiff]
    exact (e4_pair ha hN h1 h2 (hz k l hkl).1 (hz k l hkl).2).2
  have hcard : ∀ c : ℝ, (∑ _k : Fin N, ∑ _l : Fin N, c) = (N : ℝ) ^ 2 * c := by
    intro c; simp; ring
  calc 2 * ∑ k : Fin N, ∑ l : Fin N, (if k < l then |HRS.MC.CepE1.cepe1_h1 a N (x l - x k)| else 0)
      = ∑ k : Fin N, ∑ l : Fin N, 2 * (if k < l then |HRS.MC.CepE1.cepe1_h1 a N (x l - x k)| else 0) := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ k : Fin N, ∑ l : Fin N, (8 * N * (if k < l then HRS.MC.CepE1.cepe1_h1 a N (x l - x k) *
          ((x - e4_rho N) l - (x - e4_rho N) k) else 0) + 16 * Real.pi * N * a) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        by_cases hkl : k < l
        · simp only [hkl, ite_true]; exact hpair k l hkl
        · simp only [hkl, ite_false, mul_zero, zero_add]; positivity
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hcard]; ring

/-- `⟨z - ρ, ∇Φ(z)⟩ ≤ ‖∇Φ(z)‖₁` on the alcove (translation invariance and `|Δ(z - ρ)| < 1`). -/
theorem e6_inner_le {a : ℝ} {N : ℕ} {x : Ch N} (hx : x ∈ cep_Alcove N) :
    inner ℝ (x - e4_rho N) (gradient (cep_chamberPot a N) x) ≤
      ∑ i, |(gradient (cep_chamberPot a N) x) i| := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [show x - e4_rho 0 = 0 from Subsingleton.elim _ _]
    simp
  have hz : ∀ k l : Fin N, k < l → 0 < x l - x k ∧ x l - x k < 1 :=
    fun k l hkl => ⟨by linarith [hx.1 k l hkl], by linarith [hx.2 k l]⟩
  have hg : gradient (cep_chamberPot a N) x =
      HRS.MC.CepE1.cepe1_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) x :=
    (e4_Phi_hasGradient hz).gradient
  set g := gradient (cep_chamberPot a N) x with hgdef
  let i0 : Fin N := ⟨0, hN⟩
  set c : ℝ := (x - e4_rho N) i0 with hc
  -- the sum of the coordinates of the gradient vanishes
  have hsum : ∑ i, g i = 0 := by
    have h1 := e4_inner_pairGrad (HRS.MC.CepE1.cepe1_h1 a N) x
      (WithLp.toLp 2 fun _ : Fin N => (1 : ℝ))
    rw [← hg] at h1
    have h2 : inner ℝ g (WithLp.toLp 2 fun _ : Fin N => (1 : ℝ)) = ∑ i, g i := by
      simp [PiLp.inner_apply]
    rw [h2] at h1
    rw [h1]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    split_ifs <;> simp
  have hshift : inner ℝ (x - e4_rho N) g = ∑ i, g i * ((x - e4_rho N) i - c) := by
    have : inner ℝ (x - e4_rho N) g = ∑ i, g i * (x - e4_rho N) i := by
      simp [PiLp.inner_apply, mul_comm]
    rw [this]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
  rw [hshift]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb : |(x - e4_rho N) i - c| ≤ 1 := by
    have hρ : ∀ j : Fin N, 0 ≤ (e4_rho N) j ∧ (e4_rho N) j < 1 := by
      intro j
      refine ⟨by simp [e4_rho]; positivity, ?_⟩
      simp only [e4_rho]
      rw [div_lt_one (by exact_mod_cast hN)]
      exact_mod_cast j.2
    have hxd : ∀ j : Fin N, 0 ≤ x j - x i0 ∧ x j - x i0 < 1 := by
      intro j
      rcases eq_or_ne j i0 with h | h
      · subst h; simp
      · have hlt : i0 < j := Fin.lt_def.2 (by
          have : j.val ≠ 0 := fun h0 => h (Fin.ext h0)
          show 0 < j.val
          omega)
        exact ⟨(hz i0 j hlt).1.le, (hz i0 j hlt).2⟩
    have e1 : (x - e4_rho N) i - c = (x i - x i0) - ((e4_rho N) i - (e4_rho N) i0) := by
      simp only [hc, WithLp.ofLp_sub, Pi.sub_apply]; ring
    have hρ0 : (e4_rho N) i0 = 0 := by simp [e4_rho, i0]
    rw [e1, abs_le]
    have := hxd i; have := hρ i; have := hρ i0
    constructor <;> linarith
  calc g i * ((x - e4_rho N) i - c) ≤ |g i * ((x - e4_rho N) i - c)| := le_abs_self _
    _ = |g i| * |(x - e4_rho N) i - c| := abs_mul _ _
    _ ≤ |g i| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = |g i| := mul_one _

/-- **Pair forces are controlled by the total singular force** on the open alcove: with `C = 4N²/a + 8πN⁴`,
`∑_{k<l}|π cot(π(z_l - z_k))| ≤ C (‖∇Φ(z)‖₁ + 1)`, and each single term `|π cot(π(z_l - z_k))|` (`k < l`,
the wrap-around pair `(0, N-1)` included) obeys the same bound. -/
theorem cep_pair_cot_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Ch N, z ∈ cep_Alcove N →
      (∑ k : Fin N, ∑ l : Fin N, (if k < l then
          |Real.pi * (Real.cos (Real.pi * (z l - z k)) / Real.sin (Real.pi * (z l - z k)))| else 0)
        ≤ C * (∑ i, |(gradient (cep_chamberPot a N) z) i| + 1)) ∧
      ∀ k l : Fin N, k < l →
        |Real.pi * (Real.cos (Real.pi * (z l - z k)) / Real.sin (Real.pi * (z l - z k)))|
          ≤ C * (∑ i, |(gradient (cep_chamberPot a N) z) i| + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨0, le_rfl, fun z _ => ⟨by simp, fun k => k.elim0⟩⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨4 * (N : ℝ) ^ 2 / a + 8 * Real.pi * (N : ℝ) ^ 4, by positivity, fun z hz => ?_⟩
  have hs := e6_pair_sum_le ha hz
  have hi := e6_inner_le (a := a) hz
  have hP := (e4_pointwise ha hz).1
  set S : ℝ := ∑ k : Fin N, ∑ l : Fin N,
    (if k < l then |HRS.MC.CepE1.cepe1_h1 a N (z l - z k)| else 0) with hS
  set G : ℝ := ∑ i, |(gradient (cep_chamberPot a N) z) i| with hG
  have hS' : S ≤ 4 * N * G + 8 * Real.pi * N * a * (N : ℝ) ^ 2 := by nlinarith
  -- conversion: |π cot| = (N / a) * |h₁|
  have hconv : ∀ d : ℝ, |Real.pi * (Real.cos (Real.pi * d) / Real.sin (Real.pi * d))| =
      (N / a) * |HRS.MC.CepE1.cepe1_h1 a N d| := by
    intro d
    unfold HRS.MC.CepE1.cepe1_h1
    rw [abs_mul (a / N), abs_neg, abs_mul Real.pi, abs_of_pos (show 0 < a / N by positivity)]
    field_simp
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCbound : (N / a) * (4 * N * G + 8 * Real.pi * N * a * (N : ℝ) ^ 2) ≤
      (4 * (N : ℝ) ^ 2 / a + 8 * Real.pi * (N : ℝ) ^ 4) * (G + 1) := by
    have e1 : (N / a) * (4 * N * G + 8 * Real.pi * N * a * (N : ℝ) ^ 2) =
        4 * (N : ℝ) ^ 2 / a * G + 8 * Real.pi * (N : ℝ) ^ 4 := by
      field_simp
    rw [e1]
    have : 0 ≤ 4 * (N : ℝ) ^ 2 / a := by positivity
    have : 0 ≤ 8 * Real.pi * (N : ℝ) ^ 4 := by positivity
    nlinarith
  have hsum : (∑ k : Fin N, ∑ l : Fin N, (if k < l then
          |Real.pi * (Real.cos (Real.pi * (z l - z k)) / Real.sin (Real.pi * (z l - z k)))| else 0)) =
      (N / a) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · exact hconv _
    · simp
  have hNa : 0 ≤ (N : ℝ) / a := by positivity
  constructor
  · rw [hsum]
    exact (mul_le_mul_of_nonneg_left hS' hNa).trans hCbound
  · intro k l hkl
    have hterm : |HRS.MC.CepE1.cepe1_h1 a N (z l - z k)| ≤ S := by
      rw [hS]
      calc |HRS.MC.CepE1.cepe1_h1 a N (z l - z k)|
          = ∑ l' : Fin N, (if k < l' then |HRS.MC.CepE1.cepe1_h1 a N (z l' - z k)| else 0) -
            ∑ l' ∈ Finset.univ.erase l, (if k < l' then |HRS.MC.CepE1.cepe1_h1 a N (z l' - z k)| else 0) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
            simp [hkl]
        _ ≤ ∑ l' : Fin N, (if k < l' then |HRS.MC.CepE1.cepe1_h1 a N (z l' - z k)| else 0) := by
            have : 0 ≤ ∑ l' ∈ Finset.univ.erase l,
                (if k < l' then |HRS.MC.CepE1.cepe1_h1 a N (z l' - z k)| else 0) :=
              Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
            linarith
        _ ≤ _ := by
            refine Finset.single_le_sum (f := fun k' : Fin N => ∑ l' : Fin N,
              (if k' < l' then |HRS.MC.CepE1.cepe1_h1 a N (z l' - z k')| else 0))
              (fun k' _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ k)
    rw [hconv]
    exact (mul_le_mul_of_nonneg_left (hterm.trans hS') hNa).trans hCbound

end HRS.MC.CepE6
