import HRS.MC.CepE5bAux3

/-!
# Packet CEPE5B, auxiliary 4: pointwise bound of the Hessian trace by the Lyapunov functional

With `y = J_n z`, `Q_n(z) = ⟨z - ρ, G_n z⟩`, `W(y) = ∑_{k<l} |h1(y_l - y_k)|` and `r ∈ (0, 1/2]`:
`(1/n) tr D²Φ_n(z) ≤ ∑_p min(N, (2/n) h1'(y_p)) ≤ c₁ r Q_n(z) + c₂ r + c₃ /(n r²)`.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE1 (cepe1_h1 cepe1_pairGrad cepe1_vec cepe1_inner_vec)
open HRS.MC.CepE4 (e4_rho e4_pair e4_inner_pairGrad)

variable {N : ℕ} {a : ℝ} {J : ℝ → Ch N → Ch N}

/-- `∑_{k<l} 2 |h1| ≤ 8N Q + K`: the pair-sum form of the Lyapunov inequality. -/
theorem e5b_pairSum (ha : 0 < a) {x : Ch N} (hx : x ∈ cep_Alcove N) :
    ∑ k : Fin N, ∑ l : Fin N, (if k < l then 2 * |cepe1_h1 a N (x l - x k)| else 0) ≤
      8 * N * inner ℝ (x - e4_rho N) (e5b_pg a N x) + 16 * Real.pi * N * a * (N : ℝ) ^ 2 := by
  have hpair : ∀ k l : Fin N, k < l →
      2 * |cepe1_h1 a N (x l - x k)| ≤
        8 * N * (cepe1_h1 a N (x l - x k) * ((x - e4_rho N) l - (x - e4_rho N) k)) + 16 * Real.pi * N * a := by
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
    have hg := e5b_gap hx hkl
    exact (e4_pair ha hN h1 h2 hg.1 hg.2).2
  rw [real_inner_comm, e4_inner_pairGrad]
  have hcard : ∀ c : ℝ, (∑ _k : Fin N, ∑ _l : Fin N, c) = (N : ℝ) ^ 2 * c := by
    intro c; simp; ring
  calc ∑ k : Fin N, ∑ l : Fin N, (if k < l then 2 * |cepe1_h1 a N (x l - x k)| else 0)
      ≤ ∑ k : Fin N, ∑ l : Fin N, (8 * N * (if k < l then cepe1_h1 a N (x l - x k) *
            ((x - e4_rho N) l - (x - e4_rho N) k) else 0) + 16 * Real.pi * N * a) := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        by_cases hkl : k < l
        · simp only [hkl, ite_true]; exact hpair k l hkl
        · simp only [hkl, ite_false, mul_zero, zero_add]; positivity
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hcard]; ring

/-- Sum over pairs of the absolute force profile. -/
def e5b_W (a : ℝ) (N : ℕ) (y : Ch N) : ℝ :=
  ∑ k : Fin N, ∑ l : Fin N, if k < l then |cepe1_h1 a N (y l - y k)| else 0

theorem e5b_W_nonneg (a : ℝ) (y : Ch N) : 0 ≤ e5b_W a N y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem e5b_W_le (ha : 0 < a) {y : Ch N} (hy : y ∈ cep_Alcove N) :
    e5b_W a N y ≤ 4 * N * inner ℝ (y - e4_rho N) (e5b_pg a N y) + 8 * Real.pi * N * a * (N : ℝ) ^ 2 := by
  have h := e5b_pairSum ha hy
  have e : ∑ k : Fin N, ∑ l : Fin N, (if k < l then 2 * |cepe1_h1 a N (y l - y k)| else 0) =
      2 * e5b_W a N y := by
    unfold e5b_W
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> ring
  rw [e] at h
  linarith

/-- Pair-wise cutoff estimate. -/
theorem e5b_pair_min {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N) {n r d : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hr2 : r ≤ 1 / 2) (hd : d ∈ Ioo (0 : ℝ) 1) :
    min (N : ℝ) (2 / n * e5b_h1' a N d) ≤
      N * (2 * N * r / (a * Real.pi)) * |cepe1_h1 a N d| + 2 * a * Real.pi ^ 2 / (N * n * r ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hs : 0 < Real.sin (Real.pi * d) := HRS.MC.CepE2.cepe2_sin_pos hd
  set s := Real.sin (Real.pi * d) with hsdef
  set c := Real.cos (Real.pi * d) with hcdef
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hpos : 0 ≤ N * (2 * N * r / (a * Real.pi)) * |cepe1_h1 a N d| := by positivity
  have hpos2 : 0 < 2 * a * Real.pi ^ 2 / (N * n * r ^ 2) := by positivity
  by_cases hsr : r ≤ s
  · have h1 : 2 / n * e5b_h1' a N d ≤ 2 * a * Real.pi ^ 2 / (N * n * r ^ 2) := by
      unfold e5b_h1'
      have h2 : Real.pi ^ 2 / s ^ 2 ≤ Real.pi ^ 2 / r ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      calc 2 / n * (a / N * (Real.pi ^ 2 / s ^ 2)) ≤ 2 / n * (a / N * (Real.pi ^ 2 / r ^ 2)) := by gcongr
        _ = _ := by field_simp
    exact (min_le_right _ _).trans (by linarith)
  · push_neg at hsr
    have hc2 : 1 / 4 ≤ c ^ 2 := by nlinarith
    have hc : 1 / 2 ≤ |c| := by
      have : (1 / 2 : ℝ) ^ 2 ≤ |c| ^ 2 := by rw [sq_abs]; nlinarith
      exact le_of_sq_le_sq (by simpa using this) (abs_nonneg c)
    have hh : |cepe1_h1 a N d| = a / N * (Real.pi * (|c| / s)) := by
      unfold cepe1_h1
      rw [abs_mul, abs_of_pos (by positivity : 0 < a / N), abs_neg, abs_mul, abs_of_pos hpi, abs_div,
        abs_of_pos hs]
    have h3 : (N : ℝ) ≤ N * (2 * N * r / (a * Real.pi)) * |cepe1_h1 a N d| := by
      rw [hh]
      have : N * (2 * N * r / (a * Real.pi)) * (a / N * (Real.pi * (|c| / s))) = N * (2 * r * |c| / s) := by
        field_simp
      rw [this]
      have h4 : 1 ≤ 2 * r * |c| / s := by
        rw [le_div_iff₀ hs]; nlinarith
      nlinarith
    exact (min_le_left _ _).trans (by linarith)

end HRS.MC.CepE5b
