import HRS.PDE.Toolbox.CoeffL2
import HRS.Uniform.Q54Aux2

/-!
# Q54, part 3: weighted Schur bounds for matrices with off-diagonal decay

For a complex matrix `a k l` on the lattice `ℤ^d` with `‖a k l‖ ≤ A ⟨k-l⟩^{-L} ⟨l⟩^θ` and a finitely supported vector `v`
(support in `B`), at the real Sobolev index `a`:

* `weighted_E1`: `∑_{k∈S} ⟨k⟩^{2a} ‖∑_{l∈B} a k l v l‖² ≤ C ∑_{l∈B} ⟨l⟩^{2a+2θ} ‖v l‖²`  (`L > d + |a|`);
* `weighted_E2`: `∑_{k∈B}∑_{l∈B} ⟨k⟩^{2a} ‖a k l‖ ‖v k‖ ‖v l‖ ≤ C ∑_{k∈B} ⟨k⟩^{2a+θ} ‖v k‖²`  (`L > d + |a - θ/2|`).

(`⟨k⟩ = Lattice.jp k`.)  The constants depend on `(d, a, θ, L, A)` only.  This is the Fourier-symbol Schur bound of the
proof of Lemma 3.27 (TeX L2547ff).
-/

noncomputable section

open Finset

namespace HRS.Uniform.Q54

open HRS HRS.PDE

variable {d : ℕ}

theorem jp_pos' (k : Lattice d) : 0 < Lattice.jp k := Torus.jp_pos k

theorem jp_ge_one' (k : Lattice d) : 1 ≤ Lattice.jp k := Torus.jp_ge_one k

/-- Peetre's inequality for `⟨·⟩`. -/
theorem peetre_jp (e : ℝ) (k l : Lattice d) :
    Lattice.jp k ^ e ≤ (2 : ℝ) ^ (|e| / 2) * Lattice.jp l ^ e * Lattice.jp (k - l) ^ |e| := by
  have h := sobWeight_le_peetre (e / 2) k l
  rw [sobWeight_eq_jp, sobWeight_eq_jp, sobWeight_eq_jp] at h
  have e1 : 2 * (e / 2) = e := by ring
  have e2 : 2 * |e / 2| = |e| := by rw [abs_div, abs_two]; ring
  rw [e1, e2] at h
  have e3 : (2 : ℝ) ^ |e / 2| = (2 : ℝ) ^ (|e| / 2) := by rw [abs_div, abs_two]
  rw [e3] at h
  exact h

/-- the kernel `κ(m) = c ⟨m⟩^{-q}`, `q > d`, has bounded partial sums. -/
theorem kernel_partial (c q : ℝ) (hc : 0 ≤ c) (hq : (d : ℝ) < q) :
    ∃ Kκ : ℝ, 0 ≤ Kκ ∧ ∀ F : Finset (Lattice d), ∑ m ∈ F, c * Lattice.jp m ^ (-q) ≤ Kκ := by
  have hs : Summable fun k : Lattice d => Lattice.jp k ^ (-q) := by
    rw [Torus.summable_lattice_iff]
    have := HRS.summable_jp_rpow (d := d) (q / 2) (by linarith)
    refine this.congr fun k => ?_
    congr 1
    ring
  have hs' : Summable fun k : Lattice d => c * Lattice.jp k ^ (-q) := hs.mul_left c
  refine ⟨∑' k : Lattice d, c * Lattice.jp k ^ (-q), tsum_nonneg fun k => ?_, fun F => ?_⟩
  · exact mul_nonneg hc (Real.rpow_nonneg (jp_pos' k).le _)
  · exact hs'.sum_le_tsum F (fun k _ => mul_nonneg hc (Real.rpow_nonneg (jp_pos' k).le _))

theorem weighted_E1 (a θ L A : ℝ) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hL : (d : ℝ) + |a| < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Lattice d → Lattice d → ℂ)
      (hM : ∀ k l, ‖M k l‖ ≤ A * Lattice.jp (k - l) ^ (-L) * Lattice.jp l ^ θ)
      (v : Lattice d → ℂ) (B S : Finset (Lattice d)),
      ∑ k ∈ S, Lattice.jp k ^ (2 * a) * ‖∑ l ∈ B, M k l * v l‖ ^ 2 ≤
        C * ∑ l ∈ B, Lattice.jp l ^ (2 * a + 2 * θ) * ‖v l‖ ^ 2 := by
  obtain ⟨Kκ, hK0, hK⟩ := kernel_partial (A * (2 : ℝ) ^ (|a| / 2)) (L - |a|) (by positivity)
    (by linarith)
  refine ⟨Kκ ^ 2, by positivity, fun M hM v B S => ?_⟩
  set κ : Lattice d → ℝ := fun m => A * (2 : ℝ) ^ (|a| / 2) * Lattice.jp m ^ (-(L - |a|)) with hκ
  have hκ0 : ∀ m, 0 ≤ κ m := fun m => mul_nonneg (by positivity)
    (Real.rpow_nonneg (jp_pos' m).le _)
  set y : Lattice d → ℝ := fun l => Lattice.jp l ^ (a + θ) * ‖v l‖ with hy
  have hy0 : ∀ l, 0 ≤ y l := fun l => mul_nonneg (Real.rpow_nonneg (jp_pos' l).le _) (norm_nonneg _)
  have hpt : ∀ k, Lattice.jp k ^ a * ‖∑ l ∈ B, M k l * v l‖ ≤ ∑ l ∈ B, κ (k - l) * y l := by
    intro k
    calc Lattice.jp k ^ a * ‖∑ l ∈ B, M k l * v l‖
        ≤ Lattice.jp k ^ a * ∑ l ∈ B, ‖M k l‖ * ‖v l‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (jp_pos' k).le _)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          rw [norm_mul]
      _ = ∑ l ∈ B, Lattice.jp k ^ a * (‖M k l‖ * ‖v l‖) := by rw [Finset.mul_sum]
      _ ≤ ∑ l ∈ B, κ (k - l) * y l := by
          refine Finset.sum_le_sum fun l _ => ?_
          have hP := peetre_jp a k l
          have hjl := jp_pos' l
          have hjkl := jp_pos' (k - l)
          have h1 : Lattice.jp k ^ a * (‖M k l‖ * ‖v l‖) ≤
              (2 : ℝ) ^ (|a| / 2) * Lattice.jp l ^ a * Lattice.jp (k - l) ^ |a| *
                ((A * Lattice.jp (k - l) ^ (-L) * Lattice.jp l ^ θ) * ‖v l‖) := by
            calc Lattice.jp k ^ a * (‖M k l‖ * ‖v l‖)
                ≤ ((2 : ℝ) ^ (|a| / 2) * Lattice.jp l ^ a * Lattice.jp (k - l) ^ |a|) *
                  ((A * Lattice.jp (k - l) ^ (-L) * Lattice.jp l ^ θ) * ‖v l‖) := by
                  refine mul_le_mul hP (mul_le_mul_of_nonneg_right (hM k l) (norm_nonneg _))
                    (by positivity) (by positivity)
              _ = _ := by ring
          refine h1.trans (le_of_eq ?_)
          simp only [hκ, hy]
          have e1 : Lattice.jp (k - l) ^ |a| * Lattice.jp (k - l) ^ (-L) =
              Lattice.jp (k - l) ^ (-(L - |a|)) := by
            rw [← Real.rpow_add hjkl]; congr 1; ring
          have e2 : Lattice.jp l ^ a * Lattice.jp l ^ θ = Lattice.jp l ^ (a + θ) := by
            rw [← Real.rpow_add hjl]
          calc (2 : ℝ) ^ (|a| / 2) * Lattice.jp l ^ a * Lattice.jp (k - l) ^ |a| *
                ((A * Lattice.jp (k - l) ^ (-L) * Lattice.jp l ^ θ) * ‖v l‖)
              = A * (2 : ℝ) ^ (|a| / 2) * (Lattice.jp (k - l) ^ |a| * Lattice.jp (k - l) ^ (-L)) *
                  ((Lattice.jp l ^ a * Lattice.jp l ^ θ) * ‖v l‖) := by ring
            _ = _ := by rw [e1, e2]
  have hsq := schur_sq_finite κ y hκ0 hy0 Kκ hK S B
  calc ∑ k ∈ S, Lattice.jp k ^ (2 * a) * ‖∑ l ∈ B, M k l * v l‖ ^ 2
      = ∑ k ∈ S, (Lattice.jp k ^ a * ‖∑ l ∈ B, M k l * v l‖) ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_pow, Torus.jp_rpow_sq]
    _ ≤ ∑ k ∈ S, (∑ l ∈ B, κ (k - l) * y l) ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (jp_pos' k).le _) (norm_nonneg _))
          (hpt k) 2
    _ ≤ Kκ ^ 2 * ∑ l ∈ B, y l ^ 2 := hsq
    _ = Kκ ^ 2 * ∑ l ∈ B, Lattice.jp l ^ (2 * a + 2 * θ) * ‖v l‖ ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [hy]
        rw [mul_pow, Torus.jp_rpow_sq]
        congr 2
        ring

theorem weighted_E2 (a θ L A : ℝ) (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hL : (d : ℝ) + |a - θ / 2| < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Lattice d → Lattice d → ℂ)
      (hM : ∀ k l, ‖M k l‖ ≤ A * Lattice.jp (k - l) ^ (-L) * Lattice.jp l ^ θ)
      (v : Lattice d → ℂ) (B : Finset (Lattice d)),
      ∑ k ∈ B, ∑ l ∈ B, Lattice.jp k ^ (2 * a) * ‖M k l‖ * ‖v k‖ * ‖v l‖ ≤
        C * ∑ k ∈ B, Lattice.jp k ^ (2 * a + θ) * ‖v k‖ ^ 2 := by
  set e : ℝ := a - θ / 2 with he
  obtain ⟨Kκ, hK0, hK⟩ := kernel_partial (A * (2 : ℝ) ^ (|e| / 2)) (L - |e|) (by positivity)
    (by linarith)
  refine ⟨Kκ, hK0, fun M hM v B => ?_⟩
  set κ : Lattice d → ℝ := fun m => A * (2 : ℝ) ^ (|e| / 2) * Lattice.jp m ^ (-(L - |e|)) with hκ
  have hκ0 : ∀ m, 0 ≤ κ m := fun m => mul_nonneg (by positivity)
    (Real.rpow_nonneg (jp_pos' m).le _)
  set x : Lattice d → ℝ := fun k => Lattice.jp k ^ (a + θ / 2) * ‖v k‖ with hx
  have hx0 : ∀ k, 0 ≤ x k := fun k => mul_nonneg (Real.rpow_nonneg (jp_pos' k).le _) (norm_nonneg _)
  have hform := schur_form_finite κ x hκ0 hx0 Kκ hK B
  calc ∑ k ∈ B, ∑ l ∈ B, Lattice.jp k ^ (2 * a) * ‖M k l‖ * ‖v k‖ * ‖v l‖
      ≤ ∑ k ∈ B, ∑ l ∈ B, κ (k - l) * x k * x l := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
        have hP := peetre_jp e k l
        have hjl := jp_pos' l
        have hjk := jp_pos' k
        have hjkl := jp_pos' (k - l)
        -- jp k ^ e / jp l ^ e ≤ 2^(|e|/2) jp (k-l)^|e|
        have hP' : Lattice.jp k ^ e * Lattice.jp l ^ (-e) ≤
            (2 : ℝ) ^ (|e| / 2) * Lattice.jp (k - l) ^ |e| := by
          have hl : Lattice.jp l ^ e * Lattice.jp l ^ (-e) = 1 := by
            rw [← Real.rpow_add hjl]; simp
          calc Lattice.jp k ^ e * Lattice.jp l ^ (-e)
              ≤ ((2 : ℝ) ^ (|e| / 2) * Lattice.jp l ^ e * Lattice.jp (k - l) ^ |e|) *
                  Lattice.jp l ^ (-e) := by
                exact mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hjl.le _)
            _ = (2 : ℝ) ^ (|e| / 2) * Lattice.jp (k - l) ^ |e| * (Lattice.jp l ^ e * Lattice.jp l ^ (-e)) := by
                ring
            _ = _ := by rw [hl, mul_one]
        have hid : Lattice.jp k ^ (2 * a) * Lattice.jp l ^ θ =
            (Lattice.jp k ^ (a + θ / 2) * Lattice.jp l ^ (a + θ / 2)) *
              (Lattice.jp k ^ e * Lattice.jp l ^ (-e)) := by
          rw [show Lattice.jp k ^ (2 * a) = Lattice.jp k ^ (a + θ / 2) * Lattice.jp k ^ e by
                rw [← Real.rpow_add hjk]; congr 1; rw [he]; ring,
              show Lattice.jp l ^ θ = Lattice.jp l ^ (a + θ / 2) * Lattice.jp l ^ (-e) by
                rw [← Real.rpow_add hjl]; congr 1; rw [he]; ring]
          ring
        have hnn : 0 ≤ ‖v k‖ * ‖v l‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc Lattice.jp k ^ (2 * a) * ‖M k l‖ * ‖v k‖ * ‖v l‖
            = Lattice.jp k ^ (2 * a) * (‖M k l‖ * (‖v k‖ * ‖v l‖)) := by ring
          _ ≤ Lattice.jp k ^ (2 * a) * ((A * Lattice.jp (k - l) ^ (-L) * Lattice.jp l ^ θ) *
                (‖v k‖ * ‖v l‖)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hM k l) hnn)
                (Real.rpow_nonneg hjk.le _)
          _ = A * Lattice.jp (k - l) ^ (-L) * ((Lattice.jp k ^ (2 * a) * Lattice.jp l ^ θ) *
                (‖v k‖ * ‖v l‖)) := by ring
          _ = A * Lattice.jp (k - l) ^ (-L) * (((Lattice.jp k ^ (a + θ / 2) * Lattice.jp l ^ (a + θ / 2)) *
                (Lattice.jp k ^ e * Lattice.jp l ^ (-e))) * (‖v k‖ * ‖v l‖)) := by rw [hid]
          _ = A * Lattice.jp (k - l) ^ (-L) * ((Lattice.jp k ^ e * Lattice.jp l ^ (-e)) *
                (x k * x l)) := by simp only [hx]; ring
          _ ≤ A * Lattice.jp (k - l) ^ (-L) * (((2 : ℝ) ^ (|e| / 2) * Lattice.jp (k - l) ^ |e|) *
                (x k * x l)) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP' (mul_nonneg (hx0 k) (hx0 l)))
                (by positivity)
          _ = κ (k - l) * x k * x l := by
              simp only [hκ]
              have e1 : Lattice.jp (k - l) ^ |e| * Lattice.jp (k - l) ^ (-L) =
                  Lattice.jp (k - l) ^ (-(L - |e|)) := by
                rw [← Real.rpow_add hjkl]; congr 1; ring
              calc A * Lattice.jp (k - l) ^ (-L) * ((2 : ℝ) ^ (|e| / 2) * Lattice.jp (k - l) ^ |e| *
                    (x k * x l))
                  = A * (2 : ℝ) ^ (|e| / 2) * (Lattice.jp (k - l) ^ |e| * Lattice.jp (k - l) ^ (-L)) *
                      x k * x l := by ring
                _ = _ := by rw [e1]
    _ ≤ Kκ * ∑ k ∈ B, x k ^ 2 := hform
    _ = Kκ * ∑ k ∈ B, Lattice.jp k ^ (2 * a + θ) * ‖v k‖ ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hx]
        rw [mul_pow, Torus.jp_rpow_sq]
        congr 2
        ring

end HRS.Uniform.Q54
