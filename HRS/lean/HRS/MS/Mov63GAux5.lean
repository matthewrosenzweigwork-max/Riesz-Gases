import HRS.MS.Mov63GAux4

/-!
# S6.3, packet N8 (part 5): the Bernstein quantities `S_m = ∑_{|σ|=m} (∂_σ Q)²`

Namespace `HRS.MS.Mov63`, prefix `mng_`.  See `Mov63GAux1`.

* `mngS Q m`: `S_m(t,x) = ∑_{σ ∈ (Fin d)^m} (∂_σ Q)²` (sum over `List.Vector (Fin d) m`); `mngS_succ`: `S_{m+1} = ∑_σ ∑_k (∂_k ∂_σ Q)²`.
* `mngSx Q n`: `∑_{k=1}^n S_k`; `mngJn_sq_le`: `J_n² ≤ n d^n ∑_{k=1}^n S_k`.
* **`mng_S_eq`**: for `1 ≤ m ≤ N`: `∂_t S_m = νΔS_m + ⟨b,∇S_m⟩ + 2 A S_m + 2 T_m - 2ν S_{m+1}` (right derivative on `[0,∞)`),
  with `S_m ∈ C²`, `S_m` jointly continuous, and `2|T_m| ≤ S_m + C (Sx_m + a²)`.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS

variable {d : ℕ}

/-- `S_m = ∑_{σ} (∂_σ Q)²`. -/
def mngS (Q : ℝ → Euc d → ℝ) (m : ℕ) : ℝ → Euc d → ℝ :=
  fun t x => ∑ v : List.Vector (Fin d) m, mngJt Q v.toList t x * mngJt Q v.toList t x

/-- `∑_{k=1}^n S_k`. -/
def mngSx (Q : ℝ → Euc d → ℝ) (n : ℕ) : ℝ → Euc d → ℝ :=
  fun t x => ∑ m ∈ Finset.range n, mngS Q (m + 1) t x

lemma mngS_nonneg (Q : ℝ → Euc d → ℝ) (m : ℕ) (t : ℝ) (x : Euc d) : 0 ≤ mngS Q m t x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma mngSx_nonneg (Q : ℝ → Euc d → ℝ) (n : ℕ) (t : ℝ) (x : Euc d) : 0 ≤ mngSx Q n t x :=
  Finset.sum_nonneg fun _ _ => mngS_nonneg _ _ _ _

lemma mngS_succ (Q : ℝ → Euc d → ℝ) (m : ℕ) (t : ℝ) (x : Euc d) :
    mngS Q (m + 1) t x = ∑ v : List.Vector (Fin d) m, ∑ k : Fin d,
      mngPd k (mngJt Q v.toList) t x * mngPd k (mngJt Q v.toList) t x := by
  classical
  unfold mngS
  let e : List.Vector (Fin d) (m + 1) ≃ Fin d × List.Vector (Fin d) m :=
    { toFun := fun w => (w.head, w.tail)
      invFun := fun p => List.Vector.cons p.1 p.2
      left_inv := fun w => List.Vector.cons_head_tail w
      right_inv := fun p => by simp }
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => ?_
  simp [e, List.Vector.toList_cons, mngJt]

lemma mngJn_sq_le (hd : 1 ≤ d) (Q : ℝ → Euc d → ℝ) (n : ℕ) (t : ℝ) (x : Euc d) :
    mngJn Q n t x ^ 2 ≤ n * (d : ℝ) ^ n * mngSx Q n t x := by
  unfold mngJn mngSx
  have hY : ∀ m ∈ Finset.range n, (∑ v : List.Vector (Fin d) (m + 1), |mngJt Q v.toList t x|) ^ 2 ≤
      (d : ℝ) ^ n * mngS Q (m + 1) t x := by
    intro m hm
    have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (List.Vector (Fin d) (m + 1))))
      (f := fun v => |mngJt Q v.toList t x|)
    have hc : (Finset.univ : Finset (List.Vector (Fin d) (m + 1))).card = d ^ (m + 1) := by
      simp [Finset.card_univ, card_vector]
    rw [hc] at h1
    have h2 : (d : ℝ) ^ (m + 1) ≤ (d : ℝ) ^ n := by
      refine pow_le_pow_right₀ (by exact_mod_cast hd) ?_
      have := Finset.mem_range.1 hm; omega
    have h3 : (∑ v : List.Vector (Fin d) (m + 1), |mngJt Q v.toList t x| ^ 2) = mngS Q (m + 1) t x := by
      unfold mngS; refine Finset.sum_congr rfl fun v _ => ?_; rw [sq_abs, sq]
    rw [h3] at h1
    refine h1.trans ?_
    have := mngS_nonneg Q (m + 1) t x
    push_cast at h1 ⊢
    exact mul_le_mul_of_nonneg_right h2 this
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range n)
    (f := fun m => ∑ v : List.Vector (Fin d) (m + 1), |mngJt Q v.toList t x|)
  rw [Finset.card_range] at h1
  refine h1.trans ?_
  have : ∑ m ∈ Finset.range n, (∑ v : List.Vector (Fin d) (m + 1), |mngJt Q v.toList t x|) ^ 2 ≤
      ∑ m ∈ Finset.range n, (d : ℝ) ^ n * mngS Q (m + 1) t x := Finset.sum_le_sum hY
  rw [← Finset.mul_sum] at this
  calc (n : ℝ) * ∑ m ∈ Finset.range n, (∑ v : List.Vector (Fin d) (m + 1), |mngJt Q v.toList t x|) ^ 2
      ≤ n * ((d : ℝ) ^ n * ∑ m ∈ Finset.range n, mngS Q (m + 1) t x) :=
        mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
    _ = _ := by ring
section SumSq

variable {ι : Type*} [Fintype ι]

/-- The family `∑_v u_v²`. -/
def mngSq (u : ι → ℝ → Euc d → ℝ) : ℝ → Euc d → ℝ := fun t x => ∑ v, u v t x * u v t x

/-- The drift as a vector field. -/
def mngBv (b : Fin d → ℝ → Euc d → ℝ) (t : ℝ) (x : Euc d) : Euc d := WithLp.toLp 2 (fun k => b k t x)

lemma mngSq_pd (u : ι → ℝ → Euc d → ℝ) (hu : ∀ v t, Differentiable ℝ (u v t)) (k : Fin d) :
    mngPd k (mngSq u) = fun t x => ∑ v, (mngPd k (u v) t x * u v t x + u v t x * mngPd k (u v) t x) := by
  unfold mngSq
  rw [mng_pd_sum Finset.univ (f := fun v t x => u v t x * u v t x) (fun v t => (hu v t).mul (hu v t)) k]
  funext t x
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mng_pd_mul (f := u v) (g := u v) (hu v) (hu v) k]

lemma mngSq_pd2 (u : ι → ℝ → Euc d → ℝ) (hu : ∀ v t, ContDiff ℝ 2 (u v t)) (k : Fin d) :
    mngPd k (mngPd k (mngSq u)) = fun t x => ∑ v, (2 * (mngPd k (mngPd k (u v)) t x * u v t x) +
      2 * (mngPd k (u v) t x * mngPd k (u v) t x)) := by
  have hd : ∀ v t, Differentiable ℝ (u v t) := fun v t => (hu v t).differentiable (by norm_num)
  have hd1 : ∀ v t, ContDiff ℝ 1 (mngPd k (u v) t) := fun v t => mng_cd_pd (hu v t) k
  have hd1' : ∀ v t, Differentiable ℝ (mngPd k (u v) t) := fun v t => (hd1 v t).differentiable (by norm_num)
  rw [mngSq_pd u hd k]
  rw [mng_pd_sum Finset.univ (f := fun v t x => mngPd k (u v) t x * u v t x + u v t x * mngPd k (u v) t x)
    (fun v t => ((hd1' v t).mul (hd v t)).add ((hd v t).mul (hd1' v t))) k]
  funext t x
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mng_pd_add (f := fun t x => mngPd k (u v) t x * u v t x) (g := fun t x => u v t x * mngPd k (u v) t x)
    (fun t => (hd1' v t).mul (hd v t)) (fun t => (hd v t).mul (hd1' v t)) k]
  simp only
  rw [mng_pd_mul (f := mngPd k (u v)) (g := u v) (hd1' v) (hd v) k,
    mng_pd_mul (f := u v) (g := mngPd k (u v)) (hd v) (hd1' v) k]
  ring

lemma mngSq_op (ν : ℝ) (b : Fin d → ℝ → Euc d → ℝ) (u : ι → ℝ → Euc d → ℝ) (hu : ∀ v t, ContDiff ℝ 2 (u v t))
    (t : ℝ) (x : Euc d) :
    ν * Laplacian.laplacian (mngSq u t) x + inner ℝ (mngBv b t x) (gradient (mngSq u t) x) =
      ∑ v, 2 * u v t x * (ν * ∑ k : Fin d, mngPd k (mngPd k (u v)) t x + ∑ k : Fin d, b k t x * mngPd k (u v) t x)
        + 2 * ν * ∑ v, ∑ k : Fin d, mngPd k (u v) t x * mngPd k (u v) t x := by
  have hd : ∀ v t, Differentiable ℝ (u v t) := fun v t => (hu v t).differentiable (by norm_num)
  have hSc : ContDiff ℝ 2 (mngSq u t) := ContDiff.sum fun v _ => (hu v t).mul (hu v t)
  rw [mng_lap_eq hSc x]
  have hl : ∀ k, fderiv ℝ (fun y => fderiv ℝ (mngSq u t) y (mngE k)) x (mngE k) =
      mngPd k (mngPd k (mngSq u)) t x := fun k => rfl
  simp only [hl, mngSq_pd2 u hu]
  have hg : Differentiable ℝ (mngSq u t) := hSc.differentiable (by norm_num)
  rw [mng_inner_grad hg x (mngBv b t x)]
  have hg2 : ∀ k, fderiv ℝ (mngSq u t) x (mngE k) = mngPd k (mngSq u) t x := fun k => rfl
  simp only [hg2, mngSq_pd u hd]
  simp only [mngBv, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset ι)) (f := fun k v => ν * (2 * (mngPd k (mngPd k (u v)) t x * u v t x))),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset ι)) (f := fun k v => ν * (2 * (mngPd k (u v) t x * mngPd k (u v) t x))),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset ι)) (f := fun k v => b k t x * (mngPd k (u v) t x * u v t x)),
    Finset.sum_comm (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset ι)) (f := fun k v => b k t x * (u v t x * mngPd k (u v) t x))]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end SumSq

section SEq

variable {N : ℕ} {ν : ℝ} {Q : ℝ → Euc d → ℝ} {b : Fin d → ℝ → Euc d → ℝ} {A : ℝ → Euc d → ℝ} {a : ℝ → ℝ}
  {Mb MA MQ : ℝ}

/-- The explicit constant in the bound of the cross term. -/
def mngCS (d m : ℕ) (Cb : ℝ) : ℝ := (d : ℝ) ^ m * (2 * Cb ^ 2 * ((m : ℝ) * (d : ℝ) ^ m + 1))

theorem mng_S_eq (hd : 1 ≤ d) (hS : MngSys N ν Q b A a Mb MA MQ) {m : ℕ} (hm : m ≤ N) :
    ∃ T : ℝ → Euc d → ℝ, (∀ t, ContDiff ℝ 2 (mngS Q m t)) ∧ mngJC 0 (mngS Q m) ∧
      (∀ t, 0 ≤ t → ∀ x, 2 * |T t x| ≤ mngS Q m t x +
        mngCS d m (mngCbSeq d Mb MA MQ m) * (mngSx Q m t x + a t ^ 2)) ∧
      (∀ t, 0 ≤ t → ∀ x, HasDerivWithinAt (fun s => mngS Q m s x)
        (ν * Laplacian.laplacian (mngS Q m t) x + inner ℝ (mngBv b t x) (gradient (mngS Q m t) x) +
          2 * A t x * mngS Q m t x + 2 * T t x - 2 * ν * mngS Q (m + 1) t x) (Ici 0) t) := by
  have hlen : ∀ v : List.Vector (Fin d) m, v.toList.length ≤ N := fun v => by rw [v.toList_length]; exact hm
  have h1 : ∀ v : List.Vector (Fin d) m, ∃ R : ℝ → Euc d → ℝ, MngRem Q a MQ (mngCbSeq d Mb MA MQ m) (N - m) m R ∧
      mngDuh (mngJt Q v.toList) (fun t x => mngGen ν b A (mngJt Q v.toList) t x + R t x) := by
    intro v
    obtain ⟨R, hR, hd⟩ := mng_eq hS v.toList (hlen v)
    rw [v.toList_length] at hR
    exact ⟨R, hR, hd⟩
  choose R hR hduh using h1
  set C : List.Vector (Fin d) m → ℝ := fun _ => mngCbSeq d Mb MA MQ m with hCdef
  have hC0 : ∀ v, 0 ≤ C v := fun _ => mngCbSeq_nonneg hS.hMb hS.hMA hS.hMQ m
  have hCb : ∀ v, ∀ t, 0 ≤ t → ∀ x, |R v t x| ≤ C v * (mngJn Q m t x + a t) :=
    fun v t ht x => (hR v).bound hS.hQb hS.a0 t ht x
  set u : List.Vector (Fin d) m → ℝ → Euc d → ℝ := fun v => mngJt Q v.toList with hu
  have hjr : ∀ v : List.Vector (Fin d) m, (∀ t, ContDiff ℝ (N + 2 - m : ℕ) (u v t)) ∧ mngJC (N + 2 - m) (u v) := by
    intro v
    have := hS.jet_reg v.toList (by rw [v.toList_length]; omega)
    rw [v.toList_length] at this
    exact this
  have hcd2 : ∀ v t, ContDiff ℝ 2 (u v t) := fun v t =>
    ((hjr v).1 t).of_le (by exact_mod_cast (by omega : 2 ≤ N + 2 - m))
  have hJ : MngJetReg Q (N - m) m := hS.jetReg (by omega)
  refine ⟨fun t x => ∑ v, u v t x * R v t x, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ContDiff.sum fun v _ => (hcd2 v t).mul (hcd2 v t)
  · have hjc0 : ∀ v, mngJC 0 (u v) := fun v => mngJC_mono (by omega) (hjr v).2
    exact mngJC_sum (r := 0) _ (fun v t => (hcd2 v t).of_le (by norm_num) |>.mul ((hcd2 v t).of_le (by norm_num)))
      (fun v => mngJC_mul (fun t => (hcd2 v t).of_le (by norm_num)) (fun t => (hcd2 v t).of_le (by norm_num))
        (hjc0 v) (hjc0 v))
  · intro t ht x
    have hRb : ∀ v, |R v t x| ≤ C v * (mngJn Q m t x + a t) := fun v => hCb v t ht x
    have hJ2 := mngJn_sq_le hd Q m t x
    have hat := hS.a0 t ht
    have hJ0 := mngJn_nonneg Q m t x
    -- |u R| ≤ (u² + R²)/2
    have e1 : ∀ v, 2 * |u v t x * R v t x| ≤ u v t x * u v t x + R v t x ^ 2 := fun v => by
      rw [abs_mul]
      nlinarith [sq_nonneg (|u v t x| - |R v t x|), sq_abs (u v t x), sq_abs (R v t x), abs_nonneg (u v t x),
        abs_nonneg (R v t x)]
    have e2 : ∀ v, R v t x ^ 2 ≤ 2 * C v ^ 2 * ((m : ℝ) * (d : ℝ) ^ m + 1) * (mngSx Q m t x + a t ^ 2) := fun v => by
      have h0 := hRb v
      have hsq : R v t x ^ 2 ≤ (C v * (mngJn Q m t x + a t)) ^ 2 := by
        rw [← sq_abs (R v t x)]
        exact pow_le_pow_left₀ (abs_nonneg _) h0 2
      have hSx := mngSx_nonneg Q m t x
      have : (mngJn Q m t x + a t) ^ 2 ≤ 2 * (mngJn Q m t x ^ 2 + a t ^ 2) := by nlinarith [sq_nonneg (mngJn Q m t x - a t)]
      have hc2 : 0 ≤ C v ^ 2 := sq_nonneg _
      calc R v t x ^ 2 ≤ (C v * (mngJn Q m t x + a t)) ^ 2 := hsq
        _ = C v ^ 2 * (mngJn Q m t x + a t) ^ 2 := by ring
        _ ≤ C v ^ 2 * (2 * (mngJn Q m t x ^ 2 + a t ^ 2)) := mul_le_mul_of_nonneg_left this hc2
        _ ≤ C v ^ 2 * (2 * (m * (d : ℝ) ^ m * mngSx Q m t x + a t ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hc2
            linarith
        _ ≤ 2 * C v ^ 2 * ((m : ℝ) * (d : ℝ) ^ m + 1) * (mngSx Q m t x + a t ^ 2) := by
            have hm0 : (0 : ℝ) ≤ (m : ℝ) * (d : ℝ) ^ m := by positivity
            have hat2 := sq_nonneg (a t)
            nlinarith [mul_nonneg hc2 (mul_nonneg hm0 hSx), mul_nonneg hc2 hat2, mul_nonneg hc2 hSx]
    calc 2 * |∑ v, u v t x * R v t x| ≤ 2 * ∑ v, |u v t x * R v t x| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
      _ = ∑ v, 2 * |u v t x * R v t x| := by rw [Finset.mul_sum]
      _ ≤ ∑ v, (u v t x * u v t x + R v t x ^ 2) := Finset.sum_le_sum fun v _ => e1 v
      _ = mngS Q m t x + ∑ v, R v t x ^ 2 := by rw [Finset.sum_add_distrib]; rfl
      _ ≤ mngS Q m t x + ∑ v, 2 * C v ^ 2 * ((m : ℝ) * (d : ℝ) ^ m + 1) * (mngSx Q m t x + a t ^ 2) := by
          have := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (List.Vector (Fin d) m))) => e2 v)
          linarith
      _ = _ := by
          rw [← Finset.sum_mul]
          simp [mngCS, hCdef, Finset.sum_const, Finset.card_univ, card_vector]
  · intro t ht x
    -- derivative of each `u v`
    have hG0 : ∀ v, mngJC 0 (fun t x => mngGen ν b A (u v) t x + R v t x) := by
      intro v
      have hgen := mngGen_reg (ν := ν) (b := b) (A := A) (g := u v) (r := 0)
        (fun t => ((hjr v).1 t).of_le (by exact_mod_cast (by omega : 0 + 2 ≤ N + 2 - m)))
        (mngJC_mono (by omega) (hjr v).2)
        (fun k t => (hS.cdb k t).of_le (by exact_mod_cast Nat.zero_le N)) (fun k => mngJC_mono (Nat.zero_le N) (hS.jcb k))
        (fun t => (hS.cdA t).of_le (by exact_mod_cast Nat.zero_le N)) (mngJC_mono (Nat.zero_le N) hS.jcA)
      have hRr := (hR v).reg hJ
      exact mngJC_add (fun t => hgen.1 t) (fun t => (hRr.1 t).of_le (by exact_mod_cast Nat.zero_le _))
        hgen.2 (mngJC_mono (Nat.zero_le _) hRr.2)
    have hder : ∀ v, HasDerivWithinAt (fun s => u v s x) (mngGen ν b A (u v) t x + R v t x) (Ici 0) t :=
      fun v => mng_duh_hasDeriv (hG0 v) (hduh v) x ht
    have hsum : HasDerivWithinAt (fun s => mngS Q m s x)
        (∑ v, ((mngGen ν b A (u v) t x + R v t x) * u v t x + u v t x * (mngGen ν b A (u v) t x + R v t x)))
        (Ici 0) t := by
      have := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun v _ => (hder v).mul (hder v))
      simpa [mngS, hu, mul_comm, add_comm] using this
    refine hsum.congr_deriv ?_
    have hop := mngSq_op ν b u hcd2 t x
    have hSq : mngSq u t = mngS Q m t := rfl
    rw [hSq] at hop
    rw [hop, mngS_succ]
    have hY : ∑ v : List.Vector (Fin d) m, ∑ k : Fin d, mngPd k (mngJt Q v.toList) t x * mngPd k (mngJt Q v.toList) t x =
        ∑ v : List.Vector (Fin d) m, ∑ k : Fin d, mngPd k (u v) t x * mngPd k (u v) t x := rfl
    rw [hY]
    have key : ∀ v : List.Vector (Fin d) m, (mngGen ν b A (u v) t x + R v t x) * u v t x +
        u v t x * (mngGen ν b A (u v) t x + R v t x) =
        2 * u v t x * (ν * ∑ k : Fin d, mngPd k (mngPd k (u v)) t x + ∑ k : Fin d, b k t x * mngPd k (u v) t x) +
          2 * A t x * (u v t x * u v t x) + 2 * (u v t x * R v t x) := fun v => by
      unfold mngGen; ring
    rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hS' : mngS Q m t x = ∑ v : List.Vector (Fin d) m, u v t x * u v t x := rfl
    rw [hS']
    ring

end SEq


end HRS.MS.Mov63

end
