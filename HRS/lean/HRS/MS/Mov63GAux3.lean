import HRS.MS.Mov63GAux2

/-!
# S6.3, packet N8 (part 3): jets of `Q`, the remainder class and the equations of all jets

Namespace `HRS.MS.Mov63`, prefix `mng_`.  See `Mov63GAux1`, `Mov63GAux2`.

* `mngJt Q l`: the jet `∂_{l_1} ⋯ ∂_{l_n} Q` (`mngJt Q (i :: l) = ∂_i (mngJt Q l)`), `mngGen ν b A g = ν Δg + ⟨b,∇g⟩ + A g` written with partial derivatives.
* `MngSys`: the data of the abstract system (regularity of `Q`, `b`, `A`, bounds, Duhamel form of the `Q`-equation).
* `MngRem Q a r n R`: the remainder class (finite sums of `c · ∂_τ Q` with `1 ≤ |τ| ≤ n`, `c` a bounded smooth coefficient of budget `r`, and `c · Q` with `c`
  bounded by the decaying weight `a`); it is closed under `∂_i` (`MngRem.pd`, budget `r+1 → r`, order `n → n+1`) and bounded by `C (J_n + a)` (`MngRem.bound`).
* **`mng_eq`**: for every jet `l` of order `n ≤ N`: `∃ R ∈ MngRem (N-n) n`, `mngDuh (∂_l Q) (mngGen (∂_l Q) + R)`, i.e. the jet equations with remainder.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS

variable {d : ℕ}

/-- The jet `∂_{l_1} ⋯ ∂_{l_n} Q`. -/
def mngJt (Q : ℝ → Euc d → ℝ) : List (Fin d) → ℝ → Euc d → ℝ
  | [] => Q
  | i :: l => mngPd i (mngJt Q l)

/-- `ν Δg + ⟨b,∇g⟩ + A g` with partial derivatives. -/
def mngGen (ν : ℝ) (b : Fin d → ℝ → Euc d → ℝ) (A : ℝ → Euc d → ℝ) (g : ℝ → Euc d → ℝ) : ℝ → Euc d → ℝ :=
  fun t x => ν * ∑ i : Fin d, mngPd i (mngPd i g) t x + ∑ k : Fin d, b k t x * mngPd k g t x + A t x * g t x

/-- Bounds by `M w(t)` for the function and for all iterated partial derivatives of order `≤ r` (explicit constant). -/
def mngBW : ℕ → (ℝ → ℝ) → ℝ → (ℝ → Euc d → ℝ) → Prop
  | 0, w, M, f => ∀ t, 0 ≤ t → ∀ x, |f t x| ≤ M * w t
  | r + 1, w, M, f => (∀ t, 0 ≤ t → ∀ x, |f t x| ≤ M * w t) ∧ ∀ i, mngBW r w M (mngPd i f)

lemma mngBW_zero {r : ℕ} {w : ℝ → ℝ} {M : ℝ} {f : ℝ → Euc d → ℝ} (h : mngBW r w M f) :
    ∀ t, 0 ≤ t → ∀ x, |f t x| ≤ M * w t := by
  cases r with
  | zero => exact h
  | succ r => exact h.1

lemma mngBW_mono : ∀ {s r : ℕ} {w : ℝ → ℝ} {M : ℝ} {f : ℝ → Euc d → ℝ}, s ≤ r → mngBW r w M f → mngBW s w M f
  | 0, r, w, M, f, _, h => mngBW_zero h
  | s + 1, 0, w, M, f, hs, _ => absurd hs (by omega)
  | s + 1, r + 1, w, M, f, hs, h => ⟨h.1, fun i => mngBW_mono (by omega) (h.2 i)⟩

lemma mngBW_weight : ∀ {r : ℕ} {w w' : ℝ → ℝ} {M : ℝ} {f : ℝ → Euc d → ℝ}, 0 ≤ M → (∀ t, 0 ≤ t → w t ≤ w' t) →
    mngBW r w M f → mngBW r w' M f
  | 0, w, w', M, f, hM, hw, h => fun t ht x => (h t ht x).trans (mul_le_mul_of_nonneg_left (hw t ht) hM)
  | r + 1, w, w', M, f, hM, hw, ⟨h, h2⟩ =>
    ⟨fun t ht x => (h t ht x).trans (mul_le_mul_of_nonneg_left (hw t ht) hM), fun i => mngBW_weight hM hw (h2 i)⟩

/-- A coefficient of budget `r` with weight `w`: smooth, jointly regular, bounded by `M w(t)` with all its derivatives. -/
structure MngCoef (r : ℕ) (w : ℝ → ℝ) (M : ℝ) (c : ℝ → Euc d → ℝ) : Prop where
  cd : ∀ t, ContDiff ℝ r (c t)
  jc : mngJC r c
  bw : mngBW r w M c

lemma MngCoef.mono {r s : ℕ} {w : ℝ → ℝ} {M : ℝ} {c : ℝ → Euc d → ℝ} (h : MngCoef r w M c) (hs : s ≤ r) :
    MngCoef s w M c :=
  ⟨fun t => (h.cd t).of_le (by exact_mod_cast hs), mngJC_mono hs h.jc, mngBW_mono hs h.bw⟩

lemma MngCoef.weight {r : ℕ} {w w' : ℝ → ℝ} {M : ℝ} {c : ℝ → Euc d → ℝ} (h : MngCoef r w M c) (hM : 0 ≤ M)
    (hw : ∀ t, 0 ≤ t → w t ≤ w' t) : MngCoef r w' M c := ⟨h.cd, h.jc, mngBW_weight hM hw h.bw⟩

lemma MngCoef.pd {r : ℕ} {w : ℝ → ℝ} {M : ℝ} {c : ℝ → Euc d → ℝ} (h : MngCoef (r + 1) w M c) (i : Fin d) :
    MngCoef r w M (mngPd i c) := ⟨fun t => mng_cd_pd (h.cd t) i, mngJC_pd h.jc i, h.bw.2 i⟩

/-- The remainder class, with the explicit constant `Cb` of the bound `|R| ≤ Cb (J_n + a)`. -/
inductive MngRem (Q : ℝ → Euc d → ℝ) (a : ℝ → ℝ) (MQ : ℝ) : ℝ → ℕ → ℕ → (ℝ → Euc d → ℝ) → Prop
  | zero (r n : ℕ) : MngRem Q a MQ 0 r n (fun _ _ => 0)
  | add {Cb₁ Cb₂ : ℝ} {r n : ℕ} {R₁ R₂ : ℝ → Euc d → ℝ} : MngRem Q a MQ Cb₁ r n R₁ → MngRem Q a MQ Cb₂ r n R₂ →
      MngRem Q a MQ (Cb₁ + Cb₂) r n (fun t x => R₁ t x + R₂ t x)
  | jet {r n : ℕ} (M : ℝ) (hM : 0 ≤ M) (c : ℝ → Euc d → ℝ) (hc : MngCoef r (fun _ => 1) M c) (τ : List (Fin d))
      (h1 : 1 ≤ τ.length) (h2 : τ.length ≤ n) : MngRem Q a MQ M r n (fun t x => c t x * mngJt Q τ t x)
  | src {r n : ℕ} (hMQ : 0 ≤ MQ) (M : ℝ) (hM : 0 ≤ M) (c : ℝ → Euc d → ℝ) (hc : MngCoef r a M c) :
      MngRem Q a MQ (M * (MQ + 1)) r n (fun t x => c t x * Q t x)
  | mono {Cb Cb' : ℝ} {r n : ℕ} {R : ℝ → Euc d → ℝ} (h0 : 0 ≤ Cb) (h : Cb ≤ Cb') :
      MngRem Q a MQ Cb r n R → MngRem Q a MQ Cb' r n R

section Rem

variable {Q : ℝ → Euc d → ℝ} {a : ℝ → ℝ} {MQ : ℝ}

/-- Regularity of the jets used by a remainder of budget `r` and order `n`. -/
def MngJetReg (Q : ℝ → Euc d → ℝ) (r n : ℕ) : Prop :=
  ∀ τ : List (Fin d), τ.length ≤ n → (∀ t, ContDiff ℝ r (mngJt Q τ t)) ∧ mngJC r (mngJt Q τ)

lemma MngRem.nonneg {Cb : ℝ} {r n : ℕ} {R : ℝ → Euc d → ℝ} (h : MngRem Q a MQ Cb r n R) : 0 ≤ Cb := by
  induction h with
  | zero => exact le_rfl
  | add h1 h2 ih1 ih2 => exact add_nonneg ih1 ih2
  | jet M hM => exact hM
  | src hMQ M hM => exact mul_nonneg hM (by linarith)
  | mono h0 h => exact h0.trans h

lemma MngRem.reg {Cb : ℝ} {r n : ℕ} {R : ℝ → Euc d → ℝ} (h : MngRem Q a MQ Cb r n R) :
    MngJetReg Q r n → (∀ t, ContDiff ℝ r (R t)) ∧ mngJC r R := by
  induction h with
  | zero => exact fun _ => ⟨fun t => contDiff_const, mngJC_const _ 0⟩
  | add h1 h2 ih1 ih2 => exact fun hJ => ⟨fun t => ((ih1 hJ).1 t).add ((ih2 hJ).1 t),
      mngJC_add (ih1 hJ).1 (ih2 hJ).1 (ih1 hJ).2 (ih2 hJ).2⟩
  | jet M hM c hc τ h1 h2 =>
    intro hJ
    obtain ⟨hcd, hjc⟩ := hJ τ h2
    exact ⟨fun t => (hc.cd t).mul (hcd t), mngJC_mul hc.cd hcd hc.jc hjc⟩
  | src hMQ M hM c hc =>
    intro hJ
    obtain ⟨hcd, hjc⟩ := hJ [] (Nat.zero_le _)
    exact ⟨fun t => (hc.cd t).mul (hcd t), mngJC_mul hc.cd hcd hc.jc hjc⟩
  | mono h0 h _ ih => exact ih

lemma MngRem.pd_aux {Cb : ℝ} {r' n : ℕ} {R : ℝ → Euc d → ℝ} (h : MngRem Q a MQ Cb r' n R)
    (ha1 : ∀ t, 0 ≤ t → a t ≤ 1) (i : Fin d) :
    ∀ r, r' = r + 1 → MngJetReg Q r' n → MngRem Q a MQ (2 * Cb) r (n + 1) (mngPd i R) := by
  induction h with
  | zero =>
    intro r hr hJ
    have : mngPd i (fun (_ : ℝ) (_ : Euc d) => (0 : ℝ)) = fun _ _ => 0 := mng_pd_const 0 i
    rw [this]
    exact MngRem.mono le_rfl (by norm_num) (MngRem.zero _ _)
  | add h1 h2 ih1 ih2 =>
    rename_i Cb₁ Cb₂ r'' n' R₁ R₂
    intro r hr hJ
    subst hr
    have hd1 : ∀ t, Differentiable ℝ (R₁ t) := fun t => ((h1.reg hJ).1 t).differentiable (by simp)
    have hd2 : ∀ t, Differentiable ℝ (R₂ t) := fun t => ((h2.reg hJ).1 t).differentiable (by simp)
    rw [mng_pd_add hd1 hd2]
    have := MngRem.add (ih1 r rfl hJ) (ih2 r rfl hJ)
    rwa [← mul_add] at this
  | jet M hM c hc τ h1 h2 =>
    intro r hr hJ
    subst hr
    obtain ⟨hcd, -⟩ := hJ τ h2
    have hd1 : ∀ t, Differentiable ℝ (c t) := fun t => (hc.cd t).differentiable (by simp)
    have hd2 : ∀ t, Differentiable ℝ (mngJt Q τ t) := fun t => (hcd t).differentiable (by simp)
    rw [mng_pd_mul hd1 hd2]
    refine MngRem.mono (by positivity) (le_of_eq (by ring))
      (MngRem.add (MngRem.jet M hM (mngPd i c) (hc.pd i) τ h1 ?_)
        (MngRem.jet M hM c (hc.mono (Nat.le_succ _)) (i :: τ) (by simp) ?_))
    · omega
    · simp; omega
  | src hMQ M hM c hc =>
    intro r hr hJ
    subst hr
    obtain ⟨hcd, -⟩ := hJ [] (Nat.zero_le _)
    have hd1 : ∀ t, Differentiable ℝ (c t) := fun t => (hc.cd t).differentiable (by simp)
    have hd2 : ∀ t, Differentiable ℝ (Q t) := fun t => (hcd t).differentiable (by simp)
    rw [mng_pd_mul hd1 hd2]
    refine MngRem.mono (by positivity) (by nlinarith [mul_nonneg hM hMQ])
      (MngRem.add (MngRem.src hMQ M hM (mngPd i c) (hc.pd i))
        (MngRem.jet M hM c ((hc.mono (Nat.le_succ _)).weight hM ha1) [i] (by simp) (by simp)))
  | mono h0 h _ ih =>
    intro r hr hJ
    exact MngRem.mono (by linarith) (by linarith) (ih r hr hJ)

lemma MngRem.pd {Cb : ℝ} {r n : ℕ} {R : ℝ → Euc d → ℝ} (h : MngRem Q a MQ Cb (r + 1) n R)
    (hJ : MngJetReg Q (r + 1) n) (ha1 : ∀ t, 0 ≤ t → a t ≤ 1) (i : Fin d) :
    MngRem Q a MQ (2 * Cb) r (n + 1) (mngPd i R) :=
  h.pd_aux ha1 i r rfl hJ

lemma MngRem.sum {ι : Type*} {Cb : ι → ℝ} {r n : ℕ} (s : Finset ι) {R : ι → ℝ → Euc d → ℝ}
    (h : ∀ k ∈ s, MngRem Q a MQ (Cb k) r n (R k)) : MngRem Q a MQ (∑ k ∈ s, Cb k) r n (fun t x => ∑ k ∈ s, R k t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MngRem.zero (Q := Q) (a := a) (MQ := MQ) r n
  | insert k s hk ih =>
    have h1 := MngRem.add (h k (Finset.mem_insert_self k s)) (ih fun k' hk' => h k' (Finset.mem_insert_of_mem hk'))
    simpa [Finset.sum_insert hk] using h1

/-- The sum of the absolute values of all jets of order `1, …, n`. -/
def mngJn (Q : ℝ → Euc d → ℝ) (n : ℕ) (t : ℝ) (x : Euc d) : ℝ :=
  ∑ m ∈ Finset.range n, ∑ v : List.Vector (Fin d) (m + 1), |mngJt Q v.toList t x|

lemma mngJn_nonneg (Q : ℝ → Euc d → ℝ) (n : ℕ) (t : ℝ) (x : Euc d) : 0 ≤ mngJn Q n t x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma MngRem.bound {Cb : ℝ} {r n : ℕ} {R : ℝ → Euc d → ℝ} (h : MngRem Q a MQ Cb r n R)
    (hQb : ∀ t, 0 ≤ t → ∀ x, |Q t x| ≤ MQ) (ha0 : ∀ t, 0 ≤ t → 0 ≤ a t) :
    ∀ t, 0 ≤ t → ∀ x, |R t x| ≤ Cb * (mngJn Q n t x + a t) := by
  induction h with
  | zero => exact fun t ht x => by simp
  | add h1 h2 ih1 ih2 =>
    intro t ht x
    calc _ ≤ |_| + |_| := abs_add_le _ _
      _ ≤ _ := add_le_add (ih1 t ht x) (ih2 t ht x)
      _ = _ := by ring
  | @jet r' n' M hM c hc τ h1 h2 =>
    intro t ht x
    have hb := mngBW_zero hc.bw
    have hjt : |mngJt Q τ t x| ≤ mngJn Q n' t x := by
      obtain ⟨m, hm⟩ : ∃ m, τ.length = m + 1 := ⟨τ.length - 1, by omega⟩
      unfold mngJn
      have hmr : m ∈ Finset.range n' := Finset.mem_range.2 (by omega)
      refine le_trans ?_ (Finset.single_le_sum (f := fun m => ∑ v : List.Vector (Fin d) (m + 1), |mngJt Q v.toList t x|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hmr)
      let v : List.Vector (Fin d) (m + 1) := ⟨τ, hm⟩
      have := Finset.single_le_sum (s := (Finset.univ : Finset (List.Vector (Fin d) (m + 1))))
        (f := fun v : List.Vector (Fin d) (m + 1) => |mngJt Q v.toList t x|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
      exact this
    have hcb := hb t ht x
    simp only [mul_one] at hcb
    rw [abs_mul]
    have ha := ha0 t ht
    calc |c t x| * |mngJt Q τ t x| ≤ M * mngJn Q n' t x :=
          mul_le_mul hcb hjt (abs_nonneg _) hM
      _ ≤ M * (mngJn Q n' t x + a t) := mul_le_mul_of_nonneg_left (by linarith) hM
  | @src r' n' hMQ M hM c hc =>
    intro t ht x
    rw [abs_mul]
    have hJ0 := mngJn_nonneg Q n' t x
    have hq := hQb t ht x
    have hcb := mngBW_zero hc.bw t ht x
    have ha := ha0 t ht
    calc |c t x| * |Q t x| ≤ (M * a t) * MQ := mul_le_mul hcb hq (abs_nonneg _) (by positivity)
      _ ≤ M * (MQ + 1) * (mngJn Q n' t x + a t) := by nlinarith [mul_nonneg hM hMQ, mul_nonneg hM ha]
  | @mono _ _ r' n' _ h0 h _ ih =>
    intro t ht x
    have := ih t ht x
    have hJ0 := mngJn_nonneg Q n' t x
    have ha := ha0 t ht
    calc _ ≤ _ := this
      _ ≤ _ := mul_le_mul_of_nonneg_right h (by linarith)

end Rem

/-- The data of the abstract system. -/
structure MngSys (N : ℕ) (ν : ℝ) (Q : ℝ → Euc d → ℝ) (b : Fin d → ℝ → Euc d → ℝ) (A : ℝ → Euc d → ℝ)
    (a : ℝ → ℝ) (Mb MA MQ : ℝ) : Prop where
  hN : 1 ≤ N
  hMb : 0 ≤ Mb
  hMA : 0 ≤ MA
  hMQ : 0 ≤ MQ
  hQb : ∀ t, 0 ≤ t → ∀ x, |Q t x| ≤ MQ
  cdQ : ∀ t, ContDiff ℝ ((N + 2 : ℕ)) (Q t)
  jcQ : mngJC (N + 2) Q
  cdb : ∀ k t, ContDiff ℝ N (b k t)
  jcb : ∀ k, mngJC N (b k)
  bwb : ∀ k i, mngBW (N - 1) (fun _ => 1) Mb (mngPd i (b k))
  cdA : ∀ t, ContDiff ℝ N (A t)
  jcA : mngJC N A
  bwA : mngBW N a MA A
  a0 : ∀ t, 0 ≤ t → 0 ≤ a t
  a1 : ∀ t, 0 ≤ t → a t ≤ 1
  duh : mngDuh Q (mngGen ν b A Q)

section Sys

variable {N : ℕ} {ν : ℝ} {Q : ℝ → Euc d → ℝ} {b : Fin d → ℝ → Euc d → ℝ} {A : ℝ → Euc d → ℝ} {a : ℝ → ℝ} {Mb MA MQ : ℝ}

lemma MngSys.jet_reg (hS : MngSys N ν Q b A a Mb MA MQ) : ∀ τ : List (Fin d), τ.length ≤ N + 2 →
    (∀ t, ContDiff ℝ (N + 2 - τ.length : ℕ) (mngJt Q τ t)) ∧ mngJC (N + 2 - τ.length) (mngJt Q τ)
  | [], _ => by simpa [mngJt] using And.intro hS.cdQ hS.jcQ
  | i :: l, hl => by
    have ih := MngSys.jet_reg hS l (by simp at hl; omega)
    have hlen : (i :: l).length = l.length + 1 := rfl
    obtain ⟨r, hr⟩ : ∃ r, N + 2 - l.length = r + 1 := ⟨N + 1 - l.length, by simp at hl; omega⟩
    have hr' : N + 2 - (i :: l).length = r := by rw [hlen]; omega
    rw [hr'] 
    rw [hr] at ih
    exact ⟨fun t => mng_cd_pd (ih.1 t) i, mngJC_pd ih.2 i⟩

lemma MngSys.jetReg (hS : MngSys N ν Q b A a Mb MA MQ) {r n : ℕ} (h : r + n ≤ N + 2) : MngJetReg Q r n := by
  intro τ hτ
  have := hS.jet_reg τ (by omega)
  exact ⟨fun t => (this.1 t).of_le (by exact_mod_cast (by omega : r ≤ N + 2 - τ.length)),
    mngJC_mono (by omega) this.2⟩

lemma MngSys.coefB (hS : MngSys N ν Q b A a Mb MA MQ) {r : ℕ} (hr : r + 1 ≤ N) (k i : Fin d) :
    MngCoef r (fun _ => 1) Mb (mngPd i (b k)) :=
  ⟨fun t => mng_cd_pd ((hS.cdb k t).of_le (by exact_mod_cast hr)) i,
    mngJC_pd (mngJC_mono hr (hS.jcb k)) i, mngBW_mono (by omega) (hS.bwb k i)⟩

lemma MngSys.coefA (hS : MngSys N ν Q b A a Mb MA MQ) {r : ℕ} (hr : r + 1 ≤ N) (i : Fin d) :
    MngCoef r a MA (mngPd i A) :=
  ⟨fun t => mng_cd_pd ((hS.cdA t).of_le (by exact_mod_cast hr)) i,
    mngJC_pd (mngJC_mono hr hS.jcA) i, (mngBW_mono hr hS.bwA).2 i⟩

end Sys

/-- Regularity of the generator applied to a function `g`. -/
lemma mngGen_reg {ν : ℝ} {b : Fin d → ℝ → Euc d → ℝ} {A : ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ} {r : ℕ}
    (hg : ∀ t, ContDiff ℝ (r + 2 : ℕ) (g t)) (hjc : mngJC (r + 2) g)
    (hb : ∀ k t, ContDiff ℝ r (b k t)) (hbj : ∀ k, mngJC r (b k))
    (hA : ∀ t, ContDiff ℝ r (A t)) (hAj : mngJC r A) :
    (∀ t, ContDiff ℝ r (mngGen ν b A g t)) ∧ mngJC r (mngGen ν b A g) := by
  have hpd1 : ∀ k t, ContDiff ℝ (r + 1 : ℕ) (mngPd k g t) := fun k t => mng_cd_pd (hg t) k
  have hpd2 : ∀ k t, ContDiff ℝ r (mngPd k (mngPd k g) t) := fun k t => mng_cd_pd (hpd1 k t) k
  have hj1 : ∀ k, mngJC (r + 1) (mngPd k g) := fun k => mngJC_pd hjc k
  have hj2 : ∀ k, mngJC r (mngPd k (mngPd k g)) := fun k => mngJC_pd (hj1 k) k
  have hr1 : ∀ k t, ContDiff ℝ r (mngPd k g t) := fun k t => (hpd1 k t).of_le (by exact_mod_cast Nat.le_succ r)
  have hrj : ∀ k, mngJC r (mngPd k g) := fun k => mngJC_mono (Nat.le_succ r) (hj1 k)
  have hgr : ∀ t, ContDiff ℝ r (g t) := fun t => (hg t).of_le (by exact_mod_cast (by omega : r ≤ r + 2))
  have hgj : mngJC r g := mngJC_mono (by omega) hjc
  have e1 : ∀ t, ContDiff ℝ r (fun x => ν * ∑ i : Fin d, mngPd i (mngPd i g) t x) := fun t =>
    contDiff_const.mul (ContDiff.sum fun i _ => hpd2 i t)
  have j1 : mngJC r (fun t x => ν * ∑ i : Fin d, mngPd i (mngPd i g) t x) :=
    mngJC_mul (fun t => contDiff_const) (fun t => ContDiff.sum fun i _ => hpd2 i t) (mngJC_const r ν)
      (mngJC_sum _ hpd2 hj2)
  have e2 : ∀ t, ContDiff ℝ r (fun x => ∑ k : Fin d, b k t x * mngPd k g t x) := fun t =>
    ContDiff.sum fun k _ => (hb k t).mul (hr1 k t)
  have j2 : mngJC r (fun t x => ∑ k : Fin d, b k t x * mngPd k g t x) :=
    mngJC_sum _ (fun k t => (hb k t).mul (hr1 k t)) (fun k => mngJC_mul (hb k) (hr1 k) (hbj k) (hrj k))
  have e3 : ∀ t, ContDiff ℝ r (fun x => A t x * g t x) := fun t => (hA t).mul (hgr t)
  have j3 : mngJC r (fun t x => A t x * g t x) := mngJC_mul hA hgr hAj hgj
  refine ⟨fun t => (e1 t).add (e2 t) |>.add (e3 t), ?_⟩
  exact mngJC_add (fun t => (e1 t).add (e2 t)) e3 (mngJC_add e1 e2 j1 j2) j3

lemma mng_pd_gen {ν : ℝ} {b : Fin d → ℝ → Euc d → ℝ} {A : ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ}
    (hg : ∀ t, ContDiff ℝ 3 (g t)) (hb : ∀ k t, ContDiff ℝ 1 (b k t)) (hA : ∀ t, ContDiff ℝ 1 (A t)) (i : Fin d) :
    mngPd i (mngGen ν b A g) = fun t x => mngGen ν b A (mngPd i g) t x +
      (∑ k : Fin d, mngPd i (b k) t x * mngPd k g t x + mngPd i A t x * g t x) := by
  have hg2 : ∀ t, ContDiff ℝ 2 (g t) := fun t => (hg t).of_le (by norm_num)
  have hg1 : ∀ t, Differentiable ℝ (g t) := fun t => (hg t).differentiable (by norm_num)
  have hpd : ∀ k t, ContDiff ℝ 2 (mngPd k g t) := fun k t => by
    have := mng_cd_pd (r := 2) (g := g t) (by exact_mod_cast hg t) k
    exact this
  have hpd1 : ∀ k t, Differentiable ℝ (mngPd k g t) := fun k t => (hpd k t).differentiable (by norm_num)
  have hpd2 : ∀ k t, ContDiff ℝ 1 (mngPd k (mngPd k g) t) := fun k t => mng_cd_pd (hpd k t) k
  have hpd2' : ∀ k t, Differentiable ℝ (mngPd k (mngPd k g) t) := fun k t => (hpd2 k t).differentiable (by norm_num)
  have hb1 : ∀ k t, Differentiable ℝ (b k t) := fun k t => (hb k t).differentiable (by norm_num)
  have hA1 : ∀ t, Differentiable ℝ (A t) := fun t => (hA t).differentiable (by norm_num)
  unfold mngGen
  have s1 : mngPd i (fun t x => ν * ∑ j : Fin d, mngPd j (mngPd j g) t x + ∑ k : Fin d, b k t x * mngPd k g t x +
      A t x * g t x) = fun t x => mngPd i (fun t x => ν * ∑ j : Fin d, mngPd j (mngPd j g) t x) t x +
      mngPd i (fun t x => ∑ k : Fin d, b k t x * mngPd k g t x) t x + mngPd i (fun t x => A t x * g t x) t x := by
    have d1 : ∀ t, Differentiable ℝ (fun x => ν * ∑ j : Fin d, mngPd j (mngPd j g) t x) := fun t =>
      (differentiable_const ν).mul (Differentiable.fun_sum fun j _ => hpd2' j t)
    have d2 : ∀ t, Differentiable ℝ (fun x => ∑ k : Fin d, b k t x * mngPd k g t x) := fun t =>
      Differentiable.fun_sum fun k _ => (hb1 k t).mul (hpd1 k t)
    have d3 : ∀ t, Differentiable ℝ (fun x => A t x * g t x) := fun t => (hA1 t).mul (hg1 t)
    have := mng_pd_add (f := fun t x => ν * ∑ j : Fin d, mngPd j (mngPd j g) t x +
      ∑ k : Fin d, b k t x * mngPd k g t x) (g := fun t x => A t x * g t x)
      (fun t => (d1 t).add (d2 t)) d3 i
    rw [this, mng_pd_add d1 d2 i]
  rw [s1]
  have t1 : mngPd i (fun t x => ν * ∑ j : Fin d, mngPd j (mngPd j g) t x) =
      fun t x => ν * ∑ j : Fin d, mngPd j (mngPd j (mngPd i g)) t x := by
    rw [mng_pd_const_mul (f := fun t x => ∑ j : Fin d, mngPd j (mngPd j g) t x)
      (fun t => Differentiable.fun_sum fun j _ => hpd2' j t) ν i]
    rw [mng_pd_sum Finset.univ (f := fun j => mngPd j (mngPd j g)) (fun j t => hpd2' j t) i]
    funext t x
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have c1 : mngPd i (mngPd j (mngPd j g)) = mngPd j (mngPd i (mngPd j g)) :=
      mng_pd_comm (f := mngPd j g) (fun t => hpd j t) i j
    have c2 : mngPd i (mngPd j g) = mngPd j (mngPd i g) := mng_pd_comm (f := g) hg2 i j
    rw [c1, c2]
  have t2 : mngPd i (fun t x => ∑ k : Fin d, b k t x * mngPd k g t x) =
      fun t x => ∑ k : Fin d, (mngPd i (b k) t x * mngPd k g t x + b k t x * mngPd k (mngPd i g) t x) := by
    rw [mng_pd_sum Finset.univ (f := fun k t x => b k t x * mngPd k g t x) (fun k t => (hb1 k t).mul (hpd1 k t)) i]
    funext t x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mng_pd_mul (f := b k) (g := mngPd k g) (hb1 k) (hpd1 k) i]
    have c2 : mngPd i (mngPd k g) = mngPd k (mngPd i g) := mng_pd_comm (f := g) hg2 i k
    rw [c2]
  have t3 : mngPd i (fun t x => A t x * g t x) = fun t x => mngPd i A t x * g t x + A t x * mngPd i g t x :=
    mng_pd_mul hA1 hg1 i
  rw [t1, t2, t3]
  funext t x
  simp only [Finset.sum_add_distrib]
  ring

section Eq

variable {N : ℕ} {ν : ℝ} {Q : ℝ → Euc d → ℝ} {b : Fin d → ℝ → Euc d → ℝ} {A : ℝ → Euc d → ℝ} {a : ℝ → ℝ}
  {Mb MA MQ : ℝ}

/-- The explicit constants of the remainders. -/
def mngCbSeq (d : ℕ) (Mb MA MQ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 2 * mngCbSeq d Mb MA MQ n + d * Mb + MA * (MQ + 1)

lemma mngCbSeq_nonneg (hMb : 0 ≤ Mb) (hMA : 0 ≤ MA) (hMQ : 0 ≤ MQ) : ∀ n, 0 ≤ mngCbSeq d Mb MA MQ n
  | 0 => le_rfl
  | n + 1 => by
    have := mngCbSeq_nonneg hMb hMA hMQ n
    simp only [mngCbSeq]
    positivity

lemma mng_eq_step (hS : MngSys N ν Q b A a Mb MA MQ) {n r : ℕ} (hN : N = n + 1 + r) (l : List (Fin d))
    (hl : l.length = n) {Cb : ℝ} {R : ℝ → Euc d → ℝ} (hR : MngRem Q a MQ Cb (r + 1) n R)
    (hduh : mngDuh (mngJt Q l) (fun t x => mngGen ν b A (mngJt Q l) t x + R t x)) (i : Fin d) :
    ∃ R' : ℝ → Euc d → ℝ, MngRem Q a MQ (2 * Cb + d * Mb + MA * (MQ + 1)) r (n + 1) R' ∧
      mngDuh (mngJt Q (i :: l)) (fun t x => mngGen ν b A (mngJt Q (i :: l)) t x + R' t x) := by
  set g := mngJt Q l with hg
  have hjr := hS.jet_reg l (by omega)
  have e : N + 2 - l.length = r + 1 + 2 := by omega
  rw [e] at hjr
  have hJ : MngJetReg Q (r + 1) n := hS.jetReg (by omega)
  have hRreg := hR.reg hJ
  have hbk : ∀ k t, ContDiff ℝ (r + 1) (b k t) := fun k t => (hS.cdb k t).of_le (by exact_mod_cast (by omega : r + 1 ≤ N))
  have hAk : ∀ t, ContDiff ℝ (r + 1) (A t) := fun t => (hS.cdA t).of_le (by exact_mod_cast (by omega : r + 1 ≤ N))
  have hgen := mngGen_reg (ν := ν) (b := b) (A := A) hjr.1 hjr.2 hbk (fun k => mngJC_mono (by omega) (hS.jcb k))
    hAk (mngJC_mono (by omega) hS.jcA)
  have hGcd : ∀ t, ContDiff ℝ (r + 1) ((fun t x => mngGen ν b A g t x + R t x) t) := fun t => (hgen.1 t).add (hRreg.1 t)
  have hGjc : mngJC (r + 1) (fun t x => mngGen ν b A g t x + R t x) :=
    mngJC_add hgen.1 hRreg.1 hgen.2 hRreg.2
  have hdg : ∀ t, Differentiable ℝ (g t) := fun t => (hjr.1 t).differentiable (by simp)
  have hdG : ∀ t, Differentiable ℝ ((fun t x => mngGen ν b A g t x + R t x) t) := fun t =>
    (hGcd t).differentiable (by simp)
  have hstep := mng_duh_pd hdg hdG (mngJC_mono (by omega) hGjc) hduh i
  -- compute the derivative of the generator
  have hg3 : ∀ t, ContDiff ℝ 3 (g t) := fun t => (hjr.1 t).of_le (by exact_mod_cast (by omega : 3 ≤ r + 1 + 2))
  have hb1 : ∀ k t, ContDiff ℝ 1 (b k t) := fun k t => (hbk k t).of_le (by exact_mod_cast (by omega : 1 ≤ r + 1))
  have hA1 : ∀ t, ContDiff ℝ 1 (A t) := fun t => (hAk t).of_le (by exact_mod_cast (by omega : 1 ≤ r + 1))
  have hpdgen := mng_pd_gen (ν := ν) (b := b) (A := A) hg3 hb1 hA1 i
  have hdgen : ∀ t, Differentiable ℝ (mngGen ν b A g t) := fun t => (hgen.1 t).differentiable (by simp)
  have hdR : ∀ t, Differentiable ℝ (R t) := fun t => (hRreg.1 t).differentiable (by simp)
  have hsplit := mng_pd_add hdgen hdR i
  set R' : ℝ → Euc d → ℝ := fun t x =>
    ((∑ k : Fin d, mngPd i (b k) t x * mngPd k g t x) + mngPd i A t x * g t x) + mngPd i R t x with hR'
  have hG' : mngPd i (fun t x => mngGen ν b A g t x + R t x) =
      fun t x => mngGen ν b A (mngPd i g) t x + R' t x := by
    rw [hsplit, hpdgen]
    funext t x
    simp only [hR']
    ring
  refine ⟨R', ?_, ?_⟩
  · have hCb0 := hR.nonneg
    have hs0 : MngRem Q a MQ (∑ k : Fin d, Mb) r (n + 1) (fun t x => ∑ k : Fin d, mngPd i (b k) t x * mngJt Q (k :: l) t x) :=
      MngRem.sum _ fun k _ => MngRem.jet Mb hS.hMb (mngPd i (b k)) (hS.coefB (r := r) (by omega) k i) (k :: l)
        (by simp) (by simp [hl])
    have hs : MngRem Q a MQ (d * Mb) r (n + 1) (fun t x => ∑ k : Fin d, mngPd i (b k) t x * mngJt Q (k :: l) t x) :=
      MngRem.mono (Finset.sum_nonneg fun _ _ => hS.hMb) (le_of_eq (by simp)) hs0
    have hA : MngRem Q a MQ (MA * (MQ + 1)) r (n + 1) (fun t x => mngPd i A t x * g t x) := by
      cases hl' : l with
      | nil =>
        have : g = Q := by rw [hg, hl']; rfl
        rw [this]
        exact MngRem.src hS.hMQ MA hS.hMA _ (hS.coefA (r := r) (by omega) i)
      | cons j l' =>
        have : g = mngJt Q (j :: l') := by rw [hg, hl']
        rw [this]
        refine MngRem.mono hS.hMA (by nlinarith [mul_nonneg hS.hMA hS.hMQ]) ?_
        exact MngRem.jet (n := n + 1) MA hS.hMA (mngPd i A) ((hS.coefA (r := r) (by omega) i).weight hS.hMA hS.a1)
          (j :: l') (by simp) (by rw [hl'] at hl; simp at hl ⊢; omega)
    have hall := MngRem.add (MngRem.add hs hA) (hR.pd hJ hS.a1 i)
    refine MngRem.mono (by have := hS.hMb; have := hS.hMA; have := hS.hMQ; positivity) (le_of_eq (by ring)) hall
  · rw [hG'] at hstep
    exact hstep

theorem mng_eq (hS : MngSys N ν Q b A a Mb MA MQ) : ∀ l : List (Fin d), l.length ≤ N →
    ∃ R : ℝ → Euc d → ℝ, MngRem Q a MQ (mngCbSeq d Mb MA MQ l.length) (N - l.length) l.length R ∧
      mngDuh (mngJt Q l) (fun t x => mngGen ν b A (mngJt Q l) t x + R t x)
  | [], _ => by
    refine ⟨fun _ _ => 0, MngRem.zero _ _, ?_⟩
    have := hS.duh
    simpa [mngJt] using this
  | i :: l, hl => by
    have hl' : l.length ≤ N := by simp at hl; omega
    obtain ⟨R, hR, hd⟩ := mng_eq hS l hl'
    have hlen : (i :: l).length = l.length + 1 := rfl
    obtain ⟨r, hr⟩ : ∃ r, N = l.length + 1 + r := ⟨N - (l.length + 1), by simp at hl; omega⟩
    have e1 : N - l.length = r + 1 := by omega
    have e2 : N - (i :: l).length = r := by rw [hlen]; omega
    rw [e1] at hR
    rw [e2, hlen]
    exact mng_eq_step hS hr l rfl hR hd i

end Eq


end HRS.MS.Mov63

end
