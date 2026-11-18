import HRS.MS.Mov63GAux5

/-!
# S6.3, packet N8 (part 6): the Bernstein cascade

Namespace `HRS.MS.Mov63`, prefix `mng_`.  See `Mov63GAux1`.  **`mng_cascade_step`**: if the orders `1, …, n-1` decay
(`Sx_{n-1} ≤ C_x a(t)²`, `a(t) = K e^{-ct}`), then `S_n ≤ C a(t)²`: compare `ψ - (S_n + λ S_{n-1})`, `ψ = C₅ a²`, with `0` by `mng_master`
(`λ` large absorbs the top-order coupling terms with the dissipation `-2ν S_n` coming from `S_{n-1}`).
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS

variable {d : ℕ}

lemma mng_KI {ν MA Cn Cm Cx lam mu a2 sn sm sn1 sxm An Tn Tm : ℝ} (hν : 0 < ν) (hMA : 0 ≤ MA) (hCn : 0 ≤ Cn)
    (hCm : 0 ≤ Cm) (hCx : 0 ≤ Cx) (ha2 : 0 ≤ a2) (hsn : 0 ≤ sn) (hsm : 0 ≤ sm) (hsn1 : 0 ≤ sn1) (hmu : 0 ≤ mu)
    (hlam : lam = (2 * MA + 1 + Cn + mu) / (2 * ν)) (hA : |An| ≤ MA)
    (hsxm : sxm ≤ Cx * a2) (hsm' : sm ≤ sxm)
    (hTn : 2 * |Tn| ≤ sn + Cn * (sxm + sn + a2)) (hTm : 2 * |Tm| ≤ sm + Cm * (sxm + a2)) :
    2 * An * sn + 2 * Tn - 2 * ν * sn1 + lam * (2 * An * sm + 2 * Tm - 2 * ν * sn) + mu * (sn + lam * sm) ≤
      (Cn * (Cx + 1) + lam * (2 * MA * Cx + Cx + Cm * (Cx + 1)) + mu * lam * Cx) * a2 := by
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hνl : 2 * ν * lam = 2 * MA + 1 + Cn + mu := by rw [hlam]; field_simp
  have hAn := (abs_le.1 hA).2
  have hAn' := (abs_le.1 hA).1
  have hT1 : 2 * Tn ≤ 2 * |Tn| := by linarith [le_abs_self Tn]
  have hT2 : 2 * Tm ≤ 2 * |Tm| := by linarith [le_abs_self Tm]
  have e1 : 2 * An * sn ≤ 2 * MA * sn := by nlinarith
  have e2 : 2 * An * sm ≤ 2 * MA * (Cx * a2) := by
    have : 2 * An * sm ≤ 2 * MA * sm := by nlinarith
    have h2 : sm ≤ Cx * a2 := hsm'.trans hsxm
    nlinarith
  have e3 : Cn * (sxm + sn + a2) ≤ Cn * (Cx * a2 + sn + a2) := by
    apply mul_le_mul_of_nonneg_left _ hCn; linarith
  have e4 : Cm * (sxm + a2) ≤ Cm * (Cx * a2 + a2) := by
    apply mul_le_mul_of_nonneg_left _ hCm; linarith
  have e5 : 2 * Tm ≤ Cx * a2 + Cm * (Cx * a2 + a2) := by
    have h2 : sm ≤ Cx * a2 := hsm'.trans hsxm
    linarith
  have e6 : lam * (2 * An * sm + 2 * Tm - 2 * ν * sn) ≤
      lam * (2 * MA * (Cx * a2) + (Cx * a2 + Cm * (Cx * a2 + a2))) - (2 * MA + 1 + Cn + mu) * sn := by
    have : 2 * An * sm + 2 * Tm - 2 * ν * sn ≤ 2 * MA * (Cx * a2) + (Cx * a2 + Cm * (Cx * a2 + a2)) - 2 * ν * sn := by
      linarith
    have := mul_le_mul_of_nonneg_left this hlam0
    nlinarith
  have e7 : mu * (sn + lam * sm) ≤ mu * sn + mu * lam * (Cx * a2) := by
    have h2 : sm ≤ Cx * a2 := hsm'.trans hsxm
    have : lam * sm ≤ lam * (Cx * a2) := mul_le_mul_of_nonneg_left h2 hlam0
    nlinarith
  have e8 : 2 * Tn ≤ sn + Cn * (Cx * a2 + sn + a2) := by linarith
  nlinarith [mul_nonneg hν.le hsn1]
lemma mng_P_ops {f g : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (γ lam ν : ℝ) (bv x : Euc d) :
    ν * Laplacian.laplacian (fun y => γ - (f y + lam * g y)) x +
      inner ℝ bv (gradient (fun y => γ - (f y + lam * g y)) x) =
    -(ν * Laplacian.laplacian f x + inner ℝ bv (gradient f x)) -
      lam * (ν * Laplacian.laplacian g x + inner ℝ bv (gradient g x)) := by
  have hsum : ContDiff ℝ 2 (fun y => f y + lam * g y) := hf.add (contDiff_const.mul hg)
  have e : (fun y => γ - (f y + lam * g y)) = fun y => γ + (-1) * (f y + lam * g y) := by
    funext y; ring
  rw [e, mnf_laplacian_aff hsum γ (-1) x, mnf_gradient_aff hsum γ (-1) x,
    mnf_laplacian_add_smul hf.contDiffAt hg.contDiffAt lam,
    mnf_gradient_add_smul (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x) lam,
    inner_smul_right, inner_add_right, inner_smul_right]
  ring

/-- The explicit constant `C₅` of the cascade step. -/
def mngC5 (ν MA Cn Cm Cx mu D0 : ℝ) : ℝ :=
  max (D0 * (1 + (2 * MA + 1 + Cn + mu) / (2 * ν)))
    (Cn * (Cx + 1) + ((2 * MA + 1 + Cn + mu) / (2 * ν)) * (2 * MA * Cx + Cx + Cm * (Cx + 1)) +
      mu * ((2 * MA + 1 + Cn + mu) / (2 * ν)) * Cx)

lemma mngC5_nonneg {ν MA Cn Cm Cx mu D0 : ℝ} (hν : 0 < ν) (hMA : 0 ≤ MA) (hCn : 0 ≤ Cn) (hCm : 0 ≤ Cm)
    (hCx : 0 ≤ Cx) (hmu : 0 ≤ mu) : 0 ≤ mngC5 ν MA Cn Cm Cx mu D0 := by
  refine le_trans ?_ (le_max_right _ _)
  positivity

section Casc

variable {N : ℕ} {ν : ℝ} {Q : ℝ → Euc d → ℝ} {b : Fin d → ℝ → Euc d → ℝ} {A : ℝ → Euc d → ℝ} {a : ℝ → ℝ}
  {Mb MA MQ : ℝ}

set_option maxHeartbeats 6400000 in
theorem mng_cascade_step (hd : 1 ≤ d) (hS : MngSys N ν Q b A a Mb MA MQ)
    (hν : 0 < ν) {q M c K : ℝ} (hq : 0 < q) (hc : 0 < c) (hK : 0 ≤ K)
    (ha : ∀ t, a t = K * Real.exp (-c * t))
    (hdiss : ∀ t, 0 ≤ t → ∀ x, inner ℝ (mngBv b t x) x ≤ -q * ‖x‖ ^ 2 + M * ‖x‖)
    (hgrow : ∀ T : ℝ, 0 ≤ T → ∃ Kp κ0 : ℝ, 0 ≤ Kp ∧ κ0 < q / (2 * ν) ∧ ∀ m, 1 ≤ m → m ≤ N →
      ∀ t ∈ Icc 0 T, ∀ x, mngS Q m t x ≤ Kp * Real.exp (κ0 * ‖x‖ ^ 2))
    {D0 : ℝ} (hD0 : 0 ≤ D0) (hinit : ∀ m, 1 ≤ m → m ≤ N → ∀ x, mngS Q m 0 x ≤ D0 * K ^ 2)
    {m : ℕ} (hm : 1 ≤ m) (hmN : m + 1 ≤ N)
    {Cx : ℝ} (hCx0 : 0 ≤ Cx) (hCx : ∀ t, 0 ≤ t → ∀ x, mngSx Q m t x ≤ Cx * a t ^ 2) :
    ∀ t, 0 ≤ t → ∀ x, mngS Q (m + 1) t x ≤
      mngC5 ν MA (mngCS d (m + 1) (mngCbSeq d Mb MA MQ (m + 1))) (mngCS d m (mngCbSeq d Mb MA MQ m)) Cx (2 * c + 1) D0 *
        a t ^ 2 := by
  obtain ⟨Tn, hcdn, hjcn, hTbn, hdern⟩ := mng_S_eq hd hS (m := m + 1) hmN
  obtain ⟨Tm, hcdm, hjcm, hTbm, hderm⟩ := mng_S_eq hd hS (m := m) (by omega)
  have hMA0 := hS.hMA
  have hMAb : ∀ t, 0 ≤ t → ∀ x, |A t x| ≤ MA * a t := mngBW_zero hS.bwA
  set Cn : ℝ := mngCS d (m + 1) (mngCbSeq d Mb MA MQ (m + 1)) with hCn
  set Cm : ℝ := mngCS d m (mngCbSeq d Mb MA MQ m) with hCm
  have hCn0 : 0 ≤ Cn := by rw [hCn, mngCS]; positivity
  have hCm0 : 0 ≤ Cm := by rw [hCm, mngCS]; positivity
  have hinn := hinit (m + 1) (by omega) hmN
  have hinm := hinit m hm (by omega)
  set mu : ℝ := 2 * c + 1 with hmu
  have hmu0 : 0 ≤ mu := by rw [hmu]; linarith
  set lam : ℝ := (2 * MA + 1 + Cn + mu) / (2 * ν) with hlam
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  set Rest : ℝ := Cn * (Cx + 1) + lam * (2 * MA * Cx + Cx + Cm * (Cx + 1)) + mu * lam * Cx with hRest
  have hRest0 : 0 ≤ Rest := by rw [hRest]; positivity
  set C5 : ℝ := mngC5 ν MA Cn Cm Cx mu D0 with hC5
  have hC50 : 0 ≤ C5 := mngC5_nonneg hν hMA0 hCn0 hCm0 hCx0 hmu0
  have hC5def : C5 = max (D0 * (1 + lam)) Rest := rfl
  intro t0 ht0 x0
  -- the weight
  have ha' : ∀ t, HasDerivAt a (-c * a t) t := fun t => by
    have h : HasDerivAt (fun s : ℝ => K * Real.exp (-c * s)) (K * (Real.exp (-c * t) * (-c))) t := by
      have := ((hasDerivAt_id t).const_mul (-c)).exp.const_mul K
      simpa using this
    have e : a = fun s => K * Real.exp (-c * s) := funext ha
    have h2 : -c * a t = K * (Real.exp (-c * t) * (-c)) := by rw [ha]; ring
    rw [← e] at h
    rw [h2]; exact h
  have hacont : Continuous a := continuous_iff_continuousAt.2 fun t => (ha' t).continuousAt
  have ha0 : ∀ t, 0 ≤ a t := fun t => by rw [ha]; positivity
  have ha1' : ∀ t, 0 ≤ t → a t ≤ 1 := hS.a1
  have hψ : ∀ t, HasDerivAt (fun s => C5 * a s ^ 2) (-(2 * c) * C5 * a t ^ 2) t := fun t => by
    have := ((ha' t).pow 2).const_mul C5
    convert this using 1; simp; ring
  have hT := ht0
  -- the pointwise inequality (KI)
  have hSxsucc : ∀ t x, mngSx Q (m + 1) t x = mngSx Q m t x + mngS Q (m + 1) t x := fun t x => by
    unfold mngSx; rw [Finset.sum_range_succ]
  have hSm_le : ∀ t x, mngS Q m t x ≤ mngSx Q m t x := fun t x => by
    unfold mngSx
    have := Finset.single_le_sum (f := fun k => mngS Q (k + 1) t x) (fun k _ => mngS_nonneg Q (k + 1) t x)
      (Finset.mem_range.2 (by omega : m - 1 < m))
    simpa [Nat.sub_add_cancel hm] using this
  have KI : ∀ t, 0 ≤ t → ∀ x, 2 * A t x * mngS Q (m + 1) t x + 2 * Tn t x - 2 * ν * mngS Q (m + 1 + 1) t x +
      lam * (2 * A t x * mngS Q m t x + 2 * Tm t x - 2 * ν * mngS Q (m + 1) t x) +
      mu * (mngS Q (m + 1) t x + lam * mngS Q m t x) ≤ C5 * a t ^ 2 := by
    intro t ht x
    have hAb : |A t x| ≤ MA := (hMAb t ht x).trans (by
      calc MA * a t ≤ MA * 1 := mul_le_mul_of_nonneg_left (ha1' t ht) hMA0
        _ = MA := mul_one _)
    have h1 := mng_KI (ν := ν) (MA := MA) (Cn := Cn) (Cm := Cm) (Cx := Cx) (lam := lam) (mu := mu) (a2 := a t ^ 2)
      (sn := mngS Q (m + 1) t x) (sm := mngS Q m t x) (sn1 := mngS Q (m + 1 + 1) t x) (sxm := mngSx Q m t x)
      (An := A t x) (Tn := Tn t x) (Tm := Tm t x) hν hMA0 hCn0 hCm0 hCx0 (sq_nonneg _) (mngS_nonneg _ _ _ _)
      (mngS_nonneg _ _ _ _) (mngS_nonneg _ _ _ _) hmu0 hlam hAb (hCx t ht x) (hSm_le t x)
      (by have := hTbn t ht x; rw [hSxsucc] at this; linarith) (hTbm t ht x)
    refine h1.trans ?_
    have : Rest * a t ^ 2 ≤ C5 * a t ^ 2 := mul_le_mul_of_nonneg_right (by rw [hC5def]; exact le_max_right _ _) (sq_nonneg _)
    exact this
  -- the comparison on [0,t0]
  obtain ⟨Kp, κ0, hKp, hκ0, hgr⟩ := hgrow t0 ht0
  set κ1 : ℝ := max κ0 0 with hκ1
  have hκ1' : κ1 < q / (2 * ν) := max_lt hκ0 (by positivity)
  set P : ℝ → Euc d → ℝ := fun t x => C5 * a t ^ 2 - (mngS Q (m + 1) t x + lam * mngS Q m t x) with hP
  set Pt : ℝ → Euc d → ℝ := fun t x => -(2 * c) * C5 * a t ^ 2 -
    ((ν * Laplacian.laplacian (mngS Q (m + 1) t) x + inner ℝ (mngBv b t x) (gradient (mngS Q (m + 1) t) x) +
        2 * A t x * mngS Q (m + 1) t x + 2 * Tn t x - 2 * ν * mngS Q (m + 1 + 1) t x) +
      lam * (ν * Laplacian.laplacian (mngS Q m t) x + inner ℝ (mngBv b t x) (gradient (mngS Q m t) x) +
        2 * A t x * mngS Q m t x + 2 * Tm t x - 2 * ν * mngS Q (m + 1) t x)) with hPt
  have hIcc : Icc (0 : ℝ) t0 ⊆ Ici 0 := Set.Icc_subset_Ici_self
  have hPc : ContinuousOn (fun p : ℝ × Euc d => P p.1 p.2) (Icc 0 t0 ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : ℝ × Euc d => mngS Q (m + 1) p.1 p.2) (Icc 0 t0 ×ˢ univ) :=
      (mngJC_zero hjcn).mono (Set.prod_mono hIcc le_rfl)
    have h2 : ContinuousOn (fun p : ℝ × Euc d => mngS Q m p.1 p.2) (Icc 0 t0 ×ˢ univ) :=
      (mngJC_zero hjcm).mono (Set.prod_mono hIcc le_rfl)
    have h3 : Continuous (fun p : ℝ × Euc d => C5 * a p.1 ^ 2) :=
      continuous_const.mul ((hacont.comp continuous_fst).pow 2)
    exact h3.continuousOn.sub (h1.add (continuousOn_const.mul h2))
  have hPd : ∀ t ∈ Ioc 0 t0, ∀ x, HasDerivWithinAt (fun s => P s x) (Pt t x) (Icc 0 t0) t := by
    intro t ht x
    have hdn := (hdern t ht.1.le x).mono hIcc
    have hdm := (hderm t ht.1.le x).mono hIcc
    exact (hψ t).hasDerivWithinAt.sub (hdn.add (hdm.const_mul lam))
  have hPeq : ∀ t ∈ Ioc 0 t0, ∀ x, ν * Laplacian.laplacian (P t) x +
      inner ℝ (mngBv b t x) (gradient (P t) x) + (fun _ _ => -mu : ℝ → Euc d → ℝ) t x * P t x ≤ Pt t x := by
    intro t ht x
    have hops := mng_P_ops (hcdn t) (hcdm t) (C5 * a t ^ 2) lam ν (mngBv b t x) x
    have hki := KI t ht.1.le x
    have hP' : P t = fun y => C5 * a t ^ 2 - (mngS Q (m + 1) t y + lam * mngS Q m t y) := rfl
    rw [hP', hops]
    simp only [hP, hPt]
    nlinarith [hki]
  have hgr' : ∀ t ∈ Icc 0 t0, ∀ x, |P t x| ≤ (C5 * K ^ 2 + Kp * (1 + lam)) * Real.exp (κ1 * ‖x‖ ^ 2) := by
    intro t ht x
    have hat : a t ≤ K := by
      rw [ha]
      calc K * Real.exp (-c * t) ≤ K * 1 := mul_le_mul_of_nonneg_left
            (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith [ht.1])) hK
        _ = K := mul_one _
    have ha2 : a t ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (ha0 t) hat 2
    have hE1 : 1 ≤ Real.exp (κ1 * ‖x‖ ^ 2) := Real.one_le_exp (mul_nonneg (le_max_right _ _) (sq_nonneg _))
    have hE2 : Real.exp (κ0 * ‖x‖ ^ 2) ≤ Real.exp (κ1 * ‖x‖ ^ 2) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    have hs1 : mngS Q (m + 1) t x ≤ Kp * Real.exp (κ1 * ‖x‖ ^ 2) :=
      (hgr (m + 1) (by omega) hmN t ht x).trans (mul_le_mul_of_nonneg_left hE2 hKp)
    have hs2 : mngS Q m t x ≤ Kp * Real.exp (κ1 * ‖x‖ ^ 2) :=
      (hgr m hm (by omega) t ht x).trans (mul_le_mul_of_nonneg_left hE2 hKp)
    have hs1' := mngS_nonneg Q (m + 1) t x
    have hs2' := mngS_nonneg Q m t x
    have hψb : C5 * a t ^ 2 ≤ C5 * K ^ 2 * Real.exp (κ1 * ‖x‖ ^ 2) := by
      calc C5 * a t ^ 2 ≤ C5 * K ^ 2 := mul_le_mul_of_nonneg_left ha2 hC50
        _ = C5 * K ^ 2 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hE1 (by positivity)
    have hψ0 : 0 ≤ C5 * a t ^ 2 := by positivity
    have hlg : lam * mngS Q m t x ≤ lam * (Kp * Real.exp (κ1 * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_left hs2 hlam0
    rw [abs_le]
    constructor
    · simp only [hP]; nlinarith
    · simp only [hP]; nlinarith [mul_nonneg hlam0 hs2']
  have h0 : ∀ x, 0 ≤ P 0 x := by
    intro x
    have ha0' : a 0 = K := by rw [ha]; simp
    simp only [hP, ha0']
    have h1 := hinn x
    have h2 := hinm x
    have h3 : (D0 + lam * D0) * K ^ 2 ≤ C5 * K ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg K)
      calc D0 + lam * D0 = D0 * (1 + lam) := by ring
        _ ≤ C5 := by rw [hC5def]; exact le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_left h2 hlam0]
  have key := mng_master (ν := ν) (q := q) (M := M) (κ0 := κ1) (Kp := C5 * K ^ 2 + Kp * (1 + lam)) (T := t0) hν hq hκ1'
    (by positivity) (P := P) (Pt := Pt) (bv := mngBv b) (c := fun _ _ => -mu)
    (fun t ht => contDiff_const.sub ((hcdn t).add (contDiff_const.mul (hcdm t))))
    hPc hPd hPeq (fun t ht x => by simp only [hmu]; linarith) (fun t ht x => hdiss t ht.1.le x) hgr' h0
  have := key t0 ⟨ht0, le_rfl⟩ x0
  simp only [hP] at this
  have hs2' := mngS_nonneg Q m t0 x0
  nlinarith [mul_nonneg hlam0 hs2']

end Casc


/-- The explicit constants of the cascade: `Sx_{n+1} ≤ mngCxSeq n · a²`. -/
def mngCxSeq (d : ℕ) (ν Mb MA MQ c C1 D0 : ℝ) : ℕ → ℝ
  | 0 => C1
  | n + 1 => mngCxSeq d ν Mb MA MQ c C1 D0 n +
      mngC5 ν MA (mngCS d (n + 2) (mngCbSeq d Mb MA MQ (n + 2))) (mngCS d (n + 1) (mngCbSeq d Mb MA MQ (n + 1)))
        (mngCxSeq d ν Mb MA MQ c C1 D0 n) (2 * c + 1) D0

lemma mngCxSeq_nonneg {ν Mb MA MQ c C1 D0 : ℝ} (hν : 0 < ν) (hMb : 0 ≤ Mb) (hMA : 0 ≤ MA) (hMQ : 0 ≤ MQ)
    (hc : 0 < c) (hC1 : 0 ≤ C1) : ∀ n, 0 ≤ mngCxSeq d ν Mb MA MQ c C1 D0 n
  | 0 => hC1
  | n + 1 => by
    have ih := mngCxSeq_nonneg (D0 := D0) hν hMb hMA hMQ hc hC1 n
    simp only [mngCxSeq]
    refine add_nonneg ih (mngC5_nonneg hν hMA ?_ ?_ ih (by linarith))
    · unfold mngCS; positivity
    · unfold mngCS; positivity

section Casc2

variable {N : ℕ} {ν : ℝ} {Q : ℝ → Euc d → ℝ} {b : Fin d → ℝ → Euc d → ℝ} {A : ℝ → Euc d → ℝ} {a : ℝ → ℝ}
  {Mb MA MQ : ℝ}

/-- **The Bernstein cascade**: the bound `S_1 ≤ C₁ a²` (Lipschitz decay) propagates to all orders `≤ N`, with explicit constants. -/
theorem mng_cascade (hd : 1 ≤ d) (hS : MngSys N ν Q b A a Mb MA MQ)
    (hν : 0 < ν) {q M c K : ℝ} (hq : 0 < q) (hc : 0 < c) (hK : 0 ≤ K)
    (ha : ∀ t, a t = K * Real.exp (-c * t))
    (hdiss : ∀ t, 0 ≤ t → ∀ x, inner ℝ (mngBv b t x) x ≤ -q * ‖x‖ ^ 2 + M * ‖x‖)
    (hgrow : ∀ T : ℝ, 0 ≤ T → ∃ Kp κ0 : ℝ, 0 ≤ Kp ∧ κ0 < q / (2 * ν) ∧ ∀ m, 1 ≤ m → m ≤ N →
      ∀ t ∈ Icc 0 T, ∀ x, mngS Q m t x ≤ Kp * Real.exp (κ0 * ‖x‖ ^ 2))
    {D0 : ℝ} (hD0 : 0 ≤ D0) (hinit : ∀ m, 1 ≤ m → m ≤ N → ∀ x, mngS Q m 0 x ≤ D0 * K ^ 2)
    {C1 : ℝ} (hC1 : 0 ≤ C1) (hS1 : ∀ t, 0 ≤ t → ∀ x, mngS Q 1 t x ≤ C1 * a t ^ 2) :
    ∀ n, n + 1 ≤ N → ∀ t, 0 ≤ t → ∀ x, mngSx Q (n + 1) t x ≤ mngCxSeq d ν Mb MA MQ c C1 D0 n * a t ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro _ t ht x
    simpa [mngSx, mngCxSeq] using hS1 t ht x
  | succ n ih =>
    intro hnN t ht x
    have hCx0 := mngCxSeq_nonneg (d := d) (D0 := D0) hν hS.hMb hS.hMA hS.hMQ hc hC1 n
    have hstep := mng_cascade_step hd hS hν hq hc hK ha hdiss hgrow hD0 hinit (m := n + 1) (by omega) hnN hCx0
      (ih (by omega)) t ht x
    have : mngSx Q (n + 1 + 1) t x = mngSx Q (n + 1) t x + mngS Q (n + 1 + 1) t x := by
      unfold mngSx; rw [Finset.sum_range_succ]
    rw [this]
    simp only [mngCxSeq, add_mul]
    exact add_le_add (ih (by omega) t ht x) hstep

end Casc2


end HRS.MS.Mov63

end
