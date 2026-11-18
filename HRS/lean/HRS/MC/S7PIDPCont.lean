import HRS.MC.S7PIDDefs
import HRS.MC.S7PIDPHat
import HRS.MC.S7PIEVbd
import HRS.MC.S7PIEMeas
import HRS.MC.S7PIE
import HRS.Main.A33Aux3

/-!
# Packet PI-D, sub-packet P (part 2): continuity of the polygonal path and the diagonal `V^{u,u} = id`

* `S7PIDP_pie`: the standing PI-E hypotheses from a `Regime` (as in `s7_PI_E_drift_measure_proof`);
* `S7PIDP_diag`: `V^{t,t}F = F` for `t ∈ (0,T]`;
* `S7PIDP_V_within`: `t ↦ V^{t,c'}F` is continuous on `[c',T]` (also at the diagonal point `t = c'`);
* `S7PIDP_cont`: the polygonal-path function is continuous on `[0,T]` when `c < c'`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDP

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE

variable {d : ℕ}

/-- the standing PI-E data of a regime (copied from the proof of `s7_PI_E_drift_measure_proof`) -/
theorem S7PIDP_pie (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ J n₀ : ℕ, PIEHyp J R.D R.ρ T ∧ 1 ≤ n₀ ∧ n₀ + 1 ≤ J ∧ (n₀ : ℝ) < m ∧ m ≤ n₀ + 1 := by
  have hd2 : 2 ≤ d := R.hd
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  have hm0 : 0 < m := by linarith
  set N : ℕ := ⌈m⌉₊ with hN
  have hmN : m ≤ (N : ℝ) := Nat.le_ceil m
  have hNm : (N : ℝ) < m + 1 := Nat.ceil_lt_add_one hm0.le
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  obtain ⟨n₀, hn₀N⟩ : ∃ n₀ : ℕ, N = n₀ + 1 := ⟨N - 1, by omega⟩
  have hcast : (N : ℝ) = (n₀ : ℝ) + 1 := by rw [hn₀N]; push_cast; ring
  have hn₀m : (n₀ : ℝ) < m := by linarith
  have hmn₀ : m ≤ (n₀ : ℝ) + 1 := by linarith
  have hn₀1 : 1 ≤ n₀ := by
    have : (1 : ℝ) ≤ n₀ := by linarith
    exact_mod_cast this
  obtain ⟨hprob, hcont⟩ := HRS.MC.L2C0.l2c0_rho_prob_cont R
  have hA := HRS.MC.L2C0.l2c0_adjointData_generic R.D R.hM R.hV hν R.ρ hprob
    (fun j => HRS.MC.RegSet.reg_proof R j) hcont
  obtain ⟨Rg, MB, Λ, VB, ν₀, hAD⟩ := hA (n₀ + 1) (by omega) T hT
  have hmStar : PDE.mStar d ≤ n₀ + 1 := by
    have h1 : ((PDE.mStar d : ℕ) : ℝ) ≤ (d : ℝ) / 2 + 3 := by
      unfold PDE.mStar
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
      linarith
    have h2 : ((PDE.mStar d : ℕ) : ℝ) ≤ ((n₀ + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2
  exact ⟨n₀ + 1, n₀, ⟨hd1, hmStar, Rg, MB, Λ, VB, ν₀, hAD⟩, hn₀1, le_rfl, hn₀m, hmn₀⟩

theorem S7PIDP_funRealCoeff_mode (k j : NonzeroLattice d) :
    Torus.funRealCoeff (Torus.realMode k : Torus d → ℝ) j = if j = k then 1 else 0 := by
  unfold Torus.funRealCoeff
  rw [Torus.realMode_orthonormal j k]

/-- `V^{t,t}F = F` on `(0,T]` (the diagonal of the propagator) -/
theorem S7PIDP_diag {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {m t : ℝ} (ht : t ∈ Set.Ioc 0 T) (F : NegSobolev d m) :
    Vprop D μ m t t F = F := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  have hev : ∀ k : NonzeroLattice d, NegSobolev.eval F (propagator D μ t t (Torus.realMode k)) =
      NegSobolev.fourierCoeff F k := by
    intro k
    rw [prop_self_pos hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ht (pieDom_realMode J k)]
    unfold NegSobolev.eval
    rw [tsum_congr (fun j => show NegSobolev.fourierCoeff F j * Torus.funRealCoeff
        (Torus.realMode k : Torus d → ℝ) j = if j = k then NegSobolev.fourierCoeff F k else 0 by
      rw [S7PIDP_funRealCoeff_mode]
      by_cases h : j = k
      · rw [if_pos h, if_pos h, h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero])]
    rw [tsum_ite_eq]
  have hfun : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      NegSobolev.eval F (propagator D μ t t (Torus.realMode k))) = fun k => NegSobolev.coord F k := by
    funext k
    rw [hev, NegSobolev.fourierCoeff, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
      NegSobolev.eval F (propagator D μ t t (Torus.realMode k))) 2 := by
    rw [hfun]; exact lp.memℓp (F : lp (fun _ : NonzeroLattice d => ℝ) 2)
  apply pie_ext
  intro k
  have hV : Vprop D μ m t t F = NegSobolev.ofSeq m
      (fun k => NegSobolev.eval F (propagator D μ t t (Torus.realMode k))) := rfl
  rw [hV, NegSobolev.coord_ofSeq_of_mem _ hmem k, hev, NegSobolev.fourierCoeff, ← mul_assoc,
    ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

/-- Lipschitz bound of `x ↦ pieT u x` on `[u,T]` (the diagonal `x = u` is allowed) -/
theorem S7PIDP_pieT_lip {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : ℝ, 0 < u → ∀ x y : ℝ, u ≤ x → x ≤ T → u ≤ y → y ≤ T →
      ∀ j k : NonzeroLattice d,
        |pieT D μ u x j k - pieT D μ u y j k| ≤ L * |x - y| * Lattice.jp k.1 ^ (J : ℝ) := by
  obtain ⟨L, hL, hlip⟩ := pie_T_lip_t H
  refine ⟨L, hL, fun u hu x y hux hxT huy hyT j k => ?_⟩
  rcases le_total x y with h | h
  · rcases eq_or_lt_of_le h with h' | h'
    · subst h'; simp
    · have := hlip u x y hu.le hux (hu.trans_le hux) h' hyT j k
      have e : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [e, abs_sub_comm]
      linarith
  · rcases eq_or_lt_of_le h with h' | h'
    · subst h'; simp
    · have := hlip u y x hu.le huy (hu.trans_le huy) h' hxT j k
      have e : |x - y| = x - y := abs_of_nonneg (by linarith)
      rw [e]
      linarith

/-- continuity of `t ↦ V^{t,c'}F` within `[c',T]` at any point, including the diagonal `t = c'` -/
theorem S7PIDP_V_within {J n₀ : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T m : ℝ}
    (H : PIEHyp J D μ T) (hn₀ : 1 ≤ n₀) (hJ : n₀ + 1 ≤ J) (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1)
    {c' : ℝ} (hc' : 0 < c') (F : NegSobolev d m) (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Icc c' T) :
    ContinuousWithinAt (fun t => Vprop D μ m t c' F) (Set.Icc c' T) t₀ := by
  obtain ⟨L, hL, hlip⟩ := S7PIDP_pieT_lip H
  have hcT : c' ≤ T := ht₀.1.trans ht₀.2
  refine pie_V_tendsto H m n₀ hn₀ hJ hm0 hm1 (𝓝[Set.Icc c' T] t₀) (fun x : ℝ => x) (fun _ => c') t₀ c'
    ?_ ⟨⟨lt_of_lt_of_le hc' ht₀.1, ht₀.2⟩, hc'.le, ht₀.1⟩ ?_ F
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ⟨⟨lt_of_lt_of_le hc' hx.1, hx.2⟩, hc'.le, hx.1⟩
  · intro j k
    refine pie_tendsto_of_lip (fun x => pieT D μ c' x j k) (fun x : ℝ => x) (pieT D μ c' t₀ j k) t₀
      (L * Lattice.jp k.1 ^ (J : ℝ)) ?_ (tendsto_id.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with x hx
    have := hlip c' hc' x t₀ hx.1 hx.2 ht₀.1 ht₀.2 j k
    calc _ ≤ L * |x - t₀| * Lattice.jp k.1 ^ (J : ℝ) := this
      _ = L * Lattice.jp k.1 ^ (J : ℝ) * |x - t₀| := by ring

/-- the value of the polygonal interpolation at the right end point -/
theorem S7PIDP_polyAt_right (c c' : ℝ) (hcc : c < c') (n : ℕ) {m : ℝ} (v : ℕ → NegSobolev d m) :
    PID.polyAt c c' n v c' = v (2 ^ n) := by
  have hX : (max c (min c' c') - c) / (c' - c) * (2 : ℝ) ^ n = (2 : ℝ) ^ n := by
    rw [min_self, max_eq_right hcc.le, div_self (sub_ne_zero.2 hcc.ne'), one_mul]
  unfold PID.polyAt
  rw [hX, S7PIDP_hat_aux (2 ^ n) (2 ^ n) ((2 : ℝ) ^ n) (by push_cast; exact le_rfl)
    (by push_cast; linarith [pow_pos (show (0 : ℝ) < 2 by norm_num) n]) le_rfl (by push_cast; exact le_rfl) v]
  push_cast
  simp

/-- the polygonal-path function is continuous on `[0,T]` when `c < c' ≤ T` -/
theorem S7PIDP_cont {J n₀ : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T m : ℝ}
    (H : PIEHyp J D μ T) (hn₀ : 1 ≤ n₀) (hJ : n₀ + 1 ≤ J) (hm0 : (n₀ : ℝ) < m) (hm1 : m ≤ n₀ + 1)
    (c c' : ℝ) (hc0 : 0 ≤ c) (hcc : c < c') (hc'T : c' ≤ T) (n : ℕ) (v : ℕ → NegSobolev d m) :
    Continuous fun t : Set.Icc (0 : ℝ) T =>
      (fun t : ℝ => if t ≤ c' then PID.polyAt c c' n v t else Vprop D μ m t c' (v (2 ^ n))) t.1 := by
  have hc'pos : 0 < c' := lt_of_le_of_lt hc0 hcc
  have hpoly : Continuous fun t : ℝ => PID.polyAt c c' n v t := by
    unfold PID.polyAt
    refine continuous_finset_sum _ fun i _ => ?_
    have h1 : Continuous fun t : ℝ =>
        max 0 (1 - |(max c (min t c') - c) / (c' - c) * 2 ^ n - (i : ℝ)|) := by fun_prop
    exact h1.smul continuous_const
  have hL : ContinuousOn (fun t : ℝ => if t ≤ c' then PID.polyAt c c' n v t else Vprop D μ m t c' (v (2 ^ n)))
      (Set.Icc 0 c') := by
    refine hpoly.continuousOn.congr ?_
    intro t ht
    show (if t ≤ c' then PID.polyAt c c' n v t else _) = _
    rw [if_pos ht.2]
  have hR : ContinuousOn (fun t : ℝ => if t ≤ c' then PID.polyAt c c' n v t else Vprop D μ m t c' (v (2 ^ n)))
      (Set.Icc c' T) := by
    have hH : ContinuousOn (fun t => Vprop D μ m t c' (v (2 ^ n))) (Set.Icc c' T) :=
      fun t₀ ht₀ => S7PIDP_V_within H hn₀ hJ hm0 hm1 hc'pos (v (2 ^ n)) t₀ ht₀
    refine hH.congr ?_
    intro t ht
    show (if t ≤ c' then PID.polyAt c c' n v t else _) = Vprop D μ m t c' (v (2 ^ n))
    split_ifs with h
    · have htc : t = c' := le_antisymm h ht.1
      rw [htc, S7PIDP_polyAt_right c c' hcc n v]
      exact (S7PIDP_diag H ⟨hc'pos, hc'T⟩ (v (2 ^ n))).symm
    · rfl
  have hG : ContinuousOn (fun t : ℝ => if t ≤ c' then PID.polyAt c c' n v t else Vprop D μ m t c' (v (2 ^ n)))
      (Set.Icc 0 T) := by
    rw [← Set.Icc_union_Icc_eq_Icc (hc0.trans hcc.le) hc'T]
    exact ContinuousOn.union_of_isClosed hL hR isClosed_Icc isClosed_Icc
  exact continuousOn_iff_continuous_restrict.1 hG

end HRS.MC.Sec7.S7PIDP

end
