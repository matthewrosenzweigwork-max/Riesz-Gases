import HRS.MC.S7PIDVLipMat
import HRS.MC.S7PIDDefs
import HRS.MC.S7PIE

/-!
# Packet PI-D, sub-packet V: `V^{t,u}` is Hölder-`1/2` in `t` from `E_{m-1}` to `E_m` and bounded on `E_{m-1}`

Proof of `HRS.MC.Sec7.PIDPlan.s7_PID_V_holder` (statement copied verbatim).  The matrix of `V^{t,u}` is `pieT u t`;

* the `E_{m-1}`-boundedness (conclusions 2, 3) is `pie_dual` for the matrix at the exponent `m - 1`;
* the difference `Δ = pieT u t - pieT u s` obeys `E_{m-2} → E_m` with norm `ℓ ∼ (t - s)`
  (`S7PIDV_lipMat` at the integer levels `k+2`, `k+3`, interpolated by `pie_interp` with the shifted weights
  `w_j^{-2}`), and `E_m → E_m` with norm `B` (the two uniform bounds);
* `S7PIDV_holder_seq` (frequency cutoff) gives `E_{m-1} → E_m` with norm `2 √(ℓ B)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDV

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE

variable {d : ℕ}

lemma S7PIDV_finBd_mono {ι : Type*} {S : ι → ι → ℝ} {A A' : ℝ} (hA : 0 ≤ A) (h : pieFinBd S A) (hAA : A ≤ A') :
    pieFinBd S A' := fun K J x =>
  (h K J x).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAA 2)
    (Finset.sum_nonneg fun k _ => sq_nonneg _))

/-- uniform finite-section bound of `pieT u t` at a real exponent, including the degenerate time `t = 0` -/
lemma S7PIDV_finBd_unif {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) (σ : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (hJ : n + 1 ≤ J) (h0 : (n : ℝ) < σ) (h1 : σ ≤ n + 1) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T →
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) σ) A := by
  obtain ⟨A0, hA0, hb⟩ := pie_finBd_real H σ n hn hJ h0 h1
  refine ⟨max A0 1, le_max_right _ _, fun u t hu hut htT => ?_⟩
  rcases (hu.trans hut).eq_or_lt with h | h
  · have ht0 : t = 0 := h.symm
    subst ht0
    have hu0 : u = 0 := le_antisymm hut hu
    subst hu0
    exact S7PIDV_finBd_mono zero_le_one (S7PIDV_finBd_zero H σ) (le_max_right _ _)
  · exact S7PIDV_finBd_mono hA0 (hb t ⟨h, htT⟩ u ⟨hu, hut⟩) (le_max_left _ _)

/-- the norm of `ofSeq σ c` -/
lemma S7PIDV_norm_ofSeq_sq {σ : ℝ} (c : NonzeroLattice d → ℝ)
    (h : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-σ) * c k) 2) :
    Summable (fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (-σ) * c k) ^ 2) ∧
      ‖(NegSobolev.ofSeq σ c : NegSobolev d σ)‖ ^ 2 = ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ (-σ) * c k) ^ 2 := by
  obtain ⟨h2, hn⟩ := NegSobolev.coord_sq (NegSobolev.ofSeq σ c : NegSobolev d σ)
  have e : ∀ k, NegSobolev.coord (NegSobolev.ofSeq σ c : NegSobolev d σ) k = Lattice.jp k.1 ^ (-σ) * c k :=
    fun k => NegSobolev.coord_ofSeq_of_mem c h k
  exact ⟨h2.congr fun k => by rw [e], by rw [hn]; exact tsum_congr fun k => by rw [e]⟩

/-- the Fourier coefficients of `V^{t,u}F` -/
lemma S7PIDV_fc_V (D : DynData d) (μ : ℝ → Torus d → ℝ) (m : ℝ) (t u : ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hH : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) m) A)
    (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (Vprop D μ m t u F) k = ∑' j, NegSobolev.fourierCoeff F j * pieT D μ u t j k := by
  unfold NegSobolev.fourierCoeff
  rw [pie_Vprop_coord D μ m t u hA hH F k, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp [NegSobolev.fourierCoeff]

/-- the standing data of `s7_PID_V_holder`: the integer level `k + 2 < m ≤ k + 3` and the adjoint hypotheses at `k + 3` -/
lemma S7PIDV_hyp (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) + 2 < m ∧ m ≤ (k : ℝ) + 3 ∧ PDE.mStar d ≤ k ∧ PIEHyp (k + 3) R.D R.ρ T := by
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
  have hn₀big : (3 * (d : ℝ) + 7 < n₀) := by linarith
  have hn₀3 : 3 ≤ n₀ := by
    have : (3 : ℝ) ≤ n₀ := by linarith
    exact_mod_cast this
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n₀ = k + 2 := ⟨n₀ - 2, by omega⟩
  have hkR : (n₀ : ℝ) = (k : ℝ) + 2 := by rw [hk]; push_cast; ring
  have hk1 : 1 ≤ k := by omega
  have hmStar : PDE.mStar d ≤ k := by
    have h1 : ((PDE.mStar d : ℕ) : ℝ) ≤ (d : ℝ) / 2 + 3 := by
      unfold PDE.mStar
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
      linarith
    have h2 : ((PDE.mStar d : ℕ) : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast h2
  refine ⟨k, hk1, by linarith, by linarith, hmStar, ?_⟩
  obtain ⟨hprob, hcont⟩ := HRS.MC.L2C0.l2c0_rho_prob_cont R
  have hA := HRS.MC.L2C0.l2c0_adjointData_generic R.D R.hM R.hV hν R.ρ hprob
    (fun j => HRS.MC.RegSet.reg_proof R j) hcont
  obtain ⟨Rg, MB, Λ, VB, ν₀, hAD⟩ := hA (k + 3) (by omega) T hT
  exact ⟨hd1, by omega, Rg, MB, Λ, VB, ν₀, hAD⟩

/-- **D1 (`V^{t,u}` is Hölder-1/2 in `t` from `E_{m-1}` to `E_m`, and bounded on `E_{m-1}`)**. -/
theorem s7_PID_V_holder_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ L C : ℝ, 0 ≤ L ∧ 0 ≤ C ∧ ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ T →
      ∀ F : NegSobolev d m,
        Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F k) 2 →
        ‖Vprop R.D R.ρ m t u F - Vprop R.D R.ρ m s u F‖ ≤ L * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F ∧
        Memℓp (fun k : NonzeroLattice d =>
          Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff (Vprop R.D R.ρ m t u F) k) 2 ∧
        sobAt (m - 1) (Vprop R.D R.ρ m t u F) ≤ C * sobAt (m - 1) F := by
  obtain ⟨k, hk1, hk2, hk3, hkst, H⟩ := S7PIDV_hyp R m hm T hT
  have hw : ∀ i : NonzeroLattice d, 0 < Lattice.jp i.1 := fun i => Torus.jp_pos i.1
  have hw1 : ∀ i : NonzeroLattice d, 1 ≤ Lattice.jp i.1 := fun i => Torus.jp_ge_one i.1
  -- uniform bounds of the matrices at the exponents `m` and `m - 1`
  obtain ⟨Am, hAm1, hAmb⟩ := S7PIDV_finBd_unif H m (k + 2) (by omega) (by omega)
    (by push_cast; exact hk2) (by push_cast; linarith)
  obtain ⟨Ac, hAc1, hAcb⟩ := S7PIDV_finBd_unif H (m - 1) (k + 1) (by omega) (by omega)
    (by push_cast; linarith) (by push_cast; linarith)
  -- the Lipschitz bounds at the integer levels `k + 2` and `k + 3`
  obtain ⟨K0, hK0, hL0⟩ := S7PIDV_lipMat H k hk1 (by omega) (by omega)
  obtain ⟨K1, hK1, hL1⟩ := S7PIDV_lipMat H (k + 1) (by omega) (by omega) (by omega)
  set θ : ℝ := m - ((k : ℝ) + 2) with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  set Kint : ℝ := K0 ^ (1 - θ) * K1 ^ θ with hKint
  have hKint0 : 0 ≤ Kint := mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg hK1 _)
  have hAm0 : 0 ≤ Am := by linarith
  have hAc0 : 0 ≤ Ac := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt ((Kint + 1) * Am) := Real.sqrt_nonneg _
  refine ⟨4 * Real.sqrt ((Kint + 1) * Am), Ac, by positivity, by linarith, fun u s t hu hus hst htT F hF => ?_⟩
  have hsT : s ≤ T := hst.trans htT
  have hF2 : Summable fun j : NonzeroLattice d => (Lattice.jp j.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F j) ^ 2 :=
    (Torus.memℓp_two_iff _).1 hF
  obtain ⟨-, hSdef⟩ := S7PIDV_norm_ofSeq_sq (σ := m - 1) (fun k => NegSobolev.fourierCoeff F k) hF
  have hsob : sobAt (m - 1) F ^ 2 =
      ∑' j : NonzeroLattice d, (Lattice.jp j.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F j) ^ 2 := hSdef
  have hsob0 : 0 ≤ sobAt (m - 1) F := norm_nonneg _
  -- conclusions 2 and 3
  have hV23 : Memℓp (fun k : NonzeroLattice d =>
        Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff (Vprop R.D R.ρ m t u F) k) 2 ∧
      sobAt (m - 1) (Vprop R.D R.ρ m t u F) ≤ Ac * sobAt (m - 1) F := by
    have hu0 : u ≤ t := hus.trans hst
    obtain ⟨hs1, hle⟩ := pie_dual hw hAc0 (hAcb u t hu hu0 htT) (fun j => NegSobolev.fourierCoeff F j) hF2
    have hfc : ∀ k, NegSobolev.fourierCoeff (Vprop R.D R.ρ m t u F) k =
        ∑' j, NegSobolev.fourierCoeff F j * pieT R.D R.ρ u t j k :=
      S7PIDV_fc_V R.D R.ρ m t u hAm0 (hAmb u t hu hu0 htT) F
    have hmem : Memℓp (fun k : NonzeroLattice d =>
        Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff (Vprop R.D R.ρ m t u F) k) 2 := by
      rw [Torus.memℓp_two_iff]
      exact hs1.congr fun k => by rw [hfc]
    refine ⟨hmem, ?_⟩
    obtain ⟨-, hn⟩ := S7PIDV_norm_ofSeq_sq (σ := m - 1)
      (fun k => NegSobolev.fourierCoeff (Vprop R.D R.ρ m t u F) k) hmem
    have h1 : sobAt (m - 1) (Vprop R.D R.ρ m t u F) ^ 2 ≤ (Ac * sobAt (m - 1) F) ^ 2 := by
      have e1 : sobAt (m - 1) (Vprop R.D R.ρ m t u F) ^ 2 =
          ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ (-(m - 1)) *
            ∑' j, NegSobolev.fourierCoeff F j * pieT R.D R.ρ u t j k) ^ 2 := by
        show ‖(NegSobolev.ofSeq (m - 1) fun k => NegSobolev.fourierCoeff (Vprop R.D R.ρ m t u F) k :
          NegSobolev d (m - 1))‖ ^ 2 = _
        rw [hn]
        exact tsum_congr fun k => by rw [hfc]
      rw [e1, mul_pow, hsob]
      exact hle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hAc0 hsob0) two_ne_zero).1 h1
  refine ⟨?_, hV23.1, hV23.2⟩
  -- conclusion 1
  rcases hst.eq_or_lt with rfl | hlt
  · rw [sub_self, norm_zero, sub_self, Real.zero_rpow (by norm_num)]
    simp
  have hx : 0 < t - s := by linarith
  -- the interpolated Lipschitz bound `E_{m-2} → E_m`
  have hint : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT R.D R.ρ u t j k - pieT R.D R.ρ u s j k)) m)
      ((Kint + 1) * (t - s)) := by
    have ha := hL0 u s t hu hus hst htT
    have hb : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT R.D R.ρ u t j k - pieT R.D R.ρ u s j k))
        (((k : ℝ) + 2) + 1)) (K1 * (t - s)) := by
      have := hL1 u s t hu hus hst htT
      have e : (((k + 1) + 2 : ℕ) : ℝ) = ((k : ℝ) + 2) + 1 := by push_cast; ring
      rw [e] at this
      exact this
    have hip := pie_interp hw (T := fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) *
        (pieT R.D R.ρ u t j k - pieT R.D R.ρ u s j k)) (a := ((k + 2 : ℕ) : ℝ)) (b := ((k : ℝ) + 2) + 1)
      (mul_nonneg hK0 hx.le) (mul_nonneg hK1 hx.le) ha hb hθ0 hθ1
    have hσ : (1 - θ) * ((k + 2 : ℕ) : ℝ) + θ * (((k : ℝ) + 2) + 1) = m := by
      simp only [hθ]; push_cast; ring
    rw [hσ] at hip
    have hbd : (K0 * (t - s)) ^ (1 - θ) * (K1 * (t - s)) ^ θ = Kint * (t - s) := by
      rw [Real.mul_rpow hK0 hx.le, Real.mul_rpow hK1 hx.le, hKint]
      have : (t - s) ^ (1 - θ) * (t - s) ^ θ = t - s := by
        rw [← Real.rpow_add hx]; simp
      calc K0 ^ (1 - θ) * (t - s) ^ (1 - θ) * (K1 ^ θ * (t - s) ^ θ)
          = K0 ^ (1 - θ) * K1 ^ θ * ((t - s) ^ (1 - θ) * (t - s) ^ θ) := by ring
        _ = _ := by rw [this]
    rw [hbd] at hip
    exact S7PIDV_finBd_mono (mul_nonneg hKint0 hx.le) hip (by nlinarith)
  -- the `E_m → E_m` bound of the difference
  have hdiff : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => pieT R.D R.ρ u t j k - pieT R.D R.ρ u s j k) m) (2 * (Am + Am)) := by
    rw [S7PIDV_pieWmat_sub]
    exact S7PIDV_finBd_sub hAm0 hAm0 (hAmb u t hu (hus.trans hst) htT) (hAmb u s hu hus hsT)
  have hℓ : 0 < (Kint + 1) * (t - s) := by positivity
  have hB : 0 < 2 * (Am + Am) := by linarith
  have hseq := S7PIDV_holder_seq hw1 (Δ := fun j k => pieT R.D R.ρ u t j k - pieT R.D R.ρ u s j k) hℓ hB hint hdiff
    (fun j => NegSobolev.fourierCoeff F j) hF2
  -- the norm of the difference
  set X : NegSobolev d m := Vprop R.D R.ρ m t u F - Vprop R.D R.ρ m s u F with hX
  have hcoord : ∀ k, NegSobolev.coord X k = Lattice.jp k.1 ^ (-m) *
      ∑' j, NegSobolev.fourierCoeff F j * (pieT R.D R.ρ u t j k - pieT R.D R.ρ u s j k) := by
    intro k
    have e3 : NegSobolev.coord X k = NegSobolev.coord (Vprop R.D R.ρ m t u F) k -
        NegSobolev.coord (Vprop R.D R.ρ m s u F) k := rfl
    rw [e3, pie_Vprop_coord R.D R.ρ m t u hAm0 (hAmb u t hu (hus.trans hst) htT) F k,
      pie_Vprop_coord R.D R.ρ m s u hAm0 (hAmb u s hu hus hsT) F k, ← mul_sub]
    congr 1
    have r1 := pie_row_summable hw (hAmb u t hu (hus.trans hst) htT)
      (fun j => NegSobolev.fourierCoeff F j) (pie_coeff_summable F) k
    have r2 := pie_row_summable hw (hAmb u s hu hus hsT)
      (fun j => NegSobolev.fourierCoeff F j) (pie_coeff_summable F) k
    rw [← Summable.tsum_sub r1 r2]
    exact tsum_congr fun j => by ring
  have hXsq : ‖X‖ ^ 2 = ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ (-m) *
      ∑' j, NegSobolev.fourierCoeff F j * (pieT R.D R.ρ u t j k - pieT R.D R.ρ u s j k)) ^ 2 := by
    rw [(NegSobolev.coord_sq X).2]
    exact tsum_congr fun k => by rw [hcoord]
  have hmain : ‖X‖ ^ 2 ≤ (4 * Real.sqrt ((Kint + 1) * Am) * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F) ^ 2 := by
    rw [hXsq]
    refine hseq.2.trans ?_
    rw [← hsob]
    have e1 : ((t - s) ^ (1 / 2 : ℝ)) ^ 2 = t - s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
    have e2 : (Real.sqrt ((Kint + 1) * Am)) ^ 2 = (Kint + 1) * Am := Real.sq_sqrt (by positivity)
    have : (4 * Real.sqrt ((Kint + 1) * Am) * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F) ^ 2 =
        16 * (((Kint + 1) * Am) * (t - s)) * sobAt (m - 1) F ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, e1, e2]; ring
    rw [this]
    nlinarith [sq_nonneg (sobAt (m - 1) F)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hmain

end HRS.MC.Sec7.S7PIDV

end
