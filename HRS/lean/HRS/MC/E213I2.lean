import HRS.MC.E213I1
import HRS.MC.S7PIDVMain
import HRS.MC.E213F

/-!
# Packet E213I2: translation-uniform constants for `V^{t,u}` (Theorem 2.13)

`e213i_V_holder` is `s7_PID_V_holder_proof` with the constants `L, C` obtained before the density path `μ`
(for a fixed `D`, bundle `(Rg, MB, Λ, VB, ν₀)`, horizon `G`, level `k + 3`); `e213i_V_unif` adds the finite-section
bound `Am` and the operator bound `Cb`; `e213i_V_unif_shift` instantiates the family `μ = fun t => R.ρ (b + t)`, `b ≥ 0`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213I

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- uniform finite-section bound of `pieT u t` at a real exponent, constant before `μ`, including `t = 0` -/
lemma e213i_finBd_unif (hd : 1 ≤ d) (J : ℕ) (hJ : mStar d ≤ J) (D : DynData d) (Rg : PDE.Regime)
    (MB Λ VB ν₀ G : ℝ) (σ : ℝ) (n : ℕ) (hn : 1 ≤ n) (hJ' : n + 1 ≤ J) (h0 : (n : ℝ) < σ)
    (h1 : σ ≤ n + 1) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ μ : ℝ → Torus d → ℝ, AdjointData D.s J Rg MB Λ VB D ν₀ G μ →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ G →
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) σ) A := by
  obtain ⟨A0, hA0, hb⟩ := e213i_finBd_real hd J hJ D Rg MB Λ VB ν₀ G σ n hn hJ' h0 h1
  refine ⟨max A0 1, le_max_right _ _, fun μ hA u t hu hut htT => ?_⟩
  have H : PIEHyp J D μ G := ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩
  rcases (hu.trans hut).eq_or_lt with h | h
  · have ht0 : t = 0 := h.symm
    subst ht0
    have hu0 : u = 0 := le_antisymm hut hu
    subst hu0
    exact S7PIDV_finBd_mono zero_le_one (S7PIDV_finBd_zero H σ) (le_max_right _ _)
  · exact S7PIDV_finBd_mono hA0 (hb μ hA t ⟨h, htT⟩ u ⟨hu, hut⟩) (le_max_left _ _)

/-- **`V^{t,u}` is Hölder-1/2 in `t` from `E_{m-1}` to `E_m` and bounded on `E_{m-1}`, constants before `μ`.** -/
theorem e213i_V_holder (hd : 1 ≤ d) (D : DynData d) (Rg : PDE.Regime) (MB Λ VB ν₀ G : ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkst : mStar d ≤ k) (m : ℝ) (hk2 : (k : ℝ) + 2 < m) (hk3 : m ≤ (k : ℝ) + 3) :
    ∃ L C : ℝ, 0 ≤ L ∧ 0 ≤ C ∧ ∀ μ : ℝ → Torus d → ℝ,
      AdjointData D.s (k + 3) Rg MB Λ VB D ν₀ G μ →
      ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ G →
      ∀ F : NegSobolev d m,
        Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F k) 2 →
        ‖Vprop D μ m t u F - Vprop D μ m s u F‖ ≤ L * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F ∧
        Memℓp (fun k : NonzeroLattice d =>
          Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff (Vprop D μ m t u F) k) 2 ∧
        sobAt (m - 1) (Vprop D μ m t u F) ≤ C * sobAt (m - 1) F := by
  have hJst : mStar d ≤ k + 3 := by omega

  have hw : ∀ i : NonzeroLattice d, 0 < Lattice.jp i.1 := fun i => Torus.jp_pos i.1
  have hw1 : ∀ i : NonzeroLattice d, 1 ≤ Lattice.jp i.1 := fun i => Torus.jp_ge_one i.1
  -- uniform bounds of the matrices at the exponents `m` and `m - 1`
  obtain ⟨Am, hAm1, hAmb0⟩ := e213i_finBd_unif hd (k + 3) hJst D Rg MB Λ VB ν₀ G m (k + 2) (by omega)
    (by omega) (by push_cast; exact hk2) (by push_cast; linarith)
  obtain ⟨Ac, hAc1, hAcb0⟩ := e213i_finBd_unif hd (k + 3) hJst D Rg MB Λ VB ν₀ G (m - 1) (k + 1)
    (by omega) (by omega) (by push_cast; linarith) (by push_cast; linarith)
  -- the Lipschitz bounds at the integer levels `k + 2` and `k + 3`
  obtain ⟨K0, hK0, hL0'⟩ := e213i_lipMat hd (k + 3) D Rg MB Λ VB ν₀ G k hk1 (by omega) (by omega)
  obtain ⟨K1, hK1, hL1'⟩ := e213i_lipMat hd (k + 3) D Rg MB Λ VB ν₀ G (k + 1) (by omega) (by omega)
    (by omega)
  set θ : ℝ := m - ((k : ℝ) + 2) with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  set Kint : ℝ := K0 ^ (1 - θ) * K1 ^ θ with hKint
  have hKint0 : 0 ≤ Kint := mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg hK1 _)
  have hAm0 : 0 ≤ Am := by linarith
  have hAc0 : 0 ≤ Ac := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt ((Kint + 1) * Am) := Real.sqrt_nonneg _
  refine ⟨4 * Real.sqrt ((Kint + 1) * Am), Ac, by positivity, by linarith, fun μ hA u s t hu hus hst htT F hF => ?_⟩
  have hAmb := hAmb0 μ hA
  have hAcb := hAcb0 μ hA
  have hL0 := hL0' μ hA
  have hL1 := hL1' μ hA
  have hsT : s ≤ G := hst.trans htT
  have hF2 : Summable fun j : NonzeroLattice d => (Lattice.jp j.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F j) ^ 2 :=
    (Torus.memℓp_two_iff _).1 hF
  obtain ⟨-, hSdef⟩ := S7PIDV_norm_ofSeq_sq (σ := m - 1) (fun k => NegSobolev.fourierCoeff F k) hF
  have hsob : sobAt (m - 1) F ^ 2 =
      ∑' j : NonzeroLattice d, (Lattice.jp j.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F j) ^ 2 := hSdef
  have hsob0 : 0 ≤ sobAt (m - 1) F := norm_nonneg _
  -- conclusions 2 and 3
  have hV23 : Memℓp (fun k : NonzeroLattice d =>
        Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff (Vprop D μ m t u F) k) 2 ∧
      sobAt (m - 1) (Vprop D μ m t u F) ≤ Ac * sobAt (m - 1) F := by
    have hu0 : u ≤ t := hus.trans hst
    obtain ⟨hs1, hle⟩ := pie_dual hw hAc0 (hAcb u t hu hu0 htT) (fun j => NegSobolev.fourierCoeff F j) hF2
    have hfc : ∀ k, NegSobolev.fourierCoeff (Vprop D μ m t u F) k =
        ∑' j, NegSobolev.fourierCoeff F j * pieT D μ u t j k :=
      S7PIDV_fc_V D μ m t u hAm0 (hAmb u t hu hu0 htT) F
    have hmem : Memℓp (fun k : NonzeroLattice d =>
        Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff (Vprop D μ m t u F) k) 2 := by
      rw [Torus.memℓp_two_iff]
      exact hs1.congr fun k => by rw [hfc]
    refine ⟨hmem, ?_⟩
    obtain ⟨-, hn⟩ := S7PIDV_norm_ofSeq_sq (σ := m - 1)
      (fun k => NegSobolev.fourierCoeff (Vprop D μ m t u F) k) hmem
    have h1 : sobAt (m - 1) (Vprop D μ m t u F) ^ 2 ≤ (Ac * sobAt (m - 1) F) ^ 2 := by
      have e1 : sobAt (m - 1) (Vprop D μ m t u F) ^ 2 =
          ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ (-(m - 1)) *
            ∑' j, NegSobolev.fourierCoeff F j * pieT D μ u t j k) ^ 2 := by
        show ‖(NegSobolev.ofSeq (m - 1) fun k => NegSobolev.fourierCoeff (Vprop D μ m t u F) k :
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
      (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT D μ u t j k - pieT D μ u s j k)) m)
      ((Kint + 1) * (t - s)) := by
    have ha := hL0 u s t hu hus hst htT
    have hb : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT D μ u t j k - pieT D μ u s j k))
        (((k : ℝ) + 2) + 1)) (K1 * (t - s)) := by
      have := hL1 u s t hu hus hst htT
      have e : (((k + 1) + 2 : ℕ) : ℝ) = ((k : ℝ) + 2) + 1 := by push_cast; ring
      rw [e] at this
      exact this
    have hip := pie_interp hw (T := fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) *
        (pieT D μ u t j k - pieT D μ u s j k)) (a := ((k + 2 : ℕ) : ℝ)) (b := ((k : ℝ) + 2) + 1)
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
      (fun j k => pieT D μ u t j k - pieT D μ u s j k) m) (2 * (Am + Am)) := by
    rw [S7PIDV_pieWmat_sub]
    exact S7PIDV_finBd_sub hAm0 hAm0 (hAmb u t hu (hus.trans hst) htT) (hAmb u s hu hus hsT)
  have hℓ : 0 < (Kint + 1) * (t - s) := by positivity
  have hB : 0 < 2 * (Am + Am) := by linarith
  have hseq := S7PIDV_holder_seq hw1 (Δ := fun j k => pieT D μ u t j k - pieT D μ u s j k) hℓ hB hint hdiff
    (fun j => NegSobolev.fourierCoeff F j) hF2
  -- the norm of the difference
  set X : NegSobolev d m := Vprop D μ m t u F - Vprop D μ m s u F with hX
  have hcoord : ∀ k, NegSobolev.coord X k = Lattice.jp k.1 ^ (-m) *
      ∑' j, NegSobolev.fourierCoeff F j * (pieT D μ u t j k - pieT D μ u s j k) := by
    intro k
    have e3 : NegSobolev.coord X k = NegSobolev.coord (Vprop D μ m t u F) k -
        NegSobolev.coord (Vprop D μ m s u F) k := rfl
    rw [e3, pie_Vprop_coord D μ m t u hAm0 (hAmb u t hu (hus.trans hst) htT) F k,
      pie_Vprop_coord D μ m s u hAm0 (hAmb u s hu hus hsT) F k, ← mul_sub]
    congr 1
    have r1 := pie_row_summable hw (hAmb u t hu (hus.trans hst) htT)
      (fun j => NegSobolev.fourierCoeff F j) (pie_coeff_summable F) k
    have r2 := pie_row_summable hw (hAmb u s hu hus hsT)
      (fun j => NegSobolev.fourierCoeff F j) (pie_coeff_summable F) k
    rw [← Summable.tsum_sub r1 r2]
    exact tsum_congr fun j => by ring
  have hXsq : ‖X‖ ^ 2 = ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ (-m) *
      ∑' j, NegSobolev.fourierCoeff F j * (pieT D μ u t j k - pieT D μ u s j k)) ^ 2 := by
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



/-- **Uniform `V` constants.**  For a fixed `D`, bundle `(Rg, MB, Λ, VB, ν₀)`, horizon `G` and level `k + 3` with
`k + 2 < m ≤ k + 3`, there are constants `L Ac Am Cb`, chosen before the density path `μ`, such that for every `μ`
with `AdjointData D.s (k+3) Rg MB Λ VB D ν₀ G μ` and all `0 ≤ u ≤ s ≤ t ≤ G`: the finite-section bound `Am` of the
matrix `pieT u t` at the exponent `m`, the operator bound `Cb` of `V^{t,u}` on `E_m`, and the Hölder-1/2 estimate
(with the `E_{m-1}`-bound `Ac`). -/
theorem e213i_V_unif (hd : 1 ≤ d) (D : DynData d) (Rg : PDE.Regime) (MB Λ VB ν₀ G : ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkst : mStar d ≤ k) (m : ℝ) (hk2 : (k : ℝ) + 2 < m) (hk3 : m ≤ (k : ℝ) + 3) :
    ∃ L Ac Am Cb : ℝ, 0 ≤ L ∧ 0 ≤ Ac ∧ 1 ≤ Am ∧ 0 ≤ Cb ∧ ∀ μ : ℝ → Torus d → ℝ,
      AdjointData D.s (k + 3) Rg MB Λ VB D ν₀ G μ →
      ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ G →
        pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) m) Am ∧
        (∀ F : NegSobolev d m, ‖Vprop D μ m t u F‖ ≤ Cb * ‖F‖) ∧
        ∀ F : NegSobolev d m,
          Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F k) 2 →
          ‖Vprop D μ m t u F - Vprop D μ m s u F‖ ≤ L * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F ∧
          Memℓp (fun k : NonzeroLattice d =>
            Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff (Vprop D μ m t u F) k) 2 ∧
          sobAt (m - 1) (Vprop D μ m t u F) ≤ Ac * sobAt (m - 1) F := by
  have hJst : mStar d ≤ k + 3 := by omega
  obtain ⟨L, Ac, hL, hAc, hhol⟩ := e213i_V_holder hd D Rg MB Λ VB ν₀ G k hk1 hkst m hk2 hk3
  obtain ⟨Am, hAm1, hAmb⟩ := e213i_finBd_unif hd (k + 3) hJst D Rg MB Λ VB ν₀ G m (k + 2) (by omega)
    (by omega) (by push_cast; exact hk2) (by push_cast; linarith)
  have hAm0 : 0 ≤ Am := by linarith
  refine ⟨L, Ac, Am, Am, hL, hAc, hAm1, hAm0, fun μ hA u s t hu hus hst htT => ?_⟩
  have hb := hAmb μ hA u t hu (hus.trans hst) htT
  exact ⟨hb, fun F => pie_Vbound_of_finBd D μ m t u hAm0 hb F, fun F hF => hhol μ hA u s t hu hus hst htT F hF⟩

/-- **Uniform `V` constants along the shifted regime family** `μ_b = fun t => R.ρ (b + t)`, `b ≥ 0`.  The bundle
comes from `HRS.MC.E213F.adjointData_uniform`; the constants do not depend on `b`. -/
theorem e213i_V_unif_shift (R : Regime d) (k : ℕ) (hk1 : 1 ≤ k) (hkst : mStar d ≤ k) (m : ℝ)
    (hk2 : (k : ℝ) + 2 < m) (hk3 : m ≤ (k : ℝ) + 3) (G : ℝ) (hG : 0 < G) :
    ∃ L Ac Am Cb : ℝ, 0 ≤ L ∧ 0 ≤ Ac ∧ 1 ≤ Am ∧ 0 ≤ Cb ∧ ∀ b : ℝ, 0 ≤ b →
      ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ G →
        pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
          (pieT R.D (fun t => R.ρ (b + t)) u t) m) Am ∧
        (∀ F : NegSobolev d m, ‖Vprop R.D (fun t => R.ρ (b + t)) m t u F‖ ≤ Cb * ‖F‖) ∧
        ∀ F : NegSobolev d m,
          Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F k) 2 →
          ‖Vprop R.D (fun t => R.ρ (b + t)) m t u F - Vprop R.D (fun t => R.ρ (b + t)) m s u F‖ ≤
            L * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F ∧
          Memℓp (fun k : NonzeroLattice d =>
            Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff
              (Vprop R.D (fun t => R.ρ (b + t)) m t u F) k) 2 ∧
          sobAt (m - 1) (Vprop R.D (fun t => R.ρ (b + t)) m t u F) ≤ Ac * sobAt (m - 1) F := by
  have hd : 1 ≤ d := by have := R.hd; omega
  obtain ⟨Rg, MB, Λ, VB, ν₀, hbundle⟩ := HRS.MC.E213F.adjointData_uniform R (k + 3)
  obtain ⟨L, Ac, Am, Cb, hL, hAc, hAm, hCb, h⟩ :=
    e213i_V_unif hd R.D Rg MB Λ VB ν₀ G k hk1 hkst m hk2 hk3
  exact ⟨L, Ac, Am, Cb, hL, hAc, hAm, hCb, fun b hb => h _ (hbundle G hG b hb)⟩

end HRS.MC.E213I

end
