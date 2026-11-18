import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP1

/-!
# WJ2: P2 `p2_W_holder` (Hölder-`1/2` with decay for `W^{t,s} = V^{t,s} - V̄^{t,s}`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section P2Helpers

open HRS.MC.Sec7.PIE HRS.MC.E214K HRS.MC.Sec7.S7PIDI HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- `U^{s,s} e_k = e_k` for the adjoint data of a bundle with horizon `T ≥ s ≥ 0` -/
lemma p_wj2_prop_self {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) {s : ℝ}
    (hs0 : 0 ≤ s) (hsT : s ≤ T) (k : NonzeroLattice d) :
    propagator D μ s s (Torus.realMode k) = Torus.realMode k := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  rcases hs0.eq_or_lt with h | h
  · subst h
    exact HRS.A33.prop_self_zero hd D.s D.hs0 D.hsd J Rg MB Λ VB D ν₀ T μ hA (S7PIDV_isSmooth_realMode k)
  · exact HRS.A33.prop_self_pos hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ⟨h, hsT⟩ (pieDom_realMode J k)

/-- the matrix `pieT s s` is the identity -/
lemma p_wj2_pieT_self {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T) {s : ℝ}
    (hs0 : 0 ≤ s) (hsT : s ≤ T) (j k : NonzeroLattice d) :
    pieT D μ s s j k = if j = k then 1 else 0 := by
  classical
  unfold pieT
  rw [p_wj2_prop_self H hs0 hsT k]
  unfold Torus.funRealCoeff
  exact Torus.realMode_orthonormal j k

/-- **abstract Hölder step**: from the `E_m → E_m` bound of the difference matrix and the `E_{m-2} → E_m` bound of
its `w^{-2}`-weighted version, `‖(V - V')x‖² ≤ 4 ℓ B ‖x‖²_{E_{m-1}}`. -/
lemma p_wj2_holder_abs {D : DynData d} {μ μ' : ℝ → Torus d → ℝ} {m t s A1 A2 ℓ B : ℝ}
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (h1 : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ s t) m) A1)
    (h2 : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ' s t) m) A2)
    (hℓ : 0 < ℓ) (hB : 0 < B)
    (hint : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT D μ s t j k - pieT D μ' s t j k)) m) ℓ)
    (hdiff : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => pieT D μ s t j k - pieT D μ' s t j k) m) B)
    (x : NegSobolev d m)
    (hx : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff x k) 2) :
    ‖Vprop D μ m t s x - Vprop D μ' m t s x‖ ^ 2 ≤ 4 * ℓ * B * sobAt (m - 1) x ^ 2 := by
  have hw : ∀ i : NonzeroLattice d, 0 < Lattice.jp i.1 := fun i => Torus.jp_pos i.1
  have hw1 : ∀ i : NonzeroLattice d, 1 ≤ Lattice.jp i.1 := fun i => Torus.jp_ge_one i.1
  have hF2 : Summable fun j : NonzeroLattice d =>
      (Lattice.jp j.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff x j) ^ 2 :=
    (Torus.memℓp_two_iff _).1 hx
  obtain ⟨-, hSdef⟩ := S7PIDV_norm_ofSeq_sq (σ := m - 1) (fun k => NegSobolev.fourierCoeff x k) hx
  have hsob : sobAt (m - 1) x ^ 2 =
      ∑' j : NonzeroLattice d, (Lattice.jp j.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff x j) ^ 2 := hSdef
  have hseq := S7PIDV_holder_seq hw1 (Δ := fun j k => pieT D μ s t j k - pieT D μ' s t j k) hℓ hB hint hdiff
    (fun j => NegSobolev.fourierCoeff x j) hF2
  set X : NegSobolev d m := Vprop D μ m t s x - Vprop D μ' m t s x with hX
  have hcoord : ∀ k, NegSobolev.coord X k = Lattice.jp k.1 ^ (-m) *
      ∑' j, NegSobolev.fourierCoeff x j * (pieT D μ s t j k - pieT D μ' s t j k) := by
    intro k
    have e3 : NegSobolev.coord X k = NegSobolev.coord (Vprop D μ m t s x) k -
        NegSobolev.coord (Vprop D μ' m t s x) k := rfl
    rw [e3, pie_Vprop_coord D μ m t s hA1 h1 x k, pie_Vprop_coord D μ' m t s hA2 h2 x k, ← mul_sub]
    congr 1
    have r1 := pie_row_summable hw h1 (fun j => NegSobolev.fourierCoeff x j) (pie_coeff_summable x) k
    have r2 := pie_row_summable hw h2 (fun j => NegSobolev.fourierCoeff x j) (pie_coeff_summable x) k
    rw [← Summable.tsum_sub r1 r2]
    exact tsum_congr fun j => by ring
  have hXsq : ‖X‖ ^ 2 = ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ (-m) *
      ∑' j, NegSobolev.fourierCoeff x j * (pieT D μ s t j k - pieT D μ' s t j k)) ^ 2 := by
    rw [(NegSobolev.coord_sq X).2]
    exact tsum_congr fun k => by rw [hcoord]
  rw [hXsq]
  refine hseq.2.trans ?_
  rw [← hsob]

/-- **Lipschitz bound of the shifted propagator matrix, `E_{m-2} → E_m`**, constant before the shift `b` and the times. -/
lemma p_wj2_lip (R : Regime d) (k : ℕ) (hk1 : 1 ≤ k) (hkst : PDE.mStar d ≤ k) (m : ℝ)
    (hk2 : (k : ℝ) + 2 < m) (hk3 : m ≤ (k : ℝ) + 3) (G : ℝ) (hG : 0 < G) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b → ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ G →
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT R.D (fun τ => R.ρ (b + τ)) u t j k -
          pieT R.D (fun τ => R.ρ (b + τ)) u s j k)) m) (K * (t - s)) := by
  have hd : 1 ≤ d := by have := R.hd; omega
  have hw : ∀ i : NonzeroLattice d, 0 < Lattice.jp i.1 := fun i => Torus.jp_pos i.1
  obtain ⟨Rg, MB, Λ, VB, ν₀, hbundle⟩ := HRS.MC.E213F.adjointData_uniform R (k + 3)
  obtain ⟨K0, hK0, hL0'⟩ := HRS.MC.E213I.e213i_lipMat hd (k + 3) R.D Rg MB Λ VB ν₀ G k hk1 (by omega)
    (by omega)
  obtain ⟨K1, hK1, hL1'⟩ := HRS.MC.E213I.e213i_lipMat hd (k + 3) R.D Rg MB Λ VB ν₀ G (k + 1) (by omega)
    (by omega) (by omega)
  set θ : ℝ := m - ((k : ℝ) + 2) with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  set Kint : ℝ := K0 ^ (1 - θ) * K1 ^ θ with hKint
  have hKint0 : 0 ≤ Kint := mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg hK1 _)
  refine ⟨Kint, hKint0, fun b hb u s t hu hus hst htT => ?_⟩
  have hL0 := hL0' _ (hbundle G hG b hb)
  have hL1 := hL1' _ (hbundle G hG b hb)
  rcases hst.eq_or_lt with rfl | hlt
  · intro Kf Jf x
    simp [pieWmat]
  have hx : 0 < t - s := by linarith
  have ha := hL0 u s t hu hus hst htT
  have hb' : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT R.D (fun τ => R.ρ (b + τ)) u t j k -
        pieT R.D (fun τ => R.ρ (b + τ)) u s j k)) (((k : ℝ) + 2) + 1)) (K1 * (t - s)) := by
    have := hL1 u s t hu hus hst htT
    have e : (((k + 1) + 2 : ℕ) : ℝ) = ((k : ℝ) + 2) + 1 := by push_cast; ring
    rw [e] at this
    exact this
  have hip := pie_interp hw (T := fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) *
      (pieT R.D (fun τ => R.ρ (b + τ)) u t j k - pieT R.D (fun τ => R.ρ (b + τ)) u s j k))
    (a := ((k + 2 : ℕ) : ℝ)) (b := ((k : ℝ) + 2) + 1)
    (mul_nonneg hK0 hx.le) (mul_nonneg hK1 hx.le) ha hb' hθ0 hθ1
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
  exact hip

/-- **the `E_σ → E_σ` bound of the difference matrix of the unshifted prepared / stationary propagators** -/
lemma p_wj2_B (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) (σ : ℝ) (hσ : rLvl d ≤ σ) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t →
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (fun j k => pieT S.dyn S.ρ u t j k - pieT S.dyn (fun _ => (regime S β₀ hE).ρβ) u t j k) σ)
        (C * Real.exp (-κ * u)) := by
  have hth := HRS.MC.E214K.regime_thermal S β₀ hE
  obtain ⟨C, c, κ, hC, hc, hκ, hcore⟩ := p_wj1_core S hth σ hσ
  obtain ⟨VR, Wc, hVR, hWc⟩ := exists_dual S hth σ
  refine ⟨C, κ, hC, hκ, fun u t hu hut => ?_⟩
  have hM0 : 0 ≤ C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) := by positivity
  have hop : ‖VR t u - Wc t u‖ ≤ C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) := by
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun F => ?_
    rw [ContinuousLinearMap.sub_apply, ← HRS.MC.E213D.vprop_eq_vev S.dyn S.ρ σ VR hVR hu hut F,
      ← HRS.MC.E213D.vprop_eq_vev S.dyn (fun _ => (regime S β₀ hE).ρβ) σ Wc hWc hu hut F]
    exact hcore u t hu hut F
  have h := p_wj1_finBd_dual_sub hM0 S.dyn S.ρ (fun _ => (regime S β₀ hE).ρβ) VR Wc hVR hWc hu hut hop
  refine S7PIDV_finBd_mono hM0 h ?_
  have hx : 0 ≤ t - u := sub_nonneg.2 hut
  have : Real.exp (-c * (t - u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : 0 ≤ C * Real.exp (-κ * u) := by positivity
  calc C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) = Real.exp (-c * (t - u)) * (C * Real.exp (-κ * u)) := by
        ring
    _ ≤ 1 * (C * Real.exp (-κ * u)) := mul_le_mul_of_nonneg_right this h2
    _ = _ := one_mul _

end P2Helpers

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

open HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV in
/-- **P2**.  See `HRS/MC/WinJSpec.lean`. -/
theorem p2_W_holder (sd : StatDatum S β₀ m hE) (G : ℝ) (hG : 0 < G) :
    ∃ L κ : ℝ, 0 < L ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ G →
      ∀ x : NegSobolev d m,
        Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff x k) 2 →
        ‖Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t s x - Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t s x‖ ≤
          L * (t - s) ^ (1 / 2 : ℝ) * Real.exp (-κ * (b + s)) * sobAt (m - 1) x := by
  classical
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hrm : rLvl d ≤ m := rLvl_le hE
  set R : Regime d := regime S β₀ hE with hR
  set R' : Regime d := regime sd.Ss S.β sd.hEs with hR'
  obtain ⟨k0, hk1, hk2, hk3, hkst, -⟩ := HRS.MC.Sec7.S7PIDV.S7PIDV_hyp R m hm 1 one_pos
  have hd1 : 1 ≤ d := by have := R.hd; omega
  obtain ⟨Kp, hKp, hlipp⟩ := p_wj2_lip R k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨Ks, hKs, hlips⟩ := p_wj2_lip R' k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨Lp, Acp, Amp, Cbp, -, -, hAmp1, -, hUp⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨Ls, Acs, Ams, Cbs, -, -, hAms1, -, hUs⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R' k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨C, κ, hC, hκ, hBm⟩ := p_wj2_B S β₀ hE m hrm
  obtain ⟨Rg, MB, Λ₁, VB, ν₀, hbp⟩ := HRS.MC.E213F.adjointData_uniform R (k0 + 3)
  obtain ⟨Rg', MB', Λ₁', VB', ν₀', hbs⟩ := HRS.MC.E213F.adjointData_uniform R' (k0 + 3)
  set Λ' : ℝ := 2 * (Kp + Ks + 1) with hΛ'
  have hΛ'0 : 0 < Λ' := by rw [hΛ']; linarith
  refine ⟨2 * Real.sqrt (Λ' * C), κ / 2, by positivity, by positivity, fun b hb s t hs hst htG x hx => ?_⟩
  have hHp : PIEHyp (k0 + 3) R.D (fun τ => R.ρ (b + τ)) G :=
    ⟨hd1, by omega, Rg, MB, Λ₁, VB, ν₀, hbp G hG b hb⟩
  have hHs : PIEHyp (k0 + 3) R'.D (fun τ => R'.ρ (b + τ)) G :=
    ⟨hd1, by omega, Rg', MB', Λ₁', VB', ν₀', hbs G hG b hb⟩
  have hsG : s ≤ G := hst.trans htG
  have eD : (Rs sd b hb).D = (Rp sd b hb).D := sd.hD
  rw [eD]
  show ‖Vprop R.D (fun τ => R.ρ (b + τ)) m t s x - Vprop R.D (fun τ => R'.ρ (b + τ)) m t s x‖ ≤ _
  rcases hst.eq_or_lt with rfl | hlt
  · -- t = s : both sides vanish
    have e1 : Vprop R.D (fun τ => R.ρ (b + τ)) m s s x = Vprop R.D (fun τ => R'.ρ (b + τ)) m s s x := by
      unfold Vprop
      congr 1
      funext k
      have a1 := p_wj2_prop_self hHp hs hsG k
      have a2 := p_wj2_prop_self hHs hs hsG k
      rw [a1, sd.hD] at *
      rw [a2]
    rw [e1, sub_self, norm_zero, sub_self, Real.zero_rpow (by norm_num)]
    simp
  have hx0 : 0 < t - s := by linarith
  -- self matrices agree
  have hself : ∀ j k, pieT R.D (fun τ => R.ρ (b + τ)) s s j k = pieT R'.D (fun τ => R'.ρ (b + τ)) s s j k := by
    intro j k
    rw [p_wj2_pieT_self hHp hs hsG, p_wj2_pieT_self hHs hs hsG]
  rw [sd.hD] at hself hlips hUs
  -- the finite-section bounds of the two matrices
  have h1 := (hUp b hb s s t hs le_rfl hst htG).1
  have h2 : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (pieT R.D (fun τ => R'.ρ (b + τ)) s t) m) Ams := (hUs b hb s s t hs le_rfl hst htG).1
  have hAm0 : 0 ≤ Amp := by linarith
  have hAm0' : 0 ≤ Ams := by linarith
  -- the Lipschitz bound of the difference
  have hint : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT R.D (fun τ => R.ρ (b + τ)) s t j k -
        pieT R.D (fun τ => R'.ρ (b + τ)) s t j k)) m) (Λ' * (t - s)) := by
    have l1 := hlipp b hb s s t hs le_rfl hst htG
    have l2 := hlips b hb s s t hs le_rfl hst htG
    have hsub := S7PIDV_finBd_sub (mul_nonneg hKp hx0.le) (mul_nonneg hKs hx0.le) l1 l2
    rw [← S7PIDV_pieWmat_sub] at hsub
    have e : (fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT R.D (fun τ => R.ρ (b + τ)) s t j k -
          pieT R.D (fun τ => R.ρ (b + τ)) s s j k) -
        Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT R.D (fun τ => R'.ρ (b + τ)) s t j k -
          pieT R.D (fun τ => R'.ρ (b + τ)) s s j k)) =
        fun j k => Lattice.jp j.1 ^ (-(2 : ℝ)) * (pieT R.D (fun τ => R.ρ (b + τ)) s t j k -
          pieT R.D (fun τ => R'.ρ (b + τ)) s t j k) := by
      funext j k
      rw [hself j k]
      ring
    rw [e] at hsub
    refine S7PIDV_finBd_mono (by positivity) hsub ?_
    rw [hΛ']; nlinarith [mul_nonneg hKp hx0.le, mul_nonneg hKs hx0.le]
  -- the `E_m → E_m` bound of the difference
  have hdiff : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (fun j k => pieT R.D (fun τ => R.ρ (b + τ)) s t j k -
        pieT R.D (fun τ => R'.ρ (b + τ)) s t j k) m) (C * Real.exp (-κ * (b + s))) := by
    have hc := hBm (b + s) (b + t) (by linarith) (by linarith)
    have hmp : ∀ j k, pieT R.D (fun τ => R.ρ (b + τ)) s t j k = pieT S.dyn S.ρ (b + s) (b + t) j k := by
      intro j k
      unfold pieT
      rw [HRS.MC.E213U2.e213u2_propagator_shift R hb hG hs hst htG
        (HRS.MC.Sec7.S7PIDV.S7PIDV_isSmooth_realMode k)]
      rfl
    have hms : ∀ j k, pieT R.D (fun τ => R'.ρ (b + τ)) s t j k =
        pieT S.dyn (fun _ => (regime S β₀ hE).ρβ) (b + s) (b + t) j k := by
      intro j k
      have h0 := HRS.MC.E213U2.e213u2_propagator_shift R' hb hG hs hst htG
        (HRS.MC.Sec7.S7PIDV.S7PIDV_isSmooth_realMode (d := d) k)
      have e1 : propagator R.D (fun τ => R'.ρ (b + τ)) s t (Torus.realMode k) =
          propagator R'.D (fun τ => R'.ρ (b + τ)) s t (Torus.realMode k) := by rw [sd.hD]
      unfold pieT
      rw [e1, h0, sd.hD, sd.hρ]
      rfl
    have e : (fun j k => pieT R.D (fun τ => R.ρ (b + τ)) s t j k -
        pieT R.D (fun τ => R'.ρ (b + τ)) s t j k) =
        fun j k => pieT S.dyn S.ρ (b + s) (b + t) j k -
          pieT S.dyn (fun _ => (regime S β₀ hE).ρβ) (b + s) (b + t) j k := by
      funext j k
      rw [hmp j k, hms j k]
    rw [e]
    exact hc
  have hB0 : 0 < C * Real.exp (-κ * (b + s)) := by positivity
  have habs := p_wj2_holder_abs hAm0 hAm0' h1 h2 (by positivity) hB0 hint hdiff x hx
  have e1 : ((t - s) ^ (1 / 2 : ℝ)) ^ 2 = t - s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have e2 : (Real.sqrt (Λ' * C)) ^ 2 = Λ' * C := Real.sq_sqrt (by positivity)
  have e3 : (Real.exp (-(κ / 2) * (b + s))) ^ 2 = Real.exp (-κ * (b + s)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hsq : (2 * Real.sqrt (Λ' * C) * (t - s) ^ (1 / 2 : ℝ) * Real.exp (-(κ / 2) * (b + s)) *
      sobAt (m - 1) x) ^ 2 =
      4 * (Λ' * (t - s)) * (C * Real.exp (-κ * (b + s))) * sobAt (m - 1) x ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, e1, e2, e3]; ring
  have hsob0 : 0 ≤ sobAt (m - 1) x := norm_nonneg _
  have hrpow : 0 ≤ (t - s) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hrpow) (Real.exp_pos _).le) hsob0) two_ne_zero).1 ?_
  rw [hsq]
  exact habs

end HRS.MC.WinJ

end
