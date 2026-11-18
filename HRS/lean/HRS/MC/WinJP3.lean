import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP1
import HRS.MC.WinJP2

/-!
# WJ3: P3 `p3_W_fam` (the `W`-kernel family estimates)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section P3Helpers

open HRS.MC.Sec7.PIE HRS.MC.E214K HRS.MC.Sec7.S7PIDI HRS.MC.Sec7.S7PIDV HRS.MC.Sec7.S7PIDT

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

/-- dual plain evolutions at level `a` for the prepared and the stationary regime -/
lemma p_wj3_plain (sd : StatDatum S β₀ m hE) (a : ℝ) :
    ∃ VR Wc : ℝ → ℝ → NegSobolev d a →L[ℝ] NegSobolev d a,
      IsDualEvolution (regime S β₀ hE).D (regime S β₀ hE).ρ a VR ∧
      (∀ T : ℝ, 0 ≤ T → IsPlainEvolution VR T) ∧
      IsDualEvolution (regime sd.Ss S.β sd.hEs).D (regime sd.Ss S.β sd.hEs).ρ a Wc ∧
      (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Wc T) := by
  obtain ⟨-, -, -, -, VR, hVR, hVp, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd (HRS.MC.E213A.isSmoothPositiveTrajectory_of_prepared S) a
  obtain ⟨-, -, -, -, Wc, hWc, hWp, -⟩ :=
    HRS.ThermLin.thermlin_stationary_evolution S (HRS.MC.E214K.regime_thermal S β₀ hE) a
  refine ⟨VR, Wc, hVR, hVp, ?_, hWp⟩
  rw [sd.hD, sd.hρ]
  exact hWc

/-- self, cocycle and linearity of the shifted `Vprop`, from a plain dual evolution -/
lemma p_wj3_prop (R : Regime d) (m b : ℝ) (hb : 0 ≤ b)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hdual : IsDualEvolution R.D R.ρ m Vev) (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) :
    (∀ s : ℝ, 0 ≤ s → ∀ F : NegSobolev d m,
      Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m s s F = F) ∧
    (∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → ∀ F : NegSobolev d m,
      Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u F =
        Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t s
          (Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m s u F)) ∧
    (∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ F G : NegSobolev d m,
      Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u (F - G) =
        Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u F -
          Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u G) := by
  have hop : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ F : NegSobolev d m,
      Vprop (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u F = Vev (b + t) (b + u) F := by
    intro u t hu hut F
    have h := congrFun (u3_vprop_shift R m b hb hu hut) F
    rw [HRS.MC.E213D.vprop_eq_vev R.D R.ρ m Vev hdual (show 0 ≤ b + u by linarith)
      (show b + u ≤ b + t by linarith)] at h
    exact h
  refine ⟨fun s hs F => ?_, fun u s t hu hus hst F => ?_, fun u t hu hut F G => ?_⟩
  · have h0 : 0 ≤ b + s := by linarith
    have h1 := (hplain (b + s) h0).1 (b + s) ⟨h0, le_rfl⟩
    rw [hop s s hs le_rfl, h1, ContinuousLinearMap.one_apply]
  · have hu' : 0 ≤ b + u := by linarith
    have ht' : 0 ≤ b + t := by linarith [hu.trans (hus.trans hst)]
    have h2 := (hplain (b + t) ht').2.1 (b + u) (b + s) (b + t) hu' (by linarith) (by linarith) le_rfl
    have hs0 : 0 ≤ s := hu.trans hus
    rw [hop u t hu (hus.trans hst), hop s t hs0 hst, hop u s hu hus, ← h2]
    rfl
  · rw [hop u t hu hut, hop u t hu hut, hop u t hu hut, map_sub]

/-- the finite-section bound of the difference matrix at level `σ ≥ r`, with decay `e^{-κ(b+u)}` -/
lemma p_wj3_Wmat (sd : StatDatum S β₀ m hE) (σ : ℝ) (hσ : rLvl d ≤ σ) (G : ℝ) (hG : 0 < G) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (u t : ℝ), 0 ≤ u → u ≤ t → t ≤ G →
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (fun j k => pieT (Rp sd b hb).D (Rp sd b hb).ρ u t j k -
          pieT (Rs sd b hb).D (Rs sd b hb).ρ u t j k) σ) (C * Real.exp (-κ * (b + u))) := by
  obtain ⟨C, κ, hC, hκ, hBm⟩ := p_wj2_B S β₀ hE σ hσ
  refine ⟨C, κ, hC, hκ, fun b hb u t hu hut htG => ?_⟩
  have hc := hBm (b + u) (b + t) (by linarith) (by linarith)
  have hmp : ∀ j k, pieT (Rp sd b hb).D (Rp sd b hb).ρ u t j k = pieT S.dyn S.ρ (b + u) (b + t) j k := by
    intro j k
    unfold pieT
    rw [show (Rp sd b hb).D = (regime S β₀ hE).D from rfl,
      show (Rp sd b hb).ρ = fun τ => (regime S β₀ hE).ρ (b + τ) from rfl,
      HRS.MC.E213U2.e213u2_propagator_shift (regime S β₀ hE) hb hG hu hut htG
        (HRS.MC.Sec7.S7PIDV.S7PIDV_isSmooth_realMode k)]
    rfl
  have hms : ∀ j k, pieT (Rs sd b hb).D (Rs sd b hb).ρ u t j k =
      pieT S.dyn (fun _ => (regime S β₀ hE).ρβ) (b + u) (b + t) j k := by
    intro j k
    have h0 := HRS.MC.E213U2.e213u2_propagator_shift (regime sd.Ss S.β sd.hEs) hb hG hu hut htG
      (HRS.MC.Sec7.S7PIDV.S7PIDV_isSmooth_realMode (d := d) k)
    unfold pieT
    rw [show (Rs sd b hb).D = (regime sd.Ss S.β sd.hEs).D from rfl,
      show (Rs sd b hb).ρ = fun τ => (regime sd.Ss S.β sd.hEs).ρ (b + τ) from rfl, h0, sd.hD, sd.hρ]
    rfl
  have e : (fun j k => pieT (Rp sd b hb).D (Rp sd b hb).ρ u t j k -
      pieT (Rs sd b hb).D (Rs sd b hb).ρ u t j k) =
      fun j k => pieT S.dyn S.ρ (b + u) (b + t) j k -
        pieT S.dyn (fun _ => (regime S β₀ hE).ρβ) (b + u) (b + t) j k := by
    funext j k
    rw [hmp j k, hms j k]
  rw [e]
  exact hc

/-- **level `m-1` decay of `W`**: for `F ∈ E_m ∩ E_{m-1}`, `‖W^{t,u} F‖_{E_{m-1}} ≤ Cw e^{-κ(b+u)} ‖F‖_{E_{m-1}}` -/
lemma p_wj3_lvl (sd : StatDatum S β₀ m hE) (G : ℝ) (hG : 0 < G) :
    ∃ Cw κ : ℝ, 0 < Cw ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (u t : ℝ), 0 ≤ u → u ≤ t → t ≤ G →
      ∀ F : NegSobolev d m,
        Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F k) 2 →
        Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff
          (Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t u F - Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t u F) k) 2 ∧
        sobAt (m - 1) (Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t u F -
          Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t u F) ≤ Cw * Real.exp (-κ * (b + u)) * sobAt (m - 1) F := by
  classical
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hrm1 : rLvl d ≤ m - 1 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    unfold rLvl; linarith
  set R : Regime d := regime S β₀ hE with hR
  set R' : Regime d := regime sd.Ss S.β sd.hEs with hR'
  obtain ⟨k0, hk1, hk2, hk3, hkst, -⟩ := HRS.MC.Sec7.S7PIDV.S7PIDV_hyp R m hm 1 one_pos
  obtain ⟨Lp, Acp, Amp, Cbp, -, -, hAmp1, -, hUp⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨Ls, Acs, Ams, Cbs, -, -, hAms1, -, hUs⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R' k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨C, κ, hC, hκ, hW⟩ := p_wj3_Wmat sd (m - 1) hrm1 G hG
  refine ⟨C, κ, hC, hκ, fun b hb u t hu hut htG F hF => ?_⟩
  have hw : ∀ i : NonzeroLattice d, 0 < Lattice.jp i.1 := fun i => Torus.jp_pos i.1
  have hAmp0 : 0 ≤ Amp := by linarith
  have hAms0 : 0 ≤ Ams := by linarith
  have hAp : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (pieT (Rp sd b hb).D (Rp sd b hb).ρ u t) m) Amp := (hUp b hb u u t hu le_rfl hut htG).1
  have hAs : pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
      (pieT (Rs sd b hb).D (Rs sd b hb).ρ u t) m) Ams := (hUs b hb u u t hu le_rfl hut htG).1
  have hF2 : Summable fun j : NonzeroLattice d =>
      (Lattice.jp j.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F j) ^ 2 := (Torus.memℓp_two_iff _).1 hF
  obtain ⟨-, hSdef⟩ := S7PIDV_norm_ofSeq_sq (σ := m - 1) (fun k => NegSobolev.fourierCoeff F k) hF
  have hsob : sobAt (m - 1) F ^ 2 =
      ∑' j : NonzeroLattice d, (Lattice.jp j.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F j) ^ 2 := hSdef
  have hsob0 : 0 ≤ sobAt (m - 1) F := norm_nonneg _
  set X : NegSobolev d m := Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t u F -
    Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t u F with hX
  have hfc : ∀ k, NegSobolev.fourierCoeff X k = ∑' j, NegSobolev.fourierCoeff F j *
      (pieT (Rp sd b hb).D (Rp sd b hb).ρ u t j k - pieT (Rs sd b hb).D (Rs sd b hb).ρ u t j k) := by
    intro k
    have e1 : NegSobolev.fourierCoeff X k =
        NegSobolev.fourierCoeff (Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t u F) k -
          NegSobolev.fourierCoeff (Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t u F) k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_sub]
      rfl
    rw [e1, S7PIDV_fc_V _ _ m t u hAmp0 hAp F k, S7PIDV_fc_V _ _ m t u hAms0 hAs F k]
    have r1 := pie_row_summable hw hAp (fun j => NegSobolev.fourierCoeff F j) (pie_coeff_summable F) k
    have r2 := pie_row_summable hw hAs (fun j => NegSobolev.fourierCoeff F j) (pie_coeff_summable F) k
    rw [← Summable.tsum_sub r1 r2]
    exact tsum_congr fun j => by ring
  have hA0 : 0 ≤ C * Real.exp (-κ * (b + u)) := by positivity
  obtain ⟨hs1, hle⟩ := pie_dual hw hA0 (hW b hb u t hu hut htG) (fun j => NegSobolev.fourierCoeff F j) hF2
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) *
      NegSobolev.fourierCoeff X k) 2 := by
    rw [Torus.memℓp_two_iff]
    exact hs1.congr fun k => by rw [hfc]
  refine ⟨hmem, ?_⟩
  obtain ⟨-, hn⟩ := S7PIDV_norm_ofSeq_sq (σ := m - 1) (fun k => NegSobolev.fourierCoeff X k) hmem
  have h1 : sobAt (m - 1) X ^ 2 ≤ (C * Real.exp (-κ * (b + u)) * sobAt (m - 1) F) ^ 2 := by
    have e1 : sobAt (m - 1) X ^ 2 = ∑' k : NonzeroLattice d, (Lattice.jp k.1 ^ (-(m - 1)) *
        ∑' j, NegSobolev.fourierCoeff F j *
          (pieT (Rp sd b hb).D (Rp sd b hb).ρ u t j k - pieT (Rs sd b hb).D (Rs sd b hb).ρ u t j k)) ^ 2 := by
      show ‖(NegSobolev.ofSeq (m - 1) fun k => NegSobolev.fourierCoeff X k : NegSobolev d (m - 1))‖ ^ 2 = _
      rw [hn]
      exact tsum_congr fun k => by rw [hfc]
    rw [e1, mul_pow, hsob]
    exact hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hA0 hsob0) two_ne_zero).1 h1

lemma p_wj3_exp {κ κ' b x : ℝ} (hκ : κ ≤ κ') (hb : 0 ≤ b) (hbx : b ≤ x) (hκ0 : 0 ≤ κ) :
    Real.exp (-κ' * x) ≤ Real.exp (-κ * b) := by
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_nonneg hκ0 hb, mul_le_mul hκ hbx hb (hκ0.trans hκ)]


/-- **Hölder-`1/2` of `W^{t,u} F` in `t`, with decay** (cocycle `W^{t,u} - W^{s,u} = (V^{t,s} - 1) W^{s,u} + W^{t,s} V̄^{s,u}`) -/
lemma p_wj3_key (sd : StatDatum S β₀ m hE) (G : ℝ) (hG : 0 < G) :
    ∃ H κ : ℝ, 0 ≤ H ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (u s t : ℝ), 0 ≤ u → u ≤ s → s ≤ t → t ≤ G →
      ∀ F : NegSobolev d m,
        Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-(m - 1)) * NegSobolev.fourierCoeff F k) 2 →
        ‖(Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t u F - Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t u F) -
            (Vprop (Rp sd b hb).D (Rp sd b hb).ρ m s u F - Vprop (Rs sd b hb).D (Rs sd b hb).ρ m s u F)‖ ≤
          H * Real.exp (-κ * b) * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F := by
  classical
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  set R : Regime d := regime S β₀ hE with hR
  set R' : Regime d := regime sd.Ss S.β sd.hEs with hR'
  obtain ⟨k0, hk1, hk2, hk3, hkst, -⟩ := HRS.MC.Sec7.S7PIDV.S7PIDV_hyp R m hm 1 one_pos
  obtain ⟨Lp, Acp, Amp, Cbp, hLp, hAcp, hAmp1, hCbp, hUp⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨Ls, Acs, Ams, Cbs, hLs, hAcs, hAms1, hCbs, hUs⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R' k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨L2, κ2, hL2, hκ2, hP2⟩ := p2_W_holder sd G hG
  obtain ⟨Cw, κw, hCw, hκw, hlvl⟩ := p_wj3_lvl sd G hG
  obtain ⟨VR, Wc, hVRd, hVRp, hWcd, hWcp⟩ := p_wj3_plain sd m
  refine ⟨Lp * Cw + L2 * Acs, min κ2 κw, by positivity, lt_min hκ2 hκw, fun b hb u s t hu hus hst htG F hF => ?_⟩
  obtain ⟨hself, hcompP, hsubP⟩ := p_wj3_prop R m b hb VR hVRd hVRp
  obtain ⟨-, hcompS, hsubS⟩ := p_wj3_prop R' m b hb Wc hWcd hWcp
  have hselfS := (p_wj3_prop R' m b hb Wc hWcd hWcp).1
  have hs0 : 0 ≤ s := hu.trans hus
  have hsG : s ≤ G := hst.trans htG
  have hx0 : 0 ≤ t - s := by linarith
  set Vp : ℝ → ℝ → NegSobolev d m → NegSobolev d m :=
    fun t u F => Vprop (Rp sd b hb).D (Rp sd b hb).ρ m t u F with hVp
  set Vs : ℝ → ℝ → NegSobolev d m → NegSobolev d m :=
    fun t u F => Vprop (Rs sd b hb).D (Rs sd b hb).ρ m t u F with hVs
  set x : NegSobolev d m := Vs s u F with hxdef
  set y : NegSobolev d m := Vp s u F - Vs s u F with hydef
  -- the decomposition
  have hdec : (Vp t u F - Vs t u F) - (Vp s u F - Vs s u F) =
      (Vp t s y - Vp s s y) + (Vp t s x - Vs t s x) := by
    have e1 : Vp t u F = Vp t s (Vp s u F) := hcompP u s t hu hus hst F
    have e2 : Vs t u F = Vs t s (Vs s u F) := hcompS u s t hu hus hst F
    have e3 : Vp s s y = y := hself s hs0 y
    have e4 : Vp t s y = Vp t s (Vp s u F) - Vp t s x := hsubP s t hs0 hst (Vp s u F) x
    rw [e3, e4, e1, e2]
    show Vp t s (Vp s u F) - Vs t s x - y = _
    rw [hydef]
    abel
  -- bounds
  obtain ⟨hymem, hysob⟩ := hlvl b hb u s hu hus hsG F hF
  obtain ⟨-, hxmem, hxsob⟩ := (hUs b hb u u s hu le_rfl hus hsG).2.2 F hF
  have h1 : ‖Vp t s y - Vp s s y‖ ≤ Lp * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) y :=
    ((hUp b hb s s t hs0 le_rfl hst htG).2.2 y hymem).1
  have h2 : ‖Vp t s x - Vs t s x‖ ≤
      L2 * (t - s) ^ (1 / 2 : ℝ) * Real.exp (-κ2 * (b + s)) * sobAt (m - 1) x :=
    hP2 b hb s t hs0 hst htG x hxmem
  have hκ : 0 ≤ min κ2 κw := (lt_min hκ2 hκw).le
  have hexp2 : Real.exp (-κ2 * (b + s)) ≤ Real.exp (-min κ2 κw * b) :=
    p_wj3_exp (min_le_left _ _) hb (by linarith) hκ
  have hexpw : Real.exp (-κw * (b + u)) ≤ Real.exp (-min κ2 κw * b) :=
    p_wj3_exp (min_le_right _ _) hb (by linarith) hκ
  have hrpow : 0 ≤ (t - s) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0 _
  have hsob0 : 0 ≤ sobAt (m - 1) F := norm_nonneg _
  set E : ℝ := Real.exp (-min κ2 κw * b) with hE'
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have h1' : ‖Vp t s y - Vp s s y‖ ≤ Lp * Cw * E * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F := by
    refine h1.trans ?_
    have : sobAt (m - 1) y ≤ Cw * E * sobAt (m - 1) F :=
      hysob.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexpw hCw.le) hsob0)
    calc Lp * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) y
        ≤ Lp * (t - s) ^ (1 / 2 : ℝ) * (Cw * E * sobAt (m - 1) F) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg hLp hrpow)
      _ = Lp * Cw * E * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F := by ring
  have h2' : ‖Vp t s x - Vs t s x‖ ≤ L2 * Acs * E * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F := by
    refine h2.trans ?_
    have hxs : sobAt (m - 1) x ≤ Acs * sobAt (m - 1) F := hxsob
    calc L2 * (t - s) ^ (1 / 2 : ℝ) * Real.exp (-κ2 * (b + s)) * sobAt (m - 1) x
        ≤ L2 * (t - s) ^ (1 / 2 : ℝ) * E * (Acs * sobAt (m - 1) F) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hexp2 (mul_nonneg hL2.le hrpow)) hxs
            (norm_nonneg _) (mul_nonneg (mul_nonneg hL2.le hrpow) hE0)
      _ = L2 * Acs * E * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F := by ring
  rw [hdec]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ Lp * Cw * E * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F +
        L2 * Acs * E * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) F := add_le_add h1' h2'
    _ = _ := by ring


/-- **abstract measure-theoretic part**: nodes `p(u) W(t_i,u)` of a causal family `W` with a pointwise bound `N0` and an
`N1 (t-s)^{1/2}` increment bound for `u ≤ s ≤ t` -/
lemma p_wj3_abs {r : ℕ} (Φ : NegSobolev d m → EuclideanSpace ℝ (Fin r))
    (hΦ1 : ∀ x y, ‖Φ x - Φ y‖ ≤ ‖x - y‖) (hΦ0 : ∀ x, ‖Φ x‖ ≤ ‖x‖) (hΦc : Continuous Φ)
    (p : ℝ → ℝ) (B : ℝ) (hp : Measurable p) (hpB : ∀ u, |p u| ≤ B)
    (c c' G : ℝ) (hc : 0 ≤ c) (hcc : c ≤ c') (hc'G : c' ≤ G)
    (W : ℝ → ℝ → NegSobolev d m) (N0 N1 : ℝ) (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1)
    (hz : ∀ t u : ℝ, ¬ u ≤ t → W t u = 0)
    (hb : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ G → ‖W t u‖ ≤ N0)
    (hh : ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ G → ‖W t u - W s u‖ ≤ N1 * (t - s) ^ (1 / 2 : ℝ))
    (hmeas : ∀ t : ℝ, c ≤ t → t ≤ c' →
      AEStronglyMeasurable (fun u => W t u) (volume.restrict (Set.Ioc c c'))) (ν : ℕ) :
    (∀ i ≤ 2 ^ ν, MemLp (fun u => Φ (p u • W (gridPt c c' ν i) u)) 2 (volume.restrict (Set.Ioc c c'))) ∧
    (∀ i j, i ≤ j → j ≤ 2 ^ ν →
      ∫ u in Set.Ioc c c', ‖Φ (p u • W (gridPt c c' ν j) u) - Φ (p u • W (gridPt c c' ν i) u)‖ ^ 2 ≤
        B ^ 2 * (N1 ^ 2 * G + N0 ^ 2) * (gridPt c c' ν j - gridPt c c' ν i)) ∧
    (∀ i ≤ 2 ^ ν, ∫ u in Set.Ioc c c', ‖Φ (p u • W (gridPt c c' ν i) u)‖ ^ 2 ≤
        B ^ 2 * (N1 ^ 2 * G + N0 ^ 2) * (c' - c)) ∧
    (∀ i ≤ 2 ^ ν, AEStronglyMeasurable (fun u => p u • W (gridPt c c' ν i) u)
        (volume.restrict (Set.Ioc c c'))) ∧
    (∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c', ‖p u • W (gridPt c c' ν i) u‖ ≤ B * N0) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hpB 0)
  have hlen : volume.real (Set.Ioc c c') = c' - c := Real.volume_real_Ioc_of_le hcc
  have hGc : c' - c ≤ G := by linarith
  have hmeas' : ∀ i ≤ 2 ^ ν, AEStronglyMeasurable (fun u => p u • W (gridPt c c' ν i) u)
      (volume.restrict (Set.Ioc c c')) := by
    intro i hi
    obtain ⟨h1, h2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    exact hp.aestronglyMeasurable.smul (hmeas _ h1 h2)
  have hbd : ∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c', ‖p u • W (gridPt c c' ν i) u‖ ≤ B * N0 := by
    intro i hi u hu
    obtain ⟨h1, h2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hut : u ≤ gridPt c c' ν i
    · exact mul_le_mul (hpB u) (hb u _ (hc.trans hu.1.le) hut (h2.trans hc'G)) (norm_nonneg _) hB0
    · rw [hz _ _ hut, norm_zero, mul_zero]; exact mul_nonneg hB0 hN0
  have hmem : ∀ i ≤ 2 ^ ν, MemLp (fun u => Φ (p u • W (gridPt c c' ν i) u)) 2
      (volume.restrict (Set.Ioc c c')) := by
    intro i hi
    refine MemLp.of_bound (hΦc.comp_aestronglyMeasurable (hmeas' i hi)) (B * N0) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    exact (hΦ0 _).trans (hbd i hi u hu)
  refine ⟨hmem, ?_, ?_, hmeas', hbd⟩
  · intro i j hij hj
    have hi : i ≤ 2 ^ ν := hij.trans hj
    obtain ⟨hi1, hi2⟩ := S7PIDT_grid_mem c c' hcc ν i hi
    obtain ⟨hj1, hj2⟩ := S7PIDT_grid_mem c c' hcc ν j hj
    have hst : gridPt c c' ν i ≤ gridPt c c' ν j := by
      have := S7PIDT_grid_sub c c' ν i j
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      have h0 : 0 ≤ (c' - c) * ((j : ℝ) - i) / 2 ^ ν :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      linarith
    set s := gridPt c c' ν i with hsdef
    set t := gridPt c c' ν j with htdef
    have htG : t ≤ G := hj2.trans hc'G
    have hr2 : ((t - s) ^ (1 / 2 : ℝ)) ^ 2 = t - s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have hA0 : 0 ≤ B ^ 2 * (N1 ^ 2 * (t - s)) := mul_nonneg (sq_nonneg B)
      (mul_nonneg (sq_nonneg N1) (by linarith))
    -- pointwise majorant
    have hpt : ∀ u ∈ Set.Ioc c c', ‖Φ (p u • W t u) - Φ (p u • W s u)‖ ^ 2 ≤
        B ^ 2 * (N1 ^ 2 * (t - s)) + (Set.Ioc s t).indicator (fun _ => B ^ 2 * N0 ^ 2) u := by
      intro u hu
      have hu0 : 0 ≤ u := hc.trans hu.1.le
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (hΦ1 _ _) 2) ?_
      by_cases hus : u ≤ s
      · have hind : u ∉ Set.Ioc s t := fun h => absurd hus (not_le.2 h.1)
        rw [Set.indicator_of_notMem hind, add_zero, ← smul_sub, norm_smul, Real.norm_eq_abs]
        have hY := hh u s t hu0 hus hst htG
        have h1 : |p u| * ‖W t u - W s u‖ ≤ B * (N1 * (t - s) ^ (1 / 2 : ℝ)) :=
          mul_le_mul (hpB u) hY (norm_nonneg _) hB0
        calc (|p u| * ‖W t u - W s u‖) ^ 2 ≤ (B * (N1 * (t - s) ^ (1 / 2 : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) h1 2
          _ = B ^ 2 * (N1 ^ 2 * ((t - s) ^ (1 / 2 : ℝ)) ^ 2) := by ring
          _ = B ^ 2 * (N1 ^ 2 * (t - s)) := by rw [hr2]
      · have hsu : s < u := lt_of_not_ge hus
        rw [hz s u hus, smul_zero, sub_zero]
        by_cases hut : u ≤ t
        · rw [Set.indicator_of_mem (show u ∈ Set.Ioc s t from ⟨hsu, hut⟩)]
          have h1 : ‖p u • W t u‖ ≤ B * N0 := by
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul (hpB u) (hb u t hu0 hut htG) (norm_nonneg _) hB0
          have := pow_le_pow_left₀ (norm_nonneg _) h1 2
          nlinarith [this]
        · rw [hz t u hut, smul_zero, norm_zero,
            Set.indicator_of_notMem (show u ∉ Set.Ioc s t from fun h => hut h.2), add_zero]
          calc (0 : ℝ) ^ 2 = 0 := by norm_num
            _ ≤ _ := hA0
    have hI1 : Integrable (fun _ : ℝ => B ^ 2 * (N1 ^ 2 * (t - s))) (volume.restrict (Set.Ioc c c')) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hI2 : Integrable ((Set.Ioc s t).indicator (fun _ : ℝ => B ^ 2 * N0 ^ 2))
        (volume.restrict (Set.Ioc c c')) :=
      (integrableOn_const (C := B ^ 2 * N0 ^ 2) measure_Ioc_lt_top.ne).indicator measurableSet_Ioc
    have hind : (volume.restrict (Set.Ioc c c')).real (Set.Ioc s t) = t - s := by
      simp only [measureReal_def]
      rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.2 (Set.Ioc_subset_Ioc hi1 hj2),
        Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    have hcalc : ∫ u in Set.Ioc c c', (B ^ 2 * (N1 ^ 2 * (t - s)) +
        (Set.Ioc s t).indicator (fun _ => B ^ 2 * N0 ^ 2) u) =
        B ^ 2 * (N1 ^ 2 * (t - s)) * (c' - c) + B ^ 2 * N0 ^ 2 * (t - s) := by
      rw [integral_add hI1 hI2, setIntegral_const, integral_indicator_const _ measurableSet_Ioc, hind,
        hlen, smul_eq_mul, smul_eq_mul]
      ring
    have hint : ∫ u in Set.Ioc c c', ‖Φ (p u • W t u) - Φ (p u • W s u)‖ ^ 2 ≤
        ∫ u in Set.Ioc c c', (B ^ 2 * (N1 ^ 2 * (t - s)) +
          (Set.Ioc s t).indicator (fun _ => B ^ 2 * N0 ^ 2) u) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) (hI1.add hI2)
        (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => hpt u hu))
    refine le_trans hint (le_trans (le_of_eq hcalc) ?_)
    have h3 : 0 ≤ B ^ 2 * (N1 ^ 2 * (t - s)) * (G - (c' - c)) := mul_nonneg hA0 (by linarith)
    nlinarith [h3]
  · intro i hi
    have hpt : ∀ u ∈ Set.Ioc c c', ‖Φ (p u • W (gridPt c c' ν i) u)‖ ^ 2 ≤ (B * N0) ^ 2 := fun u hu =>
      pow_le_pow_left₀ (norm_nonneg _) ((hΦ0 _).trans (hbd i hi u hu)) 2
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _)
      (integrableOn_const (C := (B * N0) ^ 2) measure_Ioc_lt_top.ne)
      (ae_restrict_of_forall_mem measurableSet_Ioc hpt)) ?_
    rw [setIntegral_const, hlen, smul_eq_mul]
    have h4 : 0 ≤ B ^ 2 * N1 ^ 2 * G * (c' - c) :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg B) (sq_nonneg N1)) (hc.trans (hcc.trans hc'G))) (by linarith)
    nlinarith [h4]


end P3Helpers

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

open HRS.MC.Sec7.PIE HRS.MC.E214K HRS.MC.Sec7.S7PIDI HRS.MC.Sec7.S7PIDV HRS.MC.Sec7.S7PIDT in
/-- **P3** (`~400`, MED-HIGH).  Analogue of `E213J.e213j_fam` for the difference kernel `kernelNodesW` (the nodes
`p(u)(1_{u ≤ t_i} V^{t_i,u} - 1_{u ≤ t_i} V̄^{t_i,u}) e_k`): for every contraction `Φ : E_m → ℝ^r` (`‖Φ x - Φ y‖ ≤ ‖x - y‖`,
`‖Φ x‖ ≤ ‖x‖`, continuous) the composed nodes are in `L²(c,c']`, their dyadic increments are bounded by
`K₁ B² e^{-2κb} jp^{-2(m-1)} (t_j - t_i)` (exponent `1` in the time step: the chaining threshold), their second moments by
`K₁ B² e^{-2κb} jp^{-2(m-1)} (c'-c)`, the nodes are a.e. strongly measurable, and bounded pointwise by `B Cb e^{-κ b} ‖e_k‖`.
Proof route: split `u ≤ s` / `s < u ≤ t`; cocycle `W^{t,u} - W^{s,u} = (V^{t,s} - 1) W^{s,u} + W^{t,s} V̄^{s,u}`; first term by the
existing Hölder bound `hVd` of `e213i_V_unif_shift` and P1 at `σ = m - 1`, second by P2; pointwise bound by P1 at `σ = m`
(`‖e_k‖_{E_m} = jp^{-m}`). -/
theorem p3_W_fam (sd : StatDatum S β₀ m hE) (G : ℝ) (hG : 0 < G) :
    ∃ K₁ Cb κ : ℝ, 0 ≤ K₁ ∧ 0 ≤ Cb ∧ 0 < κ ∧ ∀ (b : ℝ) (hb : 0 ≤ b) {r : ℕ}
      (Φ : NegSobolev d m → EuclideanSpace ℝ (Fin r)),
      (∀ x y, ‖Φ x - Φ y‖ ≤ ‖x - y‖) → (∀ x, ‖Φ x‖ ≤ ‖x‖) → Continuous Φ →
      ∀ (p : ℝ → ℝ) (B : ℝ), Measurable p → (∀ u, |p u| ≤ B) →
      ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ G → ∀ (k : NonzeroLattice d) (ν : ℕ),
        (∀ i ≤ 2 ^ ν, MemLp (fun u => Φ (kernelNodesW sd b hb c c' ν p (modeVec m k) u i)) 2
            (volume.restrict (Set.Ioc c c'))) ∧
        (∀ i j, i ≤ j → j ≤ 2 ^ ν →
          ∫ u in Set.Ioc c c', ‖Φ (kernelNodesW sd b hb c c' ν p (modeVec m k) u j) -
              Φ (kernelNodesW sd b hb c c' ν p (modeVec m k) u i)‖ ^ 2 ≤
            K₁ * B ^ 2 * Real.exp (-2 * κ * b) * Lattice.jp k.1 ^ (-(2 * (m - 1))) *
              (gridPt c c' ν j - gridPt c c' ν i)) ∧
        (∀ i ≤ 2 ^ ν, ∫ u in Set.Ioc c c', ‖Φ (kernelNodesW sd b hb c c' ν p (modeVec m k) u i)‖ ^ 2 ≤
            K₁ * B ^ 2 * Real.exp (-2 * κ * b) * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (c' - c)) ∧
        (∀ i ≤ 2 ^ ν, AEStronglyMeasurable (fun u => kernelNodesW sd b hb c c' ν p (modeVec m k) u i)
            (volume.restrict (Set.Ioc c c'))) ∧
        (∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c',
          ‖kernelNodesW sd b hb c c' ν p (modeVec m k) u i‖ ≤
            B * (Cb * Real.exp (-κ * b) * ‖modeVec m k‖)) := by
  classical
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hrm : rLvl d ≤ m := rLvl_le hE
  obtain ⟨H, κH, hH, hκH, hkey⟩ := p_wj3_key sd G hG
  obtain ⟨C1, c1, κ1, hC1, hc1, hκ1, hP1⟩ := p1_vprop_compare_op sd m hrm
  obtain ⟨CbK, hCbK0, hkerP⟩ := HRS.MC.E213J.e213j_ker (regime S β₀ hE) m hm G hG
  obtain ⟨CbK', hCbK0', hkerS⟩ := HRS.MC.E213J.e213j_ker (regime sd.Ss S.β sd.hEs) m hm G hG
  have hκ : 0 < min κH κ1 := lt_min hκH hκ1
  refine ⟨H ^ 2 * G + C1 ^ 2, C1, min κH κ1, by positivity, hC1.le, hκ,
    fun b hb {r} Φ hΦ1 hΦ0 hΦc p B hp hpB c c' hc hcc hc'G k ν => ?_⟩
  set κ : ℝ := min κH κ1 with hκdef
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hpB 0)
  set e : NegSobolev d m := modeVec m k with he
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Lattice.jp k.1 ^ (-(2 * (m - 1))) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact Real.rpow_nonneg (Torus.jp_pos k.1).le _
  rw [← hQdef]
  have hsob : sobAt (m - 1) e ^ 2 = Q := by
    rw [he, S7PIDI_sobAt_mode, hQdef, S7PIDI_rpow_sq _ (Torus.jp_pos k.1).le]
  have hnorm_le : ‖e‖ ≤ sobAt (m - 1) e := by
    rw [he, S7PIDI_norm_modeVec, S7PIDI_sobAt_mode]
    exact Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one k.1) (by linarith)
  have hne2 : ‖e‖ ^ 2 ≤ Q :=
    calc ‖e‖ ^ 2 ≤ sobAt (m - 1) e ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
      _ = Q := hsob
  set E1 : ℝ := Real.exp (-κ * b) with hE1
  have hE10 : 0 ≤ E1 := (Real.exp_pos _).le
  have hE1sq : E1 ^ 2 = Real.exp (-2 * κ * b) := by
    rw [hE1, sq, ← Real.exp_add]; congr 1; ring
  set W : ℝ → ℝ → NegSobolev d m := fun t u =>
    causalVec (Rp sd b hb).D (Rp sd b hb).ρ m t u e - causalVec (Rs sd b hb).D (Rs sd b hb).ρ m t u e with hW
  have hnodes : ∀ u i, kernelNodesW sd b hb c c' ν p e u i = p u • W (gridPt c c' ν i) u := by
    intro u i
    unfold kernelNodesW kernelNodes
    rw [hW, smul_sub]
  have hz : ∀ t u : ℝ, ¬ u ≤ t → W t u = 0 := by
    intro t u h
    rw [hW]
    show causalVec (Rp sd b hb).D (Rp sd b hb).ρ m t u e - causalVec (Rs sd b hb).D (Rs sd b hb).ρ m t u e = 0
    rw [S7PIDI_cv_of_not_le _ _ m t u e h, S7PIDI_cv_of_not_le _ _ m t u e h, sub_zero]
  have hbW : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ G → ‖W t u‖ ≤ C1 * E1 * ‖e‖ := by
    intro u t hu hut htG
    rw [hW]
    show ‖causalVec (Rp sd b hb).D (Rp sd b hb).ρ m t u e - causalVec (Rs sd b hb).D (Rs sd b hb).ρ m t u e‖ ≤ _
    rw [S7PIDI_cv_of_le _ _ m t u e hut, S7PIDI_cv_of_le _ _ m t u e hut]
    refine (hP1 b hb u t hu hut e).trans ?_
    have hx : 0 ≤ t - u := sub_nonneg.2 hut
    have h1 : Real.exp (-c1 * (t - u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h2 : Real.exp (-κ1 * (b + u)) ≤ E1 := p_wj3_exp (min_le_right _ _) hb (by linarith) hκ.le
    have hn := norm_nonneg e
    calc C1 * Real.exp (-c1 * (t - u)) * Real.exp (-κ1 * (b + u)) * ‖e‖
        ≤ C1 * 1 * E1 * ‖e‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h1 hC1.le) h2
            (Real.exp_pos _).le (by positivity)) hn
      _ = C1 * E1 * ‖e‖ := by ring
  have hhW : ∀ u s t : ℝ, 0 ≤ u → u ≤ s → s ≤ t → t ≤ G →
      ‖W t u - W s u‖ ≤ (H * E1 * sobAt (m - 1) e) * (t - s) ^ (1 / 2 : ℝ) := by
    intro u s t hu hus hst htG
    have hk := hkey b hb u s t hu hus hst htG e (S7PIDI_memℓp_fc m k)
    rw [hW]
    show ‖(causalVec (Rp sd b hb).D (Rp sd b hb).ρ m t u e - causalVec (Rs sd b hb).D (Rs sd b hb).ρ m t u e) -
      (causalVec (Rp sd b hb).D (Rp sd b hb).ρ m s u e - causalVec (Rs sd b hb).D (Rs sd b hb).ρ m s u e)‖ ≤ _
    rw [S7PIDI_cv_of_le _ _ m t u e (hus.trans hst), S7PIDI_cv_of_le _ _ m t u e (hus.trans hst),
      S7PIDI_cv_of_le _ _ m s u e hus, S7PIDI_cv_of_le _ _ m s u e hus]
    refine hk.trans ?_
    have h2 : Real.exp (-κH * b) ≤ E1 := p_wj3_exp (min_le_left _ _) hb le_rfl hκ.le
    have hrp : 0 ≤ (t - s) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hs0 : 0 ≤ sobAt (m - 1) e := norm_nonneg _
    calc H * Real.exp (-κH * b) * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) e
        ≤ H * E1 * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hH) hrp) hs0
      _ = _ := by ring
  have hmeasW : ∀ t : ℝ, c ≤ t → t ≤ c' →
      AEStronglyMeasurable (fun u => W t u) (volume.restrict (Set.Ioc c c')) := by
    intro t h1 h2
    exact (hkerP b hb c c' hc hcc hc'G e t h1 h2).1.sub (hkerS b hb c c' hc hcc hc'G e t h1 h2).1
  have hN0 : 0 ≤ C1 * E1 * ‖e‖ := by positivity
  have hN1 : 0 ≤ H * E1 * sobAt (m - 1) e := mul_nonneg (mul_nonneg hH hE10) (norm_nonneg _)
  obtain ⟨a1, a2, a3, a4, a5⟩ := p_wj3_abs Φ hΦ1 hΦ0 hΦc p B hp hpB c c' G hc hcc hc'G W (C1 * E1 * ‖e‖)
    (H * E1 * sobAt (m - 1) e) hN0 hN1 hz hbW hhW hmeasW ν
  have hK : B ^ 2 * ((H * E1 * sobAt (m - 1) e) ^ 2 * G + (C1 * E1 * ‖e‖) ^ 2) ≤
      (H ^ 2 * G + C1 ^ 2) * B ^ 2 * Real.exp (-2 * κ * b) * Q := by
    rw [← hE1sq]
    have e1 : (H * E1 * sobAt (m - 1) e) ^ 2 = H ^ 2 * E1 ^ 2 * Q := by rw [mul_pow, mul_pow, hsob]
    have e2 : (C1 * E1 * ‖e‖) ^ 2 ≤ C1 ^ 2 * E1 ^ 2 * Q := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_left hne2 (by positivity)
    have : B ^ 2 * ((H * E1 * sobAt (m - 1) e) ^ 2 * G + (C1 * E1 * ‖e‖) ^ 2) ≤
        B ^ 2 * (H ^ 2 * E1 ^ 2 * Q * G + C1 ^ 2 * E1 ^ 2 * Q) := by
      rw [e1]
      exact mul_le_mul_of_nonneg_left (add_le_add_right e2 _ |>.trans' le_rfl) (sq_nonneg B)
    refine this.trans (le_of_eq ?_)
    ring
  simp only [hnodes]
  refine ⟨a1, fun i j hij hj => ?_, fun i hi => ?_, a4, a5⟩
  · have hΔ : 0 ≤ gridPt c c' ν j - gridPt c c' ν i := by
      rw [S7PIDT_grid_sub]
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    exact (a2 i j hij hj).trans (mul_le_mul_of_nonneg_right hK hΔ)
  · exact (a3 i hi).trans (mul_le_mul_of_nonneg_right hK (by linarith))


end HRS.MC.WinJ

end
