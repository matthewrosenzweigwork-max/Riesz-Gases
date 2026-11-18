import HRS.MS.FixEqP3Aux36

/-!
# S5.7 `fixed_equation` (worker S57P): the proof, `fixed_equation_proof : type_of% @HRS.Whole.fixed_equation`

Assembly (packets P1-P5): the data of the packets from the hypotheses (`s57p_mkFx`, `s57p_decay_top`, uniqueness by `uniqf_unique_fe` from
`FixedEqFcauHyp.uniq_data`), the pair bounds (`s57p_pair_b`, `s57p_pair_d`; the trivial pair bounds when `Δ_N = ⊤`), the coupling and
cost bound `s57p_core`, and the final real estimate `s57p_final_real`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

theorem s57p_ceil2 (d : ℕ) : 2 * ⌈(d : ℝ) / 2⌉₊ ≤ d + 1 := by
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity)
  have h2 : ((2 * ⌈(d : ℝ) / 2⌉₊ : ℕ) : ℝ) < d + 2 := by push_cast; linarith
  have : 2 * ⌈(d : ℝ) / 2⌉₊ < d + 2 := by exact_mod_cast h2
  omega

/-- the sup of `Δ`-type quantities: the exact shape of `fixed_equation` -/
theorem fixed_equation_proof : type_of% @HRS.Whole.fixed_equation := by
  intro d b hb K hK L' hL' p hp
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hT0 : 0 < b.T := hb.hT
  have hk8 : 8 ≤ b.k := by
    have h1 := hb.hk
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (8 : ℝ) < b.k := by linarith
    exact_mod_cast this.le
  have hce := s57p_ceil2 d
  have hJdef : b.J = 4 * b.k + 4 * d + 40 := rfl
  have hJ1 : 3 * (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ b.J := by omega
  have hJ2 : 3 * ((b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ b.J := by omega
  have hm : (b.J : ℝ) + d < b.m := by have := hb.hm; linarith
  have hP : (d : ℝ) < 2 * (((d : ℝ) + 3) / 2) := by linarith
  have hsum := s57p_summable_J hd1 hm
  have hA := s57pA0_nonneg b
  have hΛc : (0 : ℝ) ≤ max b.Λ 0 := le_max_right _ _
  obtain ⟨Cj, Ca, Cd, hCj0, hCa0, hCd0, hjets, hbdOf⟩ := s57p_fam_bounds hb.hθ hd1 hb.hs0 hb.hsd b.M b.Q b.k b.K b.m b.J hJ1
    hA hΛc hb.hν
  obtain ⟨Cp1, hCp10, hpb⟩ := s57p_pair_b hb.hθ hd1 hb.hs0 hb.hsd b.M b.Q b.k b.K b.K b.m b.J hJ2 b.T hT0.le
  obtain ⟨Cp2, hCp20, hpd⟩ := s57p_pair_d hb.hθ hd1 hb.hs0 hb.hsd b.M b.Q b.k b.K b.K b.m b.J hJ1 hJ2 b.T hT0.le hA hΛc hb.hν
  obtain ⟨Mg, hMg0, hMg⟩ := HRS.MP.RdLGS.rlg_gauss_fourth
  set S : ℝ := ∑' α : MultiIndex d, oscEigenvalue d α ^ ((b.J : ℝ) - b.m) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun α => (Real.rpow_pos_of_pos (oscEv_pos α) _).le
  set Cp1g : ℝ := max Cp1 (Ca + Ca) with hCp1g
  set Cp2g : ℝ := max Cp2 (Cd + Cd) with hCp2g
  obtain ⟨Cfin, hCfin0, hfin⟩ := s57p_final_real (Ca := Ca) (Cd := Cd) (Cp1 := Cp1g) (Cp2 := Cp2g) (S := S)
    (Cpp := s57pC d b.k (((d : ℝ) + 3) / 2)) (C0 := s57pC0 b.T) (Mg := Mg) (T := b.T) hCa0 hCd0
    (le_max_of_le_left hCp10) (le_max_of_le_left hCp20) hS0 (s57pC_nonneg _ _ _)
    (by unfold s57pC0; positivity) hMg0 hT0.le
  refine ⟨Cfin, ?_⟩
  intro νN ν cN c ρN ρ aN a qN q haN ha hqN hq hνN0 hνNs hν0 hνs adjN1 adj1 adjN2 adj2 hFN hF hdens hdrift
  intro Ω _ P _ η₀ hη₀m hη₀ hmom
  -- uniqueness (`uniq_data`)
  obtain ⟨uN, uC⟩ := HRS.MS.UniqF.uniqf_unique_fe b hb hνN0 hνNs hν0 hνs hFN hF hFN.uniq_data hF.uniq_data hdens hdrift
  have densN : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρN t) ∧
      weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρN t) ≤ ENNReal.ofReal b.Λ :=
    fun t ht => ⟨(hdens t ht).2.2.1, (hdens t ht).2.2.2.2.1⟩
  have densC : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (ρ t) ∧
      weightedSupE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) b.L (ρ t) ≤ ENNReal.ofReal b.Λ :=
    fun t ht => ⟨(hdens t ht).2.2.2.1, (hdens t ht).2.2.2.2.2⟩
  have cdN : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (cN t) ∧
      cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (cN t) ≤ ENNReal.ofReal b.Λ :=
    fun t ht => ⟨(hdrift t ht).1, (hdrift t ht).2.2.1⟩
  have cdC : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ∧
      cbNormVecE (b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊) (c t) ≤ ENNReal.ofReal b.Λ :=
    fun t ht => ⟨(hdrift t ht).2.1, (hdrift t ht).2.2.2⟩
  have FxN := s57p_mkFx b hb hνN0 hνNs hFN (fun t ht => (hdens t ht).1) densN cdN adjN1 uN
  have Fx := s57p_mkFx b hb hν0 hνs hF (fun t ht => (hdens t ht).2.1) densC cdC adj1 uC
  have hlev : b.k + 4 + ⌈(d : ℝ) / 2⌉₊ = b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3 := by omega
  rw [hlev] at adj2
  have hL'' : (d : ℝ) + 3 ≤ L' := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have := hb.hs0
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- the finite quantities
  set Δc : ℝ≥0∞ := ⨆ t : Set.Icc (0 : ℝ) b.T, cbNormVecE K (fun x => cN t x - c t x) with hΔc
  set Δρ : ℝ≥0∞ := ⨆ t : Set.Icc (0 : ℝ) b.T, weightedSupE K L' (fun x => ρN t x - ρ t x) with hΔρ
  set τE : ℝ≥0∞ := ⨆ t : Set.Icc (0 : ℝ) b.T, ∫⁻ x, ENNReal.ofReal |ρN t x - ρ t x| with hτE
  have hτE2 : τE ≤ ENNReal.ofReal 2 := iSup_le fun t =>
    s57p_tau_le (fun t ht => (hdens t ht).2.1) (fun t ht => (hdens t ht).1) t.2
  have hτEtop : τE ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hτE2
  set τ : ℝ := τE.toReal with hτdef
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hτ : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∫⁻ x, ENNReal.ofReal |ρN r x - ρ r x| ≤ ENNReal.ofReal τ := fun r hr => by
    rw [hτdef, ENNReal.ofReal_toReal hτEtop]
    exact le_iSup (fun t : Set.Icc (0 : ℝ) b.T => ∫⁻ x, ENNReal.ofReal |ρN t x - ρ t x|) ⟨r, hr⟩
  have hτE' : ENNReal.ofReal τ = τE := ENNReal.ofReal_toReal hτEtop
  have hdualAE : ∀ᵐ ζ ∂P, dualNormE b.k (((d : ℝ) + 3) / 2) (η₀ ζ) < ⊤ := hη₀.mono fun ζ h => s57p_dual_lt_top h
  have hlam : ∀ α : MultiIndex d, 0 ≤ oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) := fun α =>
    Real.rpow_nonneg (oscEigenvalue_pos α).le _
  -- the pair bundle
  obtain ⟨Dt, Pb, hDt⟩ : ∃ Dt : ℝ, ∃ _ : S57pPairBd b.θ b.T b.k b.K b.K b.s b.M b.Q ν νN c cN ρ ρN (s57pA0 b) (max b.Λ 0) b.νstar
      b.m b.J Ca Ca Cd Cd Cp1g Cp2g Dt, ENNReal.ofReal Dt ≤ ENNReal.ofReal |νN - ν| + Δc + Δρ := by
    by_cases hΔ : ENNReal.ofReal |νN - ν| + Δc + Δρ = ⊤
    · exact ⟨1, s57p_pairBd_triv Fx FxN (hbdOf Fx) (hbdOf FxN) hCa0 hCa0 hCd0 hCd0 (le_max_right _ _) (le_max_right _ _),
        by rw [hΔ]; exact le_top⟩
    · have h1 := ENNReal.add_ne_top.1 hΔ
      have h2 := ENNReal.add_ne_top.1 h1.1
      have hK'K : b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3 ≤ K := by omega
      have hK'N : b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3 ≤ b.k + 6 + ⌈(d : ℝ) / 2⌉₊ + 4 + ⌈(d : ℝ) / 2⌉₊ := by omega
      have Δdelta : S57pDelta (b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) L' b.T ν νN c cN ρ ρN |ν - νN| Δc.toReal Δρ.toReal := by
        refine ⟨le_rfl, fun τ' hτ' => ⟨(cdC τ' hτ').1.of_le (by exact_mod_cast hK'N),
          (cdN τ' hτ').1.of_le (by exact_mod_cast hK'N), ?_⟩, fun τ' hτ' => ⟨(densC τ' hτ').1.of_le
          (by exact_mod_cast hK'N), (densN τ' hτ').1.of_le (by exact_mod_cast hK'N), ?_⟩⟩
        · refine (s57p_cbVec_delta hK'K (c τ') (cN τ')).trans ?_
          refine (le_iSup (fun t : Set.Icc (0 : ℝ) b.T => cbNormVecE K (fun x => cN t x - c t x)) ⟨τ', hτ'⟩).trans ?_
          rw [ENNReal.ofReal_toReal h2.2]
        · refine (s57p_wsup_mono_r hK'K L' _).trans ?_
          refine (le_iSup (fun t : Set.Icc (0 : ℝ) b.T => weightedSupE K L' (fun x => ρN t x - ρ t x)) ⟨τ', hτ'⟩).trans ?_
          rw [ENNReal.ofReal_toReal h1.2]
      have hρN2 : ∀ t ∈ Set.Icc (0 : ℝ) b.T, RgDecay ((b.k + 1 + ⌈(d : ℝ) / 2⌉₊ + 3) + 1 + ⌈(d : ℝ) / 2⌉₊ + 2)
          (fun _ => s57pA0 b) (ρN t) := fun t ht => s57p_decay_top b hb densN ht
      have hcN2 := fun t ht => s57p_c_top b cdN (t := t) ht
      have hDν : 0 ≤ |ν - νN| := abs_nonneg _
      have hDc : 0 ≤ Δc.toReal := ENNReal.toReal_nonneg
      have hDρ : 0 ≤ Δρ.toReal := ENNReal.toReal_nonneg
      have hDt0 : 0 ≤ |ν - νN| + Δc.toReal + Δρ.toReal := by positivity
      have hmaxe : max |ν - νN| 0 + max Δc.toReal 0 + max Δρ.toReal 0 = |ν - νN| + Δc.toReal + Δρ.toReal := by
        rw [max_eq_left hDν, max_eq_left hDc, max_eq_left hDρ]
      refine ⟨|ν - νN| + Δc.toReal + Δρ.toReal, ⟨Fx, FxN, hbdOf Fx, hbdOf FxN, hCa0, hCa0, hCd0, hCd0,
        le_trans (by positivity) (le_max_of_le_left hCp10) , le_trans (by positivity) (le_max_of_le_left hCp20),
        hDt0, ?_, ?_⟩, ?_⟩
      · intro α t ht r hr i hi x
        have := hpb (Ca := Ca) (CaN := Ca) (Cd := Cd) (CdN := Cd) Fx FxN adj2 Δdelta hL'' (hbdOf FxN) α t ht r hr i hi x
        rw [hmaxe] at this
        refine this.trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlam α)) hDt0
      · intro α s₀ t₀ hs ht0 htT r hr x
        have := hpd Fx FxN adj2 hρN2 hcN2 Δdelta hL'' α s₀ t₀ hs ht0 htT r hr x
        rw [hmaxe] at this
        refine this.trans ?_
        have hu : 0 ≤ t₀ - s₀ := sub_nonneg.2 ht0
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (hlam α)) hDt0) hu
      · rw [ENNReal.ofReal_add (add_nonneg hDν hDc) hDρ, ENNReal.ofReal_add hDν hDc, abs_sub_comm,
          ENNReal.ofReal_toReal h2.2, ENNReal.ofReal_toReal h1.2]
  have hDt0 : 0 ≤ Dt := Pb.hDt
  obtain ⟨Ω₂, mΩ₂, P₂, h₂, YN, Y, hsolN, hsolC, hbound⟩ := s57p_core hb.hθ hd1 hT0 hP Pb hCj0 hjets hJ1 hm hq hqN hτ0 hτ
    hMg0 hMg hp P η₀ hη₀m hη₀ hdualAE
  refine ⟨Ω₂, mΩ₂, P₂, h₂, YN, Y, hsolN, hsolC, ?_⟩
  have key := hfin (aN := aN) (a := a) (r1 := Real.sqrt qN) (r0 := Real.sqrt q) (τ := τ) (Dt := Dt)
    ((∫⁻ ζ, dualNormE b.k (((d : ℝ) + 3) / 2) (η₀ ζ) ^ p ∂P) ^ (1 / p)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hτ0 hDt0
  rw [Real.sq_sqrt hq, Real.sq_sqrt hqN, hτE'] at key
  refine hbound.trans (key.trans (mul_le_mul' le_rfl ?_))
  refine le_trans ?_ (le_of_eq (add_assoc _ _ _).symm)
  exact add_le_add (mul_le_mul' (add_le_add le_rfl (mul_le_mul' le_rfl hDt)) le_rfl)
    (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add hDt le_rfl)))

end HRS.MS.FixEq
