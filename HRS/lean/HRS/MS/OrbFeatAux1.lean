import HRS.MS.UlOrbit
import HRS.MS.UlTie2
import HRS.MS.MovBridgeAux7
import HRS.MS.MovOscAux5

/-!
# S5.2 `orbit_feature_bounded` (packet S52B), part 1: gap analysis and the linear-index orbit bound

**Gap analysis of the frozen row `HRS.Whole.orbit_feature_bounded`** (checked against the library).

1. *Statement.* True and non-vacuous (the coefficient `fixedViscosityCoeff s (-1) Q ν c ρ` has constant drift
   `-Qx + σ - ∇g*ρ`, `Q` an arbitrary matrix, `σ` a Schwartz vector field).  No junk-value trap: all orbit
   features are genuine elements of `𝒦` once `propagatorW` is the classical solution (the `MemLp` branch of
   `orbitFeature` is taken, see `s52b_features_of_data`).
2. *Gap 1 (uniqueness).*  `propagatorW C r t φ` is `Classical.choose` of the classical adjoint solutions
   (`IsClassicalAdjointW`).  The UL-5/UL-6 evolution (`IsUlBackwardEvolution`) is one classical solution, but the
   library proves uniqueness only (a) among `UlClosure` evolutions (`ul_evolution_unique`) and (b) for the coefficients
   `WholeDyn.coeff` of a mean-field dynamics with gradient drift `M∇g*ρ - ∇V` (`Fcau.propagatorW_eq`,
   `s55f_propagatorW_eq_star`; these go through `uloc_uniqueness` / S.A.33 whose engine is written for
   `meanFieldDriftW D`).  The drift `-Qx + σ - ∇g*ρ` with arbitrary `Q` (non symmetric) and non-gradient `σ` is
   NOT of the form `M∇g*ρ - ∇V`; the engine cannot be instantiated.  Hence a uniqueness statement for the
   frozen coefficient is a hypothesis here: `S52bUniq` (OrbFeatAux2).
3. *Gap 2 (index).*  The existential `J` of `ul6_orbit_ul`/`UlTie2` is a sum over derivative orders of
   existential indices and grows quadratically in `k`; the frozen `m > 2k+2d+20+3d+4` then does not give
   `m - J > 2d` (needed for `∑_α λ_α^{(J-m)/2} < ∞`).  Fixed here: `s52b_weighted`, `s52b_schwartz_S`,
   `s52b_orbit_ul1` re-prove the chain with the explicit linear index
   `J = s52bIdx d s (K+2) = 2(K+2) + ⌈s+1⌉ + ⌊d/2⌋ + 1`, `K = k + ⌊d/2⌋ + 1`, i.e. `J ≤ 2k + 3d + 8`.
4. *Reusable (the previous plan was about 400 lines for gap 2; it took about 100 here).* the Hermite base bound is
   `mo_sobolev_emb` on the Schwartz map `φ_α` (`s52b_phi`, `oscNorm N φ_α = λ_α^{(N-m)/2}`); the
   Hilbert-space smoothness of the feature is `GoFeatTie` (generalised in `s52b_features_of_data`); `t`-measurability
   is continuity of `t ↦ ∂_a w(r+T-t)(x)` for the fixed-horizon evolution `w` (`s52b_orbit_data`).

Result of this packet: `orbit_feature_bounded_of_uniq` (OrbFeatTie), the frozen conclusion under the hypothesis
`S52bUniq (fixedViscosityCoeff s (-1) Q ν c ρ) T`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S52B

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- weighted sup bounds of Schwartz functions with an explicit (linear) index of `oscNorm` -/
theorem s52b_weighted (N : ℕ) : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j f x‖ ≤
      C * oscNorm ((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f := by
  induction N with
  | zero =>
    intro j
    have hlt : (j : ℝ) + (d : ℝ) / 2 < ((⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    obtain ⟨C, hC0, hC⟩ := HRS.MS.MovOsc.mo_sobolev_emb (d := d) j _ hlt
    refine ⟨C, hC0, fun f x => ?_⟩
    have := hC f x
    simpa using this
  | succ N ih =>
    intro j
    obtain ⟨C0, hC0, h0⟩ := ih j
    obtain ⟨C1, hC1, h1⟩ := ih (j - 1)
    obtain ⟨Cx, hCx0, hCx⟩ := HRS.MS.MovOsc.mo_xmul (d := d)
      ((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ)
    set n : ℕ := N + 1 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hn
    have hn0 : N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 + 1 = n := by omega
    have hn1 : N + ⌊((j - 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 ≤ n := by
      have : ⌊((j - 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ ≤ ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ :=
        Nat.floor_le_floor (by
          have : ((j - 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.sub_le j 1
          linarith)
      omega
    refine ⟨C0 + d * (C0 * Cx + j * C1), by positivity, fun f x => ?_⟩
    have hw := ul6_w_pos' x
    have hw0 : 0 ≤ (1 + ‖x‖) ^ N := by positivity
    have hf : ContDiff ℝ ∞ (f : Euc d → ℝ) := f.smooth _
    have b1 : oscNorm ((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) + 1 : ℝ) f ≤ oscNorm (n : ℝ) f := by
      have := ul6_osc_mono (a := N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 + 1) (b := n) (by omega) f
      simpa using this
    have b2 : oscNorm ((N + ⌊((j - 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤ oscNorm (n : ℝ) f :=
      ul6_osc_mono hn1 f
    have b0 : oscNorm ((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤ oscNorm (n : ℝ) f :=
      ul6_osc_mono (by omega) f
    have hon : 0 ≤ oscNorm (n : ℝ) f := Real.sqrt_nonneg _
    have hxi : ∀ i : Fin d, (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖) ≤
        C0 * Cx * oscNorm (n : ℝ) f + j * (C1 * oscNorm (n : ℝ) f) := by
      intro i
      have hp := ul6_pt_xmul f hf i j x
      have e1 : (fun y => y i * f y) = ⇑(HRS.MS.MovOsc.mova1_X i f) := funext fun y => by simp
      rw [e1] at hp
      have a1 := h0 (HRS.MS.MovOsc.mova1_X i f) x
      have a2 := h1 f x
      have a3 : oscNorm ((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) ⇑(HRS.MS.MovOsc.mova1_X i f) ≤
          Cx * oscNorm (((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) + 1) f := by
        have := (hCx i f).2
        rwa [e1] at this
      calc (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖)
          ≤ (1 + ‖x‖) ^ N * (‖iteratedFDeriv ℝ j (⇑(HRS.MS.MovOsc.mova1_X i f)) x‖ +
              j * ‖iteratedFDeriv ℝ (j - 1) f x‖) := mul_le_mul_of_nonneg_left hp hw0
        _ = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (⇑(HRS.MS.MovOsc.mova1_X i f)) x‖ +
              j * ((1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ (j - 1) f x‖) := by ring
        _ ≤ C0 * oscNorm ((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) ⇑(HRS.MS.MovOsc.mova1_X i f) +
              j * (C1 * oscNorm ((N + ⌊((j - 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f) := by
            gcongr
        _ ≤ C0 * (Cx * oscNorm (((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) + 1) f) +
              j * (C1 * oscNorm ((N + ⌊((j - 1 : ℕ) : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f) := by gcongr
        _ ≤ C0 * (Cx * oscNorm (n : ℝ) f) + j * (C1 * oscNorm (n : ℝ) f) := by gcongr
        _ = _ := by ring
    have hsum : (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖) ≤
        ∑ i : Fin d, (C0 * Cx * oscNorm (n : ℝ) f + j * (C1 * oscNorm (n : ℝ) f)) := by
      calc (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖)
          ≤ (1 + ‖x‖) ^ N * ((∑ i, |x i|) * ‖iteratedFDeriv ℝ j f x‖) := by
            gcongr; exact ul6_norm_le_sum x
        _ = ∑ i, (1 + ‖x‖) ^ N * (|x i| * ‖iteratedFDeriv ℝ j f x‖) := by
            rw [Finset.sum_mul, Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun i _ => hxi i
    have a0 := h0 f x
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    calc (1 + ‖x‖) ^ (N + 1) * ‖iteratedFDeriv ℝ j f x‖
        = (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j f x‖ +
            (1 + ‖x‖) ^ N * (‖x‖ * ‖iteratedFDeriv ℝ j f x‖) := by ring
      _ ≤ C0 * oscNorm ((N + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f +
          d * (C0 * Cx * oscNorm (n : ℝ) f + j * (C1 * oscNorm (n : ℝ) f)) := add_le_add a0 hsum
      _ ≤ C0 * oscNorm (n : ℝ) f + d * (C0 * Cx * oscNorm (n : ℝ) f + j * (C1 * oscNorm (n : ℝ) f)) := by
          gcongr
      _ = _ := by ring


/-- the `oscNorm` index of the symbol bound: linear in `mm` -/
def s52bIdx (d : ℕ) (s : ℝ) (mm : ℕ) : ℕ := 2 * mm + ⌈s + 1⌉₊ + ⌊(d : ℝ) / 2⌋₊ + 1

theorem s52b_schwartz_S (s : ℝ) (mm : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : SchwartzMap (Euc d) ℝ, ul6S (-(s + 1)) mm (C * oscNorm ((s52bIdx d s mm : ℕ) : ℝ) f) f := by
  have hj : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
      (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) * ‖iteratedFDeriv ℝ j f x‖ ≤
        C * oscNorm (((j + ⌈s + 1⌉₊) + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f :=
    fun j => s52b_weighted (j + ⌈s + 1⌉₊) j
  choose C hC0 hC using hj
  refine ⟨∑ j ∈ Finset.range (mm + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun f j hj x => ?_⟩
  have hjm : j ∈ Finset.range (mm + 1) := Finset.mem_range.2 (by omega)
  have hw := ul6_w_pos' x
  have h1 : (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) * (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) ≥ 1 := by
    have hnat : ((j + ⌈s + 1⌉₊ : ℕ) : ℝ) = (j : ℝ) + (⌈s + 1⌉₊ : ℝ) := by push_cast; ring
    rw [← Real.rpow_natCast, hnat, ← Real.rpow_add hw]
    refine Real.one_le_rpow (by linarith [norm_nonneg x]) ?_
    have : s + 1 ≤ (⌈s + 1⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hq : 0 ≤ (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := Real.rpow_nonneg hw.le _
  have hidx : (j + ⌈s + 1⌉₊) + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 ≤ s52bIdx d s mm := by
    have hfl : ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ = ⌊(d : ℝ) / 2⌋₊ + j := by
      rw [add_comm, Nat.floor_add_natCast (by positivity)]
    unfold s52bIdx
    omega
  have h2 : ‖iteratedFDeriv ℝ j f x‖ ≤
      C j * oscNorm (((j + ⌈s + 1⌉₊) + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f *
        (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := by
    have := hC j f x
    have hp : 0 < (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) := by positivity
    calc ‖iteratedFDeriv ℝ j f x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ *
          ((1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) * (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊)) := by
          nlinarith [norm_nonneg (iteratedFDeriv ℝ j f x)]
      _ = (1 + ‖x‖) ^ (j + ⌈s + 1⌉₊) * ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ (-(s + 1) - (j : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hq
  refine h2.trans ?_
  have hosc : oscNorm (((j + ⌈s + 1⌉₊) + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤
      oscNorm ((s52bIdx d s mm : ℕ) : ℝ) f := ul6_osc_mono hidx f
  have hCj : C j ≤ ∑ j ∈ Finset.range (mm + 1), C j :=
    Finset.single_le_sum (f := C) (fun _ _ => hC0 _) hjm
  have hC00 : 0 ≤ ∑ j ∈ Finset.range (mm + 1), C j := Finset.sum_nonneg fun j _ => hC0 j
  exact mul_le_mul_of_nonneg_right (mul_le_mul hCj hosc (Real.sqrt_nonneg _) hC00) hq


/-- **The orbit datum `L f` in `H^K_ul` with the linear index `s52bIdx d s (K+2)`** (replaces the existential `J`
of `ul6_orbit_ul`, which grows quadratically). -/
theorem s52b_orbit_ul1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {θ : Euc d → ℝ}
    (hθ : IsUlCutoff θ) (K : ℕ) (ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (σ : Euc d → Euc d)
    (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) (c : Euc d → Euc d)
    (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) :
    ∃ Cfin : ℝ, 0 ≤ Cfin ∧ ∀ f : SchwartzMap (Euc d) ℝ,
      ulNormE K θ (ul6L s Q ν c ρ f 1) ≤
        ENNReal.ofReal (Cfin * oscNorm ((s52bIdx d s (K + 2) : ℕ) : ℝ) f) := by
  obtain ⟨C1, hC10, hC1⟩ := s52b_schwartz_S (d := d) s (K + 2)
  obtain ⟨ψ, hψ⟩ := hρ
  have hρr : UlRapid ρ := by rw [← hψ]; exact ult_schwartz_rapid ψ
  choose φ hφ using hσ
  have hσr : ∀ i, UlRapid (fun x => σ x i) := fun i => by rw [← hφ i]; exact ult_schwartz_rapid (φ i)
  obtain ⟨C2, hC20, hC2⟩ := ul6_L_step (by omega) hs0 hsd ν Q hρr hσr hc K
  obtain ⟨Cu, hCu0, hCu⟩ := ul6_ul_of_S hθ K
  refine ⟨Cu * (C2 * C1), by positivity, fun f => ?_⟩
  obtain ⟨hcd0, hdec0, _⟩ := orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ (fun i => ⟨φ i, hφ i⟩) c hc f 0
  have hsym : UlSym (-(s + 1)) (⇑f : Euc d → ℝ) :=
    ⟨hcd0, fun m' => by
      obtain ⟨C, hC0, hC⟩ := hdec0 m'
      refine ⟨C, hC0, fun x => ?_⟩
      rw [show -(s + 1) - (m' : ℝ) = -(s + 1 + (m' : ℝ)) by ring]
      exact hC x⟩
  have hS := hC2 _ _ hsym (hC1 f)
  have hcd1 : ContDiff ℝ ∞ (ul6L s Q ν c ρ f 1) :=
    (orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ (fun i => ⟨φ i, hφ i⟩) c hc f 1).1
  have e : ul6L s Q ν c ρ f 1 = fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 (⇑f) x := by
    rw [ul6L_succ]; rfl
  have h1 := hCu (-(s + 1)) _ _ (by linarith) hcd1 (by rw [e]; exact hS)
  refine h1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring


/-- the normalised Hermite test function `φ_α = λ_α^{-m/2} h_α` as a Schwartz map, with its `oscNorm`s -/
theorem s52b_phi (m : ℝ) (α : MultiIndex d) : ∃ f : SchwartzMap (Euc d) ℝ,
    (⇑f : Euc d → ℝ) = oscTestFun m α ∧
      ∀ N : ℕ, oscNorm (N : ℝ) f = oscEigenvalue d α ^ (((N : ℝ) - m) / 2) := by
  obtain ⟨Φ, hΦ⟩ := HRS.MS.MovOsc.mova3c_hermite_schwartz (d := d) _ α rfl
  set c0 : ℝ := oscEigenvalue d α ^ (-(m / 2)) with hc0
  refine ⟨c0 • Φ, ?_, fun N => ?_⟩
  · funext x
    simp [oscTestFun, hΦ, hc0]
  · have hf : (⇑(c0 • Φ) : Euc d → ℝ) = HRS.MS.MovOsc.mo_hsum {α} (fun _ => c0) := by
      funext x
      simp [HRS.MS.MovOsc.mo_hsum, hΦ]
    have h2 := HRS.MS.MovOsc.mo_hsum_oscNorm_sq (N : ℝ) {α} (fun _ => c0)
    rw [← hf] at h2
    simp only [Finset.sum_singleton] at h2
    have hpos := oscEv_pos (d := d) α
    have h3 : 0 ≤ oscNorm (N : ℝ) (⇑(c0 • Φ)) := Real.sqrt_nonneg _
    have h4 : 0 ≤ oscEigenvalue d α ^ (((N : ℝ) - m) / 2) := Real.rpow_nonneg hpos.le _
    have h5 : (oscEigenvalue d α ^ (((N : ℝ) - m) / 2)) ^ 2 = oscEigenvalue d α ^ ((N : ℝ) - m) :=
      rpow_half_sq _ _ hpos
    have h6 : c0 ^ 2 = oscEigenvalue d α ^ (-m) := by
      rw [hc0, ← rpow_half_sq (-m) _ hpos, neg_div]
    have h7 : oscEigenvalue d α ^ (N : ℝ) * c0 ^ 2 = oscEigenvalue d α ^ ((N : ℝ) - m) := by
      rw [h6, ← Real.rpow_add hpos]; ring_nf
    nlinarith [sq_nonneg (oscNorm (N : ℝ) (⇑(c0 • Φ)) - oscEigenvalue d α ^ (((N : ℝ) - m) / 2)),
      sq_nonneg (oscNorm (N : ℝ) (⇑(c0 • Φ)) + oscEigenvalue d α ^ (((N : ℝ) - m) / 2))]


theorem s52b_exists_ulCutoff (d : ℕ) : ∃ θ : Euc d → ℝ, IsUlCutoff θ := by
  obtain ⟨χ, hχ⟩ := HRS.MS.Ul.ul0_exists_ulocCutoff d
  set a : ℝ := 2 * d + 1 with ha
  have ha0 : 0 < a := by positivity
  set e : Euc d ≃ₜ Euc d := Homeomorph.smulOfNeZero (a⁻¹) (inv_ne_zero ha0.ne') with he
  refine ⟨fun x => χ (a⁻¹ • x), ?_, ?_, fun x hx => ?_⟩
  · exact hχ.1.comp (contDiff_const_smul _)
  · exact hχ.2.1.comp_homeomorph e
  · apply hχ.2.2.2.2
    rw [mem_closedBall_zero_iff]
    have h1 : ‖x‖ ≤ ∑ i, |x i| := ult_norm_le_sum_abs x
    have h2 : ∑ i, |x i| ≤ ∑ _i : Fin d, (2 : ℝ) := Finset.sum_le_sum fun i _ => hx i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha0)]
    rw [inv_mul_le_iff₀ ha0]
    linarith

end HRS.MS.S52B
