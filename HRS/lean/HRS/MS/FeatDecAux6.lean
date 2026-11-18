import HRS.MS.FeatDecAux5

/-!
# S8.5 `feature_decay`, part 6 (S85 packet): weighted orbit data `∂_a U(r,t) L φ_α`

`s85_orbit_weighted`: for the stationary Schwartz coefficient `C = (⟨s, -1, quadV Q 0, ν⟩).coeff (fun _ => ρ)`
(`0 ≤ s < d`, `ν > 0`, `ρ` a Schwartz density) there are `Co` and an oscillator index `J` such that for all Hermite indices `α`, all
`a`, all `0 ≤ r ≤ t ≤ T` and `j ≤ n` (`n ≥ 2`):
`‖D^j ∂_a U(r,t) L φ_α (x)‖ ≤ Co λ_α^{(J-m)/2} ⟨x⟩^{-(s+2+j)}` and `∂_a U(r,t) L φ_α ∈ C^n`.
Proof: `s85_adjoint_decay` (with the explicit-order UL witness for `UlAdjointInput`) applied to the datum `Lφ_α`, whose
decay `‖Lφ_α‖_{k,s+1}` and ul-norm are bounded by `C λ_α^{·}` (`ul6_L_step`, `s52b_schwartz_S`, `s52b_orbit_ul1`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Adj HRS.MS.S52B HRS.MS.UlW

variable {d : ℕ}

theorem s85_cdiff_nat {f : Euc d → ℝ} (h : ContDiff ℝ ∞ f) (N : ℕ) :
    ContDiff ℝ (N : WithTop ℕ∞) f := h.of_le (by exact_mod_cast le_top)

theorem s85_orbit_weighted (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (n : ℕ)
    (hn : 2 ≤ n) (m : ℝ) {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (ρ : Euc d → ℝ) (hρ : IsSchwartzDensity ρ) :
    ∃ Co : ℝ, 0 ≤ Co ∧ ∃ J : ℕ, (J : ℝ) ≤ 2 * (n : ℝ) + 2 * d + s + 20 ∧
      ∀ (α : MultiIndex d) (a : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T →
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a (propagatorW
        ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) r t
        (generatorW ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) t
          (oscTestFun m α))) x) ∧
      ∀ j ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun x => gradComp a (propagatorW
        ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) r t
        (generatorW ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) t
          (oscTestFun m α))) x) x‖ ≤
        Co * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * jbracket x ^ (-(s + 2 + (j : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  set k : ℕ := n + 1 with hk
  set L : ℝ := (d : ℝ) + k + s + 5 with hL
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    simp only [hL]; linarith
  have hLlt : (d : ℝ) + k + s + 4 < L := by simp only [hL]; linarith
  obtain ⟨ψ, hψ⟩ := hρ.2
  have hρr : UlRapid ρ := by rw [← hψ]; exact ult_schwartz_rapid ψ
  obtain ⟨Λ, hΛ⟩ := s85_wse_of_rapid hρr (k + 2) hL0
  have hρsm : ContDiff ℝ ((k + 2 : ℕ) : WithTop ℕ∞) ρ := s85_cdiff_nat hρr.1 (k + 2)
  obtain ⟨K, hK⟩ := s85_witness5 hd s hs0 hsd θ hθ (k + 2) (by omega) T ν Q (-1) 0 ρ hT hν hQ hρ
  obtain ⟨Cad, hCad⟩ := s85_adjoint_decay hd θ s hs0 hsd (-1) Q hQ 0 T ν k L Λ K hLlt
  -- the datum
  set σ : Euc d → Euc d := fun _ => 0 with hσdef
  set c : Euc d → Euc d := fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x with hc
  have hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i := fun i => ⟨0, by ext x; simp [hσdef]⟩
  have hσr : ∀ i, UlRapid (fun x => σ x i) := fun i => by
    obtain ⟨φ, hφ⟩ := hσ i
    rw [← hφ]; exact ult_schwartz_rapid φ
  have hcoeff : (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ) =
      fixedViscosityCoeff s (-1) Q ν c ρ := by
    rw [ulw_coeff_eq (s := s) (ν := ν) (-1) Q hQ 0 ρ]
    congr 1
    funext x
    simp [hc, hσdef, Torus.matVec]
  set K' : ℕ := k + 3 + ⌈(d : ℝ) / 2⌉₊ with hK'
  obtain ⟨Cfin, hCfin0, hCfin⟩ := s52b_orbit_ul1 hd hs0 hsd hθ K' ν Q ρ ⟨ψ, hψ⟩ σ hσ c rfl
  obtain ⟨C1, hC10, hC1⟩ := s52b_schwartz_S (d := d) s (k + 2)
  obtain ⟨C2, hC20, hC2⟩ := ul6_L_step hd1 hs0 hsd ν Q hρr hσr (c := c) rfl k
  set idxU : ℕ := s52bIdx d s (K' + 2) with hidxU
  set idxD : ℕ := s52bIdx d s (k + 2) with hidxD
  set J : ℕ := max idxU idxD with hJ
  set Cad' : ℝ := max Cad 0 * (C2 * C1 + Cfin) with hCad'
  have hCad'0 : 0 ≤ Cad' := by positivity
  have hJle : (J : ℝ) ≤ 2 * (n : ℝ) + 2 * d + s + 20 := by
    have hc1 : (⌈(d : ℝ) / 2⌉₊ : ℝ) < (d : ℝ) / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hc2 : (⌈s + 1⌉₊ : ℝ) < s + 1 + 1 := Nat.ceil_lt_add_one (by linarith)
    have hf : (⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
    have hU : (idxU : ℝ) ≤ 2 * (n : ℝ) + 2 * d + s + 20 := by
      simp only [hidxU, s52bIdx, hK', hk]; push_cast; linarith
    have hD : (idxD : ℝ) ≤ 2 * (n : ℝ) + 2 * d + s + 20 := by
      simp only [hidxD, s52bIdx, hk]; push_cast; linarith
    simp only [hJ]
    rw [Nat.cast_max]
    exact max_le hU hD
  refine ⟨(d : ℝ) ^ (n + 1) * Cad', by positivity, J, hJle, fun α a r t hr hrt htT => ?_⟩
  obtain ⟨f, hf, hfN⟩ := s52b_phi (d := d) m α
  have hosc_nn : ∀ N : ℝ, 0 ≤ oscNorm N f := fun N => Real.sqrt_nonneg _
  set C : WholeCoeff d := (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ) with hCdef
  set g : Euc d → ℝ := generatorW C t (oscTestFun m α) with hg
  have hgeq : g = ul6L s Q ν c ρ f 1 := by
    have e : ul6L s Q ν c ρ f 1 = fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 (⇑f) x := by
      rw [ul6L_succ]; rfl
    rw [e, hg, hcoeff, s52b_gen_const, ← hf]
  have hgcd : ContDiff ℝ ∞ g := by
    rw [hgeq]
    exact (orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ hσ c rfl f 1).1
  have hul : ulNormE K' θ g ≤ ENNReal.ofReal (Cfin * oscNorm (idxU : ℝ) f) := by
    rw [hgeq]; exact hCfin f
  have hsym : UlSym (-(s + 1)) (⇑f : Euc d → ℝ) := by
    obtain ⟨hcd0, hdec0, _⟩ := orbitData_decay hd hs0 hsd ν Q ρ ⟨ψ, hψ⟩ σ hσ c rfl f 0
    refine ⟨hcd0, fun m' => ?_⟩
    obtain ⟨C', hC0, hC'⟩ := hdec0 m'
    refine ⟨C', hC0, fun x => ?_⟩
    rw [show -(s + 1) - (m' : ℝ) = -(s + 1 + (m' : ℝ)) by ring]
    exact hC' x
  have hS := hC2 _ (⇑f) hsym (hC1 f)
  have hdecg : decayNormE k (s + 1) g ≤ ENNReal.ofReal (C2 * (C1 * oscNorm (idxD : ℝ) f)) := by
    have hB0 : 0 ≤ C2 * (C1 * oscNorm (idxD : ℝ) f) :=
      mul_nonneg hC20 (mul_nonneg hC10 (hosc_nn _))
    refine u2_decayNormE_le (by linarith) hB0 (fun j hj x => ?_)
    have e : g = fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 (⇑f) x := by
      rw [hgeq]
      have e' : ul6L s Q ν c ρ f 1 = fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 (⇑f) x := by
        rw [ul6L_succ]; rfl
      exact e'
    rw [e]
    have := hS j hj x
    rwa [show -(s + 1) - (j : ℝ) = -((s + 1) + (j : ℝ)) by ring] at this
  have hulfin : ulNormE K' θ g < ⊤ := lt_of_le_of_lt hul ENNReal.ofReal_lt_top
  have hgK : ContDiff ℝ (K' : WithTop ℕ∞) g := hgcd.of_le (by exact_mod_cast le_top)
  obtain ⟨hFc, hFd⟩ := hCad ν ρ hν.le le_rfl hρsm hΛ hK r t hr hrt htT g hgK hulfin
  -- combine
  set F : Euc d → ℝ := propagatorW C r t g with hF
  have hoscJ1 : oscNorm (idxD : ℝ) f ≤ oscNorm (J : ℝ) f :=
    ul6_osc_mono (le_max_right _ _) f
  have hoscJ2 : oscNorm (idxU : ℝ) f ≤ oscNorm (J : ℝ) f :=
    ul6_osc_mono (le_max_left _ _) f
  have hosc0 : 0 ≤ oscNorm (J : ℝ) f := Real.sqrt_nonneg _
  have hB : decayNormE k (s + 1) F ≤ ENNReal.ofReal (Cad' * oscNorm (J : ℝ) f) := by
    refine hFd.trans ?_
    have h1 : decayNormE k (s + 1) g + ulNormE K' θ g ≤
        ENNReal.ofReal (C2 * (C1 * oscNorm (idxD : ℝ) f) + Cfin * oscNorm (idxU : ℝ) f) := by
      rw [ENNReal.ofReal_add (mul_nonneg hC20 (mul_nonneg hC10 (hosc_nn _)))
        (mul_nonneg hCfin0 (hosc_nn _))]
      exact add_le_add hdecg hul
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left Cad 0)) h1).trans ?_
    rw [← ENNReal.ofReal_mul (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : C2 * (C1 * oscNorm (idxD : ℝ) f) + Cfin * oscNorm (idxU : ℝ) f ≤
        (C2 * C1 + Cfin) * oscNorm (J : ℝ) f := by
      have a1 : C2 * (C1 * oscNorm (idxD : ℝ) f) ≤ C2 * C1 * oscNorm (J : ℝ) f := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hoscJ1 (by positivity)
      have a2 : Cfin * oscNorm (idxU : ℝ) f ≤ Cfin * oscNorm (J : ℝ) f :=
        mul_le_mul_of_nonneg_left hoscJ2 hCfin0
      nlinarith
    calc max Cad 0 * (C2 * (C1 * oscNorm (idxD : ℝ) f) + Cfin * oscNorm (idxU : ℝ) f)
        ≤ max Cad 0 * ((C2 * C1 + Cfin) * oscNorm (J : ℝ) f) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = Cad' * oscNorm (J : ℝ) f := by rw [hCad']; ring
  have hB0 : 0 ≤ Cad' * oscNorm (J : ℝ) f := mul_nonneg hCad'0 (hosc_nn _)
  have hpt : ∀ j ≤ n + 1, ∀ (I : Fin j → Fin d) (x : Euc d),
      jbracket x ^ (s + 1 + (j : ℝ)) * |partialDeriv I F x| ≤ Cad' * oscNorm (J : ℝ) f :=
    fun j hj I x => s85_decay_pt hB0 hB j hj I x
  have hFc' : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F := hFc
  obtain ⟨hcd, hbd⟩ := s85_gradcomp_bound s n hd1 hFc' hB0 hpt a
  refine ⟨hcd, fun j hj x => ?_⟩
  refine (hbd j hj x).trans (le_of_eq ?_)
  rw [hfN J]
  ring

end HRS.MS.S85
