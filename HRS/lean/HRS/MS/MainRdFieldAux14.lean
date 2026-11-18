import HRS.MS.MainRdFieldAux13
import HRS.MS.PathFidiAux7
import HRS.MS.MainRdFieldAux3
import HRS.MS.SuppU3
import HRS.MH.CoercTestW7e

/-!
# S.A.6, packet P8a: `main_rd_field` for `Λ ≥ 1`

`sa6_main_core`: the statement of `main_rd_field` for `1 ≤ Λ`.  The a.e.-in-time injectivity of the flow (needed by the
pathwise cutoff estimate) comes from `sa6_inj_N`, i.e. `sa26_flow_inj_all` (collision-free branch, Cepa-Lepingle
occupation, and the null contact occupation of the `d = 1` contact-allowing branch).  Proof: S.B.5 (`sa6_B5`), the
coercivity pair, the cutoff estimate, S.A.20 and the packets P3-P7.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MH.DualityRd

variable {d : ℕ}

lemma sa6_inj_of_occ {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {N : ℕ}
    (hocc : ∀ᵐ ζ ∂(R N).P, volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) S.T ∧
      (R N).X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} = 0) :
    ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal ρ) ζ) := by
  filter_upwards [hocc] with ζ hζ
  have h0 : ∀ᵐ ρ ∂(volume : Measure ℝ), ρ ∉ {s : ℝ | s ∈ Set.Icc (0 : ℝ) S.T ∧
      (R N).X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} := measure_eq_zero_iff_ae_notMem.1 hζ
  filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_Icc] with ρ h1 h2
  intro i j hij
  by_contra hne
  exact h1 ⟨h2, ⟨i, j, hne, hij⟩⟩

/-- A.e. injectivity of the selected flow for a.e. time, in all three branches of A.1 (collision-free, Cepa-Lepingle
occupation, contact-allowing in `d = 1` via the null contact occupation of S.A.26). -/
theorem sa6_inj_N {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 : ℝ} {r mV : ℕ}
    {C₀ : ℝ} {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal ρ) ζ) := by
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  exact HRS.MS.PathFidi.sa26_flow_inj_all S.hT.le (hS.flow N hN) hF

theorem sa6_kernels (S : WholeMainData d) {Γ : ℕ} {Kad : ℝ}
    (hadj : AdjointDerivInput (Γ : ℝ) (mStar d) S.coeff S.T Kad) :
    ∃ KF : ℕ → Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ),
      ∀ N : ℕ, 1 ≤ N → Sa6Kern (S.coeff N) S.T Γ (max Kad 0) (KF N) := by
  classical
  refine ⟨fun N => if h : 1 ≤ N then (sa6_kern_exists (hadj N h)).choose else fun _ _ _ _ => 0,
    fun N hN => ?_⟩
  simp only [dif_pos hN]
  exact (sa6_kern_exists (hadj N hN)).choose_spec

/-- The constant inputs of the field theorems: the commutator input (S.B.5), the coercivity pair and cutoff estimate, and
the kernel family with the `𝒩`-bound of S.A.20. -/
theorem sa6_inputs (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ K' Cp Ck : ℝ, 0 ≤ Ck ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        SelectedCommutatorInput S (fd.Gamma : ℝ) S.T K' C₀ Λ fd.eN ∧
        (∀ Λ' : ℝ, 1 ≤ Λ' → ∀ N' : ℕ, 2 ≤ N' → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ') →
          Integrable (fun x => ‖x‖ ^ 2 * ρ x) → ∀ X : EucConfig d N', Function.Injective X →
          ∀ h : Euc d → ℝ, cNormE χ h < ⊤ → ∀ Rr : ℝ, 1 ≤ Rr →
            |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h| ≤ Cp * (cNormE χ h).toReal *
              (Rr ^ ((d : ℝ) / 2) * (smearScale d N' Λ' + Real.sqrt (rieszModulatedEnergy d S.s X
                (HRS.Whole.withDensityReal ρ) + oNΛ d S.s C₀ Λ' N')) +
                (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / Rr ^ 2)) ∧
        ∃ KF : ℕ → Fin d → ℝ → ℝ → Euc d → HNeg d (fd.Gamma : ℝ),
          (∀ N : ℕ, 1 ≤ N → Sa6Kern (S.coeff N) S.T fd.Gamma (max Kad 0) (KF N)) ∧
          ∀ N : ℕ, 1 ≤ N → ∀ t' ∈ Set.Icc (0 : ℝ) S.T,
            ∀ B : HNeg d (fd.Gamma : ℝ) →L[ℝ] HNeg d (fd.Gamma : ℝ),
            (∀ u v, inner ℝ (B u) v = inner ℝ u (B v)) → ‖B‖ ≤ 1 → ∀ σ ∈ Set.Icc (0 : ℝ) t',
              cNormE χ (fun z => ∑ j, inner ℝ (B (KF N j σ t' z)) (KF N j σ t' z)) ≤
                ENNReal.ofReal Ck := by
  classical
  by_cases hex : ∃ S0 : WholeMainData d, S0.s = s ∧ fd.Holds S0 ν₀
  swap
  · exact ⟨0, fun C₀ _ => ⟨0, 0, 0, le_rfl, fun S hs _ _ hH => absurd ⟨S, hs, hH⟩ hex⟩⟩
  obtain ⟨S0, hS0s, hS0⟩ := hex
  have hd1 : 1 ≤ d := S0.hd
  have hs0 : 0 ≤ s := hS0s ▸ S0.hs0
  have hsd : s < d := hS0s ▸ S0.hsd
  obtain ⟨C₀B, hB⟩ := sa6_B5 s fd ν₀ MB Λ ΛV G₀ νbar T m20 hΛ
  obtain ⟨C₀c, C₁, hC₀c, hpairE⟩ := HRS.MH.CoercTest.p_assembly d hd1 s hs0 hsd
  obtain ⟨Cp, hCp⟩ := test_cutoff_pathwise hd1 s hs0 hsd χ hχ C₁
  obtain ⟨Ck, hCkall⟩ := HRS.MS.SuppU3.adjoint_field_kernel_proof (d := d) fd.Gamma T Kad χ hχ
  refine ⟨max C₀B C₀c, fun C₀ hC₀ => ?_⟩
  obtain ⟨K', hK'⟩ := hB C₀ (le_trans (le_max_left _ _) hC₀) Kad
  have hpair := hpairE C₀ (le_trans (le_max_right _ _) hC₀)
  refine ⟨K', Cp, max Ck 0, le_max_right _ _, ?_⟩
  intro S hs hT hinv hH R 𝔈 hS hFA
  subst hs
  subst hT
  refine ⟨hK' S rfl rfl hinv hH R 𝔈 hS hFA, hCp C₀ hpair, ?_⟩
  obtain ⟨KF, hKF⟩ := sa6_kernels S hFA.deriv
  have hpairKF : ∀ N : ℕ, 1 ≤ N → ∀ (j : Fin d) (r t' : ℝ), 0 ≤ r → r ≤ t' → t' ≤ S.T → ∀ (x : Euc d)
      (φ : Euc d → ℝ), IsSobolevTest (fd.Gamma : ℝ) φ →
      HNeg.pairing φ (KF N j r t' x) = HRS.Whole.partialDeriv (fun _ : Fin 1 => j)
        (propagatorW (S.coeff N) r t' φ) x := by
    intro N hN j r t' hr hrt htT x φ hφ
    rw [(hKF N hN).pair j r t' hr hrt htT x φ hφ, rpk_gradient_partial]
  obtain ⟨-, -, hKern⟩ := hCkall S.coeff hFA.deriv hFA.meas
  refine ⟨KF, hKF, ?_⟩
  intro N hN t' ht'' B hB hn σ hσ
  have := ((hKern (fun N' r t'' x j => KF N' j r t'' x) hpairKF).2 B
    (fun u v => by rw [HRS.MS.SuppU3.u3_innerR_eq, HRS.MS.SuppU3.u3_innerR_eq]; exact hB u v) hn
    N hN σ t' hσ.1 hσ.2 ht''.2)
  simp only [HRS.MS.SuppU3.u3_innerR_eq] at this
  exact this.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

theorem sa6_main_core (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        Filter.Tendsto (fun N : ℕ => S.sigma N * fd.eN N) Filter.atTop (nhds 0) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
          InitialFieldDist S R fd.Gamma εf Iemp I →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ N : ℕ, C ≤ (N : ℝ) →
            ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
              IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
              (∃ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ ∧
                IsFluctFieldRepr S R N fd.Gamma t Ξ) ∧
              ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
                IsFluctFieldRepr S R N fd.Gamma t Ξ →
                smoothDist 2 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                  C * Real.exp (ΛT * t) *
                    fieldRateRd (εf N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) (fd.eN N)) ∧
          ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
            IsFluctFieldRepr S R N fd.Gamma t Ξ → ∫⁻ ζ, ‖Ξ ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal B := by
  classical
  obtain ⟨C₀m, hin⟩ := sa6_inputs s fd ν₀ MB Λ ΛV G₀ νbar T m20 χ hχ Kad hΛ
  refine ⟨C₀m, fun C₀ hC₀ => ?_⟩
  obtain ⟨K', Cp, Ck, hCk0, hall⟩ := hin C₀ hC₀
  set Cp' : ℝ := max Cp 0 with hCp'
  set C1 : ℝ := max K' 0 / 2 * T with hC1
  set C2 : ℝ := T * Cp' * Ck with hC2
  set Cc : ℝ := max 2 (max C1 C2) with hCc
  have hCc2 : 2 ≤ Cc := le_max_left _ _
  refine ⟨Cc, 1, by linarith, one_pos, ?_⟩
  intro S hs hT hinv hH R 𝔈 hS hFA hσe m₂ hm₂ hm2 m₀ ε hinit0 εf Iemp I hinit hdist t ht
  subst hs
  subst hT
  obtain ⟨hsel, hCpf, KF, hKF, hcN⟩ := hall S rfl rfl hinv hH R 𝔈 hS hFA
  have ht' : t ∈ Set.Icc (0 : ℝ) S.T := ht
  have hT0 : 0 ≤ S.T := S.hT.le
  have he : ∀ N, 0 ≤ fd.eN N := mrr_eN_nonneg fd
  have hq0 := fun N => sa6_qN_nonneg S N
  refine ⟨fun N hNC νG hνG => ⟨?_, ?_⟩, ?_⟩
  · have hN2 : 2 ≤ N := by exact_mod_cast (le_trans hCc2 hNC)
    exact sa6_exists_Xi hS (by omega) (hFA.deriv N (by omega)) ht'
  · intro Ξ hΞm hΞ
    have hN2 : 2 ≤ N := by exact_mod_cast (le_trans hCc2 hNC)
    have hN1 : 1 ≤ N := by omega
    have hcore := sa6_core_dC2 (Cp := Cp) (χ := χ) hS hΛ hFA.deriv he hsel hCk0 hCpf hm₂ hm2 hinit hdist
      hN2 ht' (sa6_inj_N hS hN1) (hKF N hN1) (hcN N hN1 t ht') hνG hΞm hΞ
    have hw := sa6_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂
    have hεf := hinit.εf_nonneg N hN1
    have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
    have hσ := mrr_sigma_nonneg S N
    have hX1 : 0 ≤ S.sigma N * (𝔈 N + fd.eN N) := mul_nonneg hσ (add_nonneg h𝔈 (he N))
    have hY : 0 ≤ S.qN N * wN d N (𝔈 N) m₂ := mul_nonneg (hq0 N) hw
    have hC1C : C1 ≤ Cc := le_trans (le_max_left _ _) (le_max_right _ _)
    have hC2C : C2 ≤ Cc := le_trans (le_max_right _ _) (le_max_right _ _)
    have h1 : C1 * (S.sigma N * (𝔈 N + fd.eN N)) ≤ Cc * (S.sigma N * (𝔈 N + fd.eN N)) :=
      mul_le_mul_of_nonneg_right hC1C hX1
    have hCpC : 0 ≤ Cp' * Ck := mul_nonneg (le_max_right _ _) hCk0
    have h2 : t * Cp' * Ck * (S.qN N * wN d N (𝔈 N) m₂) ≤ Cc * (S.qN N * wN d N (𝔈 N) m₂) := by
      calc t * Cp' * Ck * (S.qN N * wN d N (𝔈 N) m₂) = t * (Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) := by ring
        _ ≤ S.T * (Cp' * Ck) * (S.qN N * wN d N (𝔈 N) m₂) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht'.2 hCpC) hY
        _ = C2 * (S.qN N * wN d N (𝔈 N) m₂) := by rw [hC2]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hC2C hY
    have h3 : εf N ≤ Cc * εf N := by nlinarith
    have hexp : 1 ≤ Real.exp (1 * t) := Real.one_le_exp (by have := ht'.1; linarith)
    have hbr : 0 ≤ εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂ := by linarith
    have h4 : Cc * (εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) ≤
        Cc * Real.exp (1 * t) * (εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) := by
      have : Cc * 1 ≤ Cc * Real.exp (1 * t) := mul_le_mul_of_nonneg_left hexp (by linarith)
      nlinarith
    unfold fieldRateRd
    refine hcore.trans ?_
    have e1 : S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + fd.eN N) =
        C1 * (S.sigma N * (𝔈 N + fd.eN N)) := by rw [hC1]; ring
    have e2 : 1 / 2 * (t * (2 * S.qN N * max Cp 0 * Ck * wN d N (𝔈 N) m₂)) =
        t * Cp' * Ck * (S.qN N * wN d N (𝔈 N) m₂) := by rw [hCp']; ring
    rw [e1, e2]
    linarith
  · -- the first-moment bound
    obtain ⟨bσ, hbσ⟩ : ∃ b : ℝ, ∀ N, S.sigma N * (𝔈 N + fd.eN N) ≤ b := by
      have h1 : Filter.Tendsto (fun N : ℕ => S.sigma N * (𝔈 N + fd.eN N)) Filter.atTop (nhds 0) := by
        have := hS.energy.small.add hσe
        simpa [mul_add] using this
      obtain ⟨b, hb⟩ := h1.bddAbove_range
      exact ⟨b, fun N => hb ⟨N, rfl⟩⟩
    set n₀ : ℕ := ⌈Cc⌉₊ with hn₀
    have hsum0 : 0 ≤ ∑ N' ∈ Finset.range n₀, 2 * S.sigma N' * |Kad| :=
      Finset.sum_nonneg fun N' _ => mul_nonneg (mul_nonneg (by norm_num) (mrr_sigma_nonneg S N'))
        (abs_nonneg _)
    set Bbig : ℝ := (1 + Cin ^ 2) + (1 + mrmCb * (2 * d * S.T * (max Kad 0) ^ 2) ^ 2) +
      max K' 0 / 2 * S.T * bσ with hBbig
    have hB0 : 0 ≤ Bbig := by
      have hK0 : 0 ≤ max K' 0 / 2 * S.T * bσ := by
        have : 0 ≤ S.sigma 1 * (𝔈 1 + fd.eN 1) :=
          mul_nonneg (mrr_sigma_nonneg S 1) (add_nonneg (hS.energy.pos 1 le_rfl).le (he 1))
        exact mul_nonneg (by positivity) (this.trans (hbσ 1))
      have hm := mul_nonneg mrmCb_nonneg (sq_nonneg (2 * d * S.T * (max Kad 0) ^ 2))
      rw [hBbig]; linarith [sq_nonneg Cin]
    refine ⟨Bbig + ∑ N' ∈ Finset.range n₀, 2 * S.sigma N' * |Kad|, fun N hN Ξ hΞm hΞ => ?_⟩
    by_cases hlt : N < n₀
    · have hn := sa6_Xi_norm_le hS hN (hFA.deriv N hN) ht' hΞ
      have hbd : 2 * S.sigma N * |Kad| ≤ Bbig + ∑ N' ∈ Finset.range n₀, 2 * S.sigma N' * |Kad| := by
        have h1 := Finset.single_le_sum (f := fun N' => 2 * S.sigma N' * |Kad|)
          (fun N' _ => mul_nonneg (mul_nonneg (by norm_num) (mrr_sigma_nonneg S N')) (abs_nonneg _))
          (Finset.mem_range.2 hlt)
        linarith
      calc ∫⁻ ζ, ‖Ξ ζ‖ₑ ∂(R N).P ≤ ∫⁻ _ζ, ENNReal.ofReal (2 * S.sigma N * |Kad|) ∂(R N).P :=
            lintegral_mono_ae (hn.mono fun ζ h => by
              rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal h)
        _ = ENNReal.ofReal (2 * S.sigma N * |Kad|) := by simp
        _ ≤ _ := ENNReal.ofReal_le_ofReal hbd
    · have hCN : Cc ≤ (N : ℝ) := (Nat.le_ceil Cc).trans (by exact_mod_cast not_lt.1 hlt)
      have hN2 : 2 ≤ N := by exact_mod_cast (le_trans hCc2 hCN)
      have hmom := sa6_core_moment hS hΛ hFA.deriv he hsel hinit hN2 ht'
        (sa6_inj_N hS (by omega)) (hKF N hN) hΞm hΞ
      refine hmom.trans (ENNReal.ofReal_le_ofReal ?_)
      have hσ := mrr_sigma_nonneg S N
      have e1 : S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + fd.eN N) =
          max K' 0 / 2 * S.T * (S.sigma N * (𝔈 N + fd.eN N)) := by ring
      rw [e1]
      have h2 : max K' 0 / 2 * S.T * (S.sigma N * (𝔈 N + fd.eN N)) ≤ max K' 0 / 2 * S.T * bσ :=
        mul_le_mul_of_nonneg_left (hbσ N) (by positivity)
      rw [hBbig]
      linarith

end HRS.MS.MainRdField
