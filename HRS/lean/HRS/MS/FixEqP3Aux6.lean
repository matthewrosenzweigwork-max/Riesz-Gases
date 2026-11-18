import HRS.MS.FixEqP3Aux5

/-!
# S5.7 `fixed_equation` (worker S57P), part 18: the terminal-time derivative of the orbits

Restriction lemmas for the families on `[0,T]`; the jets of `𝓛_τ φ_α` (`s57p_gen_jets`); and the terminal-time formula
`s57p_td_int`: for `r ≤ s ≤ t ≤ T`, `D^i (U^{r,t} φ - U^{r,s} φ) = ∫_s^t D^i U^{r,u} (𝓛_u φ) du` (Duhamel, `s57p_duhamel` with the source
`g(u) = 𝓛_u φ`), and its bound `≤ |K| C_u B_g (t-s)`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem S57pGen.mono {C : WholeCoeff d} {T T' : ℝ} (G : S57pGen C T) (h : T' ≤ T) : S57pGen C T' := by
  refine ⟨?_, fun {B} hB {τ} {τ₀} hτ hτ₀ ht {u} {u₀} hu hu₀ h1 x h2 =>
    G.tendsto hB (fun m => ⟨(hτ m).1, (hτ m).2.trans h⟩) ⟨hτ₀.1, hτ₀.2.trans h⟩ ht hu hu₀ h1 x h2⟩
  obtain ⟨K, hK, hb⟩ := G.bound
  exact ⟨K, hK, fun τ hτ => hb τ ⟨hτ.1, hτ.2.trans h⟩⟩

theorem S57pLin.mono {C : WholeCoeff d} {T T' : ℝ} (L : S57pLin C T) (h : T' ≤ T) : S57pLin C T' :=
  ⟨fun τ hτ => L.sub τ ⟨hτ.1, hτ.2.trans h⟩, fun τ hτ => L.comm τ ⟨hτ.1, hτ.2.trans h⟩⟩

theorem S57pFam.mono {C : WholeCoeff d} {θ : Euc d → ℝ} {T T' : ℝ} {j : ℕ} {K : ℝ} (F : S57pFam C θ T j K)
    (h : T' ≤ T) : S57pFam C θ T' j K :=
  ⟨F.hj, fun t ht => F.uniq t ⟨ht.1, ht.2.trans h⟩, F.lin.mono h, F.gen.mono h,
    fun r t hr hrt htT => F.adj r t hr hrt (htT.trans h)⟩

/-- the jets of `𝓛_τ φ_α` -/
theorem s57p_gen_jets {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M Q : Matrix (Fin d) (Fin d) ℝ) (m : ℝ) (J R : ℕ) (hJ : 3 * R + 9 ≤ J) {A Λc νbar : ℝ} (hA : 0 ≤ A)
    (hΛc : 0 ≤ Λc) (hνbar : 0 ≤ νbar) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {ν : ℝ}, |ν| ≤ νbar → ∀ {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {τ : ℝ},
      RgDecay (R + 2) (fun _ => A) (ρ τ) → ContDiff ℝ R (c τ) → (∀ i ≤ R, ∀ x, ‖iteratedFDeriv ℝ i (c τ) x‖ ≤ Λc) →
      ∀ α : MultiIndex d, ContDiff ℝ (R : WithTop ℕ∞) (generatorW (fixedEqCoeff s M Q ν c ρ) τ (oscTestFun m α)) ∧
        ∀ n ≤ R, ∀ x, ‖iteratedFDeriv ℝ n (generatorW (fixedEqCoeff s M Q ν c ρ) τ (oscTestFun m α)) x‖ ≤
          Cg * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
  obtain ⟨KB, K1, hKB0, hK10, hK⟩ := s57p_gen_hi hd hs0 hsd M Q R hA hΛc hνbar
  have hceil2 : ⌈(1 + (((R + 3 : ℕ) : ℝ))) / 2⌉₊ ≤ R + 3 := by
    rw [Nat.ceil_le]; push_cast
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  obtain ⟨C0, hC0, hosc⟩ := s55_osc_bounds hθ m R (R + 3) 1 (by norm_num) J (by omega) (by omega)
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨(KB * (d : ℝ) ^ (R + 3) + K1 * (2 * (d : ℝ) ^ (R + 3))) * C0, by positivity, ?_⟩
  intro ν hν c ρ τ hρ hc hcb α
  obtain ⟨hsm, -, hdec⟩ := hosc α
  set e : ℝ := (((J : ℝ) - m) / 2) with he
  set Λφ : ℝ := C0 * oscEigenvalue d α ^ e with hΛφ
  have hΛφ0 : 0 ≤ Λφ := mul_nonneg hC0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hφR : ContDiff ℝ ((R + 3 : ℕ) : WithTop ℕ∞) (oscTestFun m α) := s55_cd_of_inf (R + 3) hsm
  have hnorm := s55f_decay_to_norm hφR hdec
  rw [max_eq_left hΛφ0] at hnorm
  set B : ℝ := (d : ℝ) ^ (R + 3) * Λφ with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hpow : ∀ n ≤ R + 3, (d : ℝ) ^ n ≤ (d : ℝ) ^ (R + 3) := fun n hn => pow_le_pow_right₀ hd1' hn
  have hBφ : ∀ n, n ≤ R + 2 + 1 → ∀ x, ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ ≤ B := by
    intro n hn x
    exact ((hnorm n (by omega) x).1).trans (mul_le_mul_of_nonneg_right (hpow n (by omega)) hΛφ0)
  have hB1φ : ∀ n, n ≤ R + 1 → ∀ x, ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ * (1 + ‖x‖) ≤ 2 * B := by
    intro n hn x
    exact ((hnorm n (by omega) x).2).trans (by
      have := mul_le_mul_of_nonneg_right (hpow n (by omega)) hΛφ0
      linarith)
  have hcore := hK hν hρ hc hcb hB0 (by positivity : (0 : ℝ) ≤ 2 * B)
    (s55_cd_of_inf (R + 2 + 1) hsm) hBφ hB1φ
  refine ⟨hcore.1, fun n hn x => ?_⟩
  have h2 := hcore.2 n hn x
  simp only [mul_one] at h2
  refine h2.trans (le_of_eq ?_)
  rw [hBdef, hΛφ]
  ring

theorem s57p_ii_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {a b B : ℝ} (hab : a ≤ b) (hc : ContinuousOn F (Set.Ioc a b)) (hb : ∀ u ∈ Set.Ioc a b, ‖F u‖ ≤ B) :
    IntervalIntegrable F volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := ⟨by simp⟩
  refine (integrable_const B).mono' (hc.aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact hb u hu

end HRS.MS.FixEq
