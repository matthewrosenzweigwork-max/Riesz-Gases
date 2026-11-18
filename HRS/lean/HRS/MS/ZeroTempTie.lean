import HRS.MS.ZeroTempAux16

/-!
# SA11 tie: S.A.11 `zero_temp_decaying_field`

`zero_temp_decaying_field_proof : type_of% @HRS.Whole.AppendixA.zero_temp_decaying_field`.

Route (zero temperature, `invβ = 0`: `σ_N = κ_N`, `A_N = 1`, no Gaussian block, no martingale term):
the transported field is `Z = η ∘ T` with `T : W^{m,p} → W^{m,p}` the bounded linear transpose of the propagator `U^{0,t}` on jets
(boundedness: `AdjointInputRd`; linearity: uniqueness of classical solutions, `HRS/MS/ZeroTempAux5.lean`; uniqueness of weak jets,
`ZeroTempAux2.lean`); the particle field is the continuous image `σ(μ_N^t - ρ_N^t)` of the configuration
(Sobolev embedding `W^{m,p} ↪ C_b^{m_*}` in the jet norm, `ZeroTempAux3.lean`); the difference is `Ξ_t - Ψ_0 ∘ T` (pathwise Duhamel
identity and S.B.5, `ZeroTempAux9/12/13`) plus `(Ψ_0 - η) ∘ T` (the coupling).  The constant is
`C = 2 + K_T + K_c T (1 + c₂)`, `Λ_T = 1`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

theorem sa11_gamma_pos {s : ℝ} (fd : FieldDensityRd d s) : 1 ≤ fd.Gamma := by
  cases fd with
  | nd Rg => simp only [FieldDensityRd.Gamma, gammaNd]; omega
  | decSub c => simp only [FieldDensityRd.Gamma, DecayingDensity.gammaIndex]; omega
  | decSuperIso m' p' => simp only [FieldDensityRd.Gamma]; omega
  | decSuperHilb m' => simp only [FieldDensityRd.Gamma]; omega

theorem sa11_hm_of_holds {s : ℝ} (fd : FieldDensityRd d s) {m : ℕ} {p : ℝ} (hfd : fd.wParams = some (m, p))
    {s' : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {invβ ν₀ : ℝ} (h : fd.HoldsAt s' M invβ ν₀) :
    mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m := by
  cases fd with
  | nd Rg => simp [FieldDensityRd.wParams] at hfd
  | decSub c =>
    simp only [FieldDensityRd.wParams, Option.some.injEq, Prod.mk.injEq] at hfd
    obtain ⟨rfl, rfl⟩ := hfd
    exact le_rfl
  | decSuperIso m' p' =>
    simp only [FieldDensityRd.wParams, Option.some.injEq, Prod.mk.injEq] at hfd
    obtain ⟨rfl, rfl⟩ := hfd
    obtain ⟨-, hp2, hlt, -⟩ := h
    have h1 : (⌊(d : ℝ) / p'⌋₊ : ℝ) ≤ (d : ℝ) / p' := Nat.floor_le (by
      have : (0 : ℝ) < p' := by linarith
      positivity)
    have h2 : ((mStar d + ⌊(d : ℝ) / p'⌋₊ : ℕ) : ℝ) < m' := by push_cast; linarith
    have := (Nat.cast_lt (α := ℝ)).1 h2
    omega
  | decSuperHilb m' =>
    simp only [FieldDensityRd.wParams, Option.some.injEq, Prod.mk.injEq] at hfd
    obtain ⟨rfl, rfl⟩ := hfd
    obtain ⟨-, hlt, -⟩ := h
    have h1 : (⌊(d : ℝ) / 2⌋₊ : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
    have h2 : ((mStar d + ⌊(d : ℝ) / 2⌋₊ : ℕ) : ℝ) < m' := by push_cast; linarith
    have := (Nat.cast_lt (α := ℝ)).1 h2
    omega

theorem zero_temp_decaying_field_proof : type_of% @HRS.Whole.AppendixA.zero_temp_decaying_field := by
  intro d s fd m p _inst hfd ν₀ MB Λ ΛV G₀ νbar T Cin m20 χ hχ Kad
  obtain ⟨C₀min, Kc, c₂, hKc, hc₂, H⟩ := sa11_comm_exists s fd hfd ν₀ MB Λ Kad
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  have hKT0 : 0 ≤ max Kad 0 * sa11_cJ d m := mul_nonneg (le_max_right _ _) (sa11_cJ_nonneg d m)
  have hCpos : 0 < 2 + max Kad 0 * sa11_cJ d m + Kc * max T 0 * (1 + c₂) := by
    have : 0 ≤ Kc * max T 0 * (1 + c₂) := mul_nonneg (mul_nonneg hKc (le_max_right _ _)) (by linarith)
    linarith
  refine ⟨2 + max Kad 0 * sa11_cJ d m + Kc * max T 0 * (1 + c₂), 1, hCpos, one_pos, ?_⟩
  intro S hs hT hinvbar hH hinv0 R 𝔈 hS hA m₂ hm₂ hmom m₀ ε hinit εfX Ξ0 ηW hcoup t ht N hN
  set C : ℝ := 2 + max Kad 0 * sa11_cJ d m + Kc * max T 0 * (1 + c₂) with hCdef
  have hN2' : (2 : ℝ) ≤ N := by
    have : (2 : ℝ) ≤ C := by
      have : 0 ≤ Kc * max T 0 * (1 + c₂) := mul_nonneg (mul_nonneg hKc (le_max_right _ _)) (by linarith)
      linarith
    exact this.trans hN
  have hN2 : 2 ≤ N := by exact_mod_cast hN2'
  have hN1 : 1 ≤ N := by omega
  have hd1 : 1 ≤ d := S.hd
  have hHN := hH N hN1
  have hm := sa11_hm_of_holds fd hfd hHN
  have hΓ := sa11_gamma_pos fd
  have hRg := sa11_regime fd hfd hHN
  have hν := hinvbar N
  have htS : t ∈ Set.Icc (0 : ℝ) S.T := by rw [hT]; exact ht
  have hcomm := H C₀ hC₀ S R ΛV G₀ m20 𝔈 hs hH hS N hN2 (hA N hN1)
  have hη := (hcoup.meas N hN1).2
  obtain ⟨hΞ, hZ, hW⟩ := sa11_main_N hd1 hm hΓ hS hN2 (hinv0 N) hν hRg (hA N hN1) htS hKc hc₂
    (fun N => HRS.MP.RdRem.mrr_eN_nonneg fd N) hcomm (ηW N) (Ξ0 N) hη (hcoup.repr_emp N hN1)
    (hcoup.nonneg N hN1) (hcoup.bound N hN1)
  refine ⟨hΞ, hZ, fun Ξ Z hΞm hZm hΞr hZr => (hW Ξ Z hΞm hZm hΞr hZr).trans ?_⟩
  -- the numerical comparison
  have hσ0 : 0 ≤ S.sigma N := HRS.MP.RdRem.mrr_sigma_nonneg S N
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have he : 0 ≤ fd.eN N := HRS.MP.RdRem.mrr_eN_nonneg fd N
  have hεf : 0 ≤ εfX N := hcoup.nonneg N hN1
  have hTpos : 0 < T := by rw [← hT]; exact S.hT
  have hTm : max T 0 = T := max_eq_left hTpos.le
  have hexp : (1 : ℝ) ≤ Real.exp (1 * t) := by
    rw [one_mul]; exact Real.one_le_exp ht.1
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hT]
  set A : ℝ := εfX N + S.sigma N * (𝔈 N + fd.eN N) with hA
  have hA0 : 0 ≤ A := add_nonneg hεf (mul_nonneg hσ0 (add_nonneg h𝔈 he))
  have hCA : C * A ≤ C * Real.exp (1 * t) * A := by
    have : 0 ≤ C * A := mul_nonneg hCpos.le hA0
    nlinarith
  refine le_trans ?_ hCA
  rw [hCdef, hTm]
  have h1 : max Kad 0 * sa11_cJ d m * εfX N ≤ (2 + max Kad 0 * sa11_cJ d m + Kc * T * (1 + c₂)) * εfX N := by
    have : 0 ≤ Kc * T * (1 + c₂) := mul_nonneg (mul_nonneg hKc hTpos.le) (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith) hεf
  have h2 : S.sigma N / 2 * Kc * T * (𝔈 N + c₂ * fd.eN N) ≤
      (2 + max Kad 0 * sa11_cJ d m + Kc * T * (1 + c₂)) * (S.sigma N * (𝔈 N + fd.eN N)) := by
    have hK : 0 ≤ Kc * T := mul_nonneg hKc hTpos.le
    have hb : 𝔈 N + c₂ * fd.eN N ≤ (1 + c₂) * (𝔈 N + fd.eN N) := by nlinarith
    have hS' : 0 ≤ S.sigma N * (𝔈 N + fd.eN N) := mul_nonneg hσ0 (add_nonneg h𝔈 he)
    calc S.sigma N / 2 * Kc * T * (𝔈 N + c₂ * fd.eN N)
        ≤ S.sigma N * Kc * T * (1 + c₂) * (𝔈 N + fd.eN N) := by
          have : S.sigma N / 2 * Kc * T * (𝔈 N + c₂ * fd.eN N) =
              (S.sigma N / 2) * (Kc * T) * (𝔈 N + c₂ * fd.eN N) := by ring
          rw [this]
          have h3 : (S.sigma N / 2) * (Kc * T) * (𝔈 N + c₂ * fd.eN N) ≤
              (S.sigma N / 2) * (Kc * T) * ((1 + c₂) * (𝔈 N + fd.eN N)) :=
            mul_le_mul_of_nonneg_left hb (mul_nonneg (by positivity) hK)
          have h4 : (S.sigma N / 2) * (Kc * T) * ((1 + c₂) * (𝔈 N + fd.eN N)) ≤
              S.sigma N * Kc * T * (1 + c₂) * (𝔈 N + fd.eN N) := by
            have : 0 ≤ S.sigma N * Kc * T * (1 + c₂) * (𝔈 N + fd.eN N) := by
              have := mul_nonneg (mul_nonneg hσ0 hK) (by linarith : (0 : ℝ) ≤ 1 + c₂)
              have h6 : S.sigma N * Kc * T * (1 + c₂) = S.sigma N * (Kc * T) * (1 + c₂) := by ring
              rw [h6]
              exact mul_nonneg this (add_nonneg h𝔈 he)
            nlinarith
          exact h3.trans h4
      _ ≤ (2 + max Kad 0 * sa11_cJ d m + Kc * T * (1 + c₂)) * (S.sigma N * (𝔈 N + fd.eN N)) := by
          have h5 : S.sigma N * Kc * T * (1 + c₂) * (𝔈 N + fd.eN N) =
              (Kc * T * (1 + c₂)) * (S.sigma N * (𝔈 N + fd.eN N)) := by ring
          rw [h5]
          have : 0 ≤ (2 + max Kad 0 * sa11_cJ d m) * (S.sigma N * (𝔈 N + fd.eN N)) :=
            mul_nonneg (by linarith) hS'
          nlinarith
  rw [hA]
  nlinarith

end HRS.MS.ZeroTemp

example := (@HRS.MS.ZeroTemp.zero_temp_decaying_field_proof : type_of% @HRS.Whole.AppendixA.zero_temp_decaying_field)
