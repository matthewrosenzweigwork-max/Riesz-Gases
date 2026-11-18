import HRS.MC.CepN6Aux4

/-!
# Packet CEPN6 (aux 5): the deterministic bootstrap

If a continuous path stays in the closed good set `Kc` on `[t₁, u]`, starts well inside, and the noise increments
are small, then at time `u` it is in the open good set `Uo` (with room to spare).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

variable {N : ℕ}

theorem n6_boot {D : DynData 1} {p0 p1 : Fin N} (hp : p0 ≠ p1)
    {y : ℝ → Fin N → Euc 1} {w : ℝ → Fin N → ℝ} {t₁ u : ℝ} (hu : t₁ ≤ u)
    {Bd ν η r r2 gcap L K Nz : ℝ} (hν : 0 ≤ ν) (hη : 0 ≤ η) (hBd0 : 0 ≤ Bd)
    (hBd1 : ∀ z ∈ liftedFree 1 N, ∀ k : Fin N, (∀ j, j ≠ k → r2 ≤ n6_dc (z k 0 - z j 0)) →
      |(liftedDrift D z k) 0| ≤ Bd)
    (hBd2 : ∀ z ∈ liftedFree 1 N,
      (∀ j, j ≠ p0 → j ≠ p1 → r2 ≤ n6_dc (z p0 0 - z j 0) ∧ r2 ≤ n6_dc (z p1 0 - z j 0)) →
      |(liftedDrift D z p0) 0 + (liftedDrift D z p1) 0| ≤ Bd)
    (hfree : ∀ v ∈ Set.Icc t₁ u, y v ∈ liftedFree 1 N)
    (hK : ∀ v ∈ Set.Icc t₁ u, y v ∈ n6_Kc p0 p1 r2 gcap)
    (hint : ∀ k, IntervalIntegrable (fun s => (liftedDrift D (y s) k) 0) volume t₁ u)
    (heq : ∀ k, ∀ v ∈ Set.Icc t₁ u, y v k 0 - y t₁ k 0 =
      (∫ s in t₁..v, (liftedDrift D (y s) k) 0) + ν * (w v k - w t₁ k))
    (hw : ∀ k, ∀ v ∈ Set.Icc t₁ u, |w v k - w t₁ k| ≤ η)
    (hcont : ContinuousOn y (Set.Icc t₁ u))
    (hinit : ∀ k l, n6_rel p0 p1 k l → r ≤ n6_dc (y t₁ k 0 - y t₁ l 0))
    (hG0 : y t₁ p1 0 - y t₁ p0 0 ≤ L)
    (hGpos : ∀ v ∈ Set.Icc t₁ u, 0 < y v p1 0 - y v p0 0)
    (hK0 : 0 ≤ K)
    (hrise : ∀ s t, t₁ ≤ s → s ≤ t → t ≤ u → (∀ v ∈ Set.Ioc s t, L ≤ y v p1 0 - y v p0 0) →
      (y t p1 0 - y t p0 0) - (y s p1 0 - y s p0 0) ≤ K * (t - s) + Nz)
    (hcond : K * (u - t₁) + Nz < L)
    (hM : r2 + 2 * (Bd * (u - t₁) + 2 * ν * η + L) < r) (h2L : 2 * L ≤ gcap) :
    y u ∈ n6_Uo p0 p1 r2 gcap := by
  have huI : u ∈ Set.Icc t₁ u := ⟨hu, le_rfl⟩
  have htI : t₁ ∈ Set.Icc t₁ u := ⟨le_rfl, hu⟩
  have hdu : 0 ≤ u - t₁ := sub_nonneg.2 hu
  -- gap bound
  have hGc : ContinuousOn (fun v => y v p1 0 - y v p0 0) (Set.Icc t₁ u) :=
    ((n6_coord_cont p1).comp_continuousOn hcont).sub ((n6_coord_cont p0).comp_continuousOn hcont)
  have hGb := n6_gap_bound (G := fun v => y v p1 0 - y v p0 0) hGc hK0 hG0 hu hrise hcond
  have hGu : y u p1 0 - y u p0 0 < 2 * L := hGb u huI
  have hGt : 0 < y t₁ p1 0 - y t₁ p0 0 := hGpos t₁ htI
  have hGu0 : 0 < y u p1 0 - y u p0 0 := hGpos u huI
  have hL0 : 0 < L := lt_of_lt_of_le hGt hG0
  set M : ℝ := Bd * (u - t₁) + 2 * ν * η + L with hMdef
  have hB'0 : 0 ≤ Bd * (u - t₁) + 2 * ν * η := by positivity
  -- displacement of non-pair particles
  have hnp : ∀ k : Fin N, k ≠ p0 → k ≠ p1 → |y u k 0 - y t₁ k 0| ≤ M := by
    intro k hk0 hk1
    have h := n6_disp (f := fun s => (liftedDrift D (y s) k) 0) (yk := fun v => y v k 0)
      (t₁ := t₁) (u := u) (B := Bd) (ν := ν) (η := η) (n := w u k - w t₁ k) hu hν
      (heq k u huI) (fun s hs => by
        refine hBd1 (y s) (hfree s hs) k (fun j hj => ?_)
        refine (hK s hs).2 k j ⟨hj.symm, ?_⟩
        rintro ⟨h | h, _⟩
        · exact hk0 h
        · exact hk1 h) (hw k u huI)
    have : ν * η ≤ 2 * ν * η := by nlinarith [mul_nonneg hν hη]
    rw [hMdef]
    linarith
  -- displacement of the pair centre
  have hS := n6_disp2 (f := fun s => (liftedDrift D (y s) p0) 0)
    (g := fun s => (liftedDrift D (y s) p1) 0) (yp := fun v => y v p0 0) (yq := fun v => y v p1 0)
    (t₁ := t₁) (u := u) (B := Bd) (ν := ν) (η := η) (n := w u p0 - w t₁ p0) (m := w u p1 - w t₁ p1)
    hu hν (hint p0) (hint p1) (heq p0 u huI) (heq p1 u huI)
    (fun s hs => by
      refine hBd2 (y s) (hfree s hs) (fun j hj0 hj1 => ⟨?_, ?_⟩)
      · refine (hK s hs).2 p0 j ⟨hj0.symm, ?_⟩
        rintro ⟨_, h | h⟩
        · exact hj0 h
        · exact hj1 h
      · refine (hK s hs).2 p1 j ⟨hj1.symm, ?_⟩
        rintro ⟨_, h | h⟩
        · exact hj0 h
        · exact hj1 h)
    (hw p0 u huI) (hw p1 u huI)
  simp only at hS
  obtain ⟨hS1, hS2⟩ := abs_le.1 hS
  have hp0 : |y u p0 0 - y t₁ p0 0| ≤ M := by
    rw [abs_le, hMdef]
    constructor <;> nlinarith
  have hp1 : |y u p1 0 - y t₁ p1 0| ≤ M := by
    rw [abs_le, hMdef]
    constructor <;> nlinarith
  have hdisp : ∀ i : Fin N, |y u i 0 - y t₁ i 0| ≤ M := by
    intro i
    by_cases h0 : i = p0
    · subst h0; exact hp0
    · by_cases h1 : i = p1
      · subst h1; exact hp1
      · exact hnp i h0 h1
  refine ⟨by linarith, fun k l hkl => ?_⟩
  have h1 := hinit k l hkl
  have h2 := n6_dc_lip (y t₁ k 0 - y t₁ l 0) (y u k 0 - y u l 0)
  have h3 : |(y t₁ k 0 - y t₁ l 0) - (y u k 0 - y u l 0)| ≤ 2 * M := by
    obtain ⟨a1, a2⟩ := abs_le.1 (hdisp k)
    obtain ⟨b1, b2⟩ := abs_le.1 (hdisp l)
    rw [abs_le]
    constructor <;> linarith
  rw [hMdef] at h3
  linarith

end HRS.MC.CepN6
