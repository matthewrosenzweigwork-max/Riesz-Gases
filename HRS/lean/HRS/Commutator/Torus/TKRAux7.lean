import HRS.Commutator.Torus.TKRAux6

/-!
# T-KR helpers, part 7: the lattice sum of the differences of the symbol of `∇g_{>}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad HRS.PDE.Kern

variable {d : ℕ} {s η : ℝ}

/-- the coefficient sequence of the symbol `tkrGn` -/
def tkrCG (d : ℕ) (s η : ℝ) (i : Fin d) (k : Lattice d) : ℂ :=
  ((tkrGn d s η i (Lattice.toEuc k) : ℝ) : ℂ)

lemma tkr_coef_eq (hsd : s < d) (hη : 0 < η) (hη1 : η ≤ 1) (i : Fin d) (k : Lattice d) :
    (1 - ((tkrChi η k : ℝ) : ℂ)) * tkrCI d s i k =
      ((2 * Real.pi * HDB.kapC d s : ℝ) : ℂ) * Complex.I * tkrCG d s η i k := by
  unfold tkrCI tkrCG
  rw [tkrGn_eq s η hη hη1, HDB.rieszCoeff_eq hsd k]
  have hin : inner ℝ (EuclideanSpace.single i (1 : ℝ)) (Lattice.toEuc k) = ((k i : ℤ) : ℝ) := by
    rw [EuclideanSpace.inner_single_left]
    simp [Lattice.toEuc]
  rw [hin]
  unfold tkrChi
  push_cast
  ring

lemma tkr_Dls_smul (a : ℂ) (L : List (Fin d)) (c : Lattice d → ℂ) (k : Lattice d) :
    Dls L (fun l => a * c l) k = a * Dls L c k := by
  induction L generalizing c k with
  | nil => rfl
  | cons i L ih =>
    simp only [Dls]
    have : Dl i (fun l => a * c l) = fun l => a * Dl i c l := by
      funext l; simp [Dl]; ring
    rw [this, ih]

lemma tkr_Dls_tkrCG (L : List (Fin d)) (i : Fin d) (k : Lattice d) :
    Dls L (tkrCG d s η i) k =
      ((fdiffs (L.map fun j => EuclideanSpace.single j (1 : ℝ)) (tkrGn d s η i)
        (Lattice.toEuc k) : ℝ) : ℂ) := by
  have h := Dls_comp_toEuc L (fun ξ => ((tkrGn d s η i ξ : ℝ) : ℂ))
  have e : tkrCG d s η i = (fun ξ => ((tkrGn d s η i ξ : ℝ) : ℂ)) ∘ Lattice.toEuc := rfl
  rw [e, h, HDB.fdiffs_ofReal]
  rfl

lemma tkr_exists_box (u : Finset (Lattice d)) : ∃ M : ℕ, u ⊆ boxF d M := by
  classical
  refine ⟨u.sup fun k => Finset.univ.sup fun i => (k i).natAbs, fun k hk => ?_⟩
  rw [LatSum.mem_boxF']
  intro i
  have h1 : (k i).natAbs ≤ Finset.univ.sup fun i => (k i).natAbs := Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)
  have h2 : (Finset.univ.sup fun i => (k i).natAbs) ≤ u.sup fun k => Finset.univ.sup fun i => (k i).natAbs :=
    Finset.le_sup (f := fun k => Finset.univ.sup fun i => (k i).natAbs) hk
  have := h1.trans h2
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this

lemma tkr_dls_sum (hd : 1 ≤ d) (s : ℝ) (N : ℕ) (hp : 1 ≤ (N : ℝ) - (s + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ i j : Fin d,
      Summable (fun k : Lattice d => ‖Dls (List.replicate N j) (tkrCG d s η i) k‖) ∧
      ∑' k : Lattice d, ‖Dls (List.replicate N j) (tkrCG d s η i) k‖ ≤
        K * η ^ ((N : ℝ) - (s + 1)) := by
  obtain ⟨C1, hC1, hC⟩ := tkrGn_fdiffs_bound (d := d) s N
  obtain ⟨At, hAt0, hAt⟩ := LatSum.tail_sum hd hp
  set pp : ℝ := (N : ℝ) - (s + 1) with hpp
  refine ⟨C1 * At * (((N : ℝ) + 1) ^ pp), by positivity, fun η hη hη1 i j => ?_⟩
  set T : ℝ := max (1 / η - N) 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  have hterm : ∀ k : Lattice d, ‖Dls (List.replicate N j) (tkrCG d s η i) k‖ ≤
      C1 * (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - pp) else 0) := by
    intro k
    rw [tkr_Dls_tkrCG, Complex.norm_real, Real.norm_eq_abs, ← Real.norm_eq_abs]
    have hL' : (List.replicate N j).map (fun j => (EuclideanSpace.single j (1 : ℝ) : Euc d)) =
        List.replicate N (EuclideanSpace.single j (1 : ℝ)) := by
      rw [List.map_replicate]
    rw [hL']
    obtain ⟨hb, hz0⟩ := hC η hη hη1 i j (Lattice.toEuc k)
    by_cases hTk : T ≤ Lattice.enorm k
    · rw [if_pos hTk]
      refine hb.trans (le_of_eq ?_)
      have e : s - (d : ℝ) + 1 - N = -(d : ℝ) - pp := by rw [hpp]; ring
      rw [e]
      rfl
    · rw [if_neg hTk, mul_zero]
      have hlt : Lattice.enorm k < T := not_le.mp hTk
      have hTpos : T = 1 / η - N := by
        rcases le_or_gt (1 / η - N) 0 with h | h
        · exfalso
          have : T = 0 := by rw [hT]; exact max_eq_right h
          have : 0 ≤ Lattice.enorm k := norm_nonneg _
          linarith
        · rw [hT]; exact max_eq_left h.le
      have : ‖Lattice.toEuc k‖ < 1 / η - N := by
        have := hlt; unfold Lattice.enorm at this; rwa [hTpos] at this
      rw [hz0 this, norm_zero]
  have hT1 : (1 + T) ^ (-pp) ≤ ((N : ℝ) + 1) ^ pp * η ^ pp := by
    have hlow := HDB.one_add_T_ge hη N
    have hNρ : (0 : ℝ) < ((N : ℝ) + 1) * η := by positivity
    have hpp0 : 0 ≤ pp := by linarith
    calc (1 + T) ^ (-pp) ≤ (1 / (((N : ℝ) + 1) * η)) ^ (-pp) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
      _ = (((N : ℝ) + 1) * η) ^ pp := by
          rw [one_div, Real.inv_rpow hNρ.le, Real.rpow_neg hNρ.le, inv_inv]
      _ = ((N : ℝ) + 1) ^ pp * η ^ pp := Real.mul_rpow (by positivity) hη.le
  have hbox : ∀ u : Finset (Lattice d), ∑ k ∈ u, ‖Dls (List.replicate N j) (tkrCG d s η i) k‖ ≤
      C1 * At * (((N : ℝ) + 1) ^ pp) * η ^ pp := by
    intro u
    obtain ⟨M, hM⟩ := tkr_exists_box u
    have h1 : ∑ k ∈ u, ‖Dls (List.replicate N j) (tkrCG d s η i) k‖ ≤
        ∑ k ∈ boxF d M, ‖Dls (List.replicate N j) (tkrCG d s η i) k‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hM (fun _ _ _ => norm_nonneg _)
    refine h1.trans ?_
    calc ∑ k ∈ boxF d M, ‖Dls (List.replicate N j) (tkrCG d s η i) k‖
        ≤ ∑ k ∈ boxF d M, C1 * (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - pp) else 0) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = C1 * ∑ k ∈ boxF d M, (if T ≤ Lattice.enorm k then (1 + Lattice.enorm k) ^ (-(d : ℝ) - pp) else 0) := by
          rw [Finset.mul_sum]
      _ ≤ C1 * (At * (1 + T) ^ (-pp)) := mul_le_mul_of_nonneg_left (hAt _ T hT0) hC1
      _ ≤ C1 * (At * (((N : ℝ) + 1) ^ pp * η ^ pp)) := by gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : Lattice d => ‖Dls (List.replicate N j) (tkrCG d s η i) k‖) :=
    summable_of_sum_le (fun k => norm_nonneg _) hbox
  exact ⟨hsumm, hsumm.tsum_le_of_sum_le hbox⟩

end HRS.Commutator.TorusNote
