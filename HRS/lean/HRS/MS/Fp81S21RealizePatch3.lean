import HRS.MS.Fp81S21GaussModification

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS.Whole

private def fp81s21_patchIndex (t : ℝ) : ℕ := Nat.ceil (max t 0) + 1

private theorem fp81s21_patchIndex_mem {t : ℝ} :
    max t 0 ∈ Set.Icc (0 : ℝ) ((fp81s21_patchIndex t : ℝ) + 1) := by
  constructor
  · exact le_max_right _ _
  · have hc := Nat.le_ceil (max t 0)
    dsimp [fp81s21_patchIndex]
    push_cast
    linarith

private theorem fp81s21_patchIndex_mem_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    t ∈ Set.Icc (0 : ℝ) ((fp81s21_patchIndex t : ℝ) + 1) := by
  simpa [max_eq_left ht] using (fp81s21_patchIndex_mem (t := t))

private def fp81s21_patchOverlapPoint (n k : ℕ) (q : ℚ) : ℝ :=
  max 0 (min (q : ℝ) (((min n k : ℕ) : ℝ) + 1))

private theorem fp81s21_patchOverlapPoint_mem_left (n k : ℕ) (q : ℚ) :
    fp81s21_patchOverlapPoint n k q ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1) := by
  constructor
  · exact le_max_left _ _
  · apply max_le
    · positivity
    · have hmn : ((min n k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.min_le_left n k
      exact le_trans (min_le_right _ _) (by linarith)

private theorem fp81s21_patchOverlapPoint_mem_right (n k : ℕ) (q : ℚ) :
    fp81s21_patchOverlapPoint n k q ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1) := by
  constructor
  · exact le_max_left _ _
  · apply max_le
    · positivity
    · have hmk : ((min n k : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.min_le_right n k
      exact le_trans (min_le_right _ _) (by linarith)

private theorem fp81s21_patch_overlap_eq
    {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (Y : ∀ n : ℕ, Ω → OscPath d m ((n : ℝ) + 1))
    (ω : Ω)
    (hcompat : ∀ (n k : ℕ) (q : ℚ),
      OscPath.at' (Y n ω)
          ⟨fp81s21_patchOverlapPoint n k q,
            fp81s21_patchOverlapPoint_mem_left n k q⟩ =
        OscPath.at' (Y k ω)
          ⟨fp81s21_patchOverlapPoint n k q,
            fp81s21_patchOverlapPoint_mem_right n k q⟩)
    (n k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (((min n k : ℕ) : ℝ) + 1)) :
    OscPath.at' (Y n ω) ⟨t, ⟨ht.1, ht.2.trans (by
      have hmn : ((min n k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.min_le_left n k
      linarith)⟩⟩ =
      OscPath.at' (Y k ω) ⟨t, ⟨ht.1, ht.2.trans (by
        have hmk : ((min n k : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.min_le_right n k
        linarith)⟩⟩ := by
  let L : ℝ := ((min n k : ℕ) : ℝ) + 1
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hLn : L ≤ (n : ℝ) + 1 := by
    dsimp [L]
    have hmn : ((min n k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.min_le_left n k
    linarith
  have hLk : L ≤ (k : ℝ) + 1 := by
    dsimp [L]
    have hmk : ((min n k : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.min_le_right n k
    linarith
  let cl : ℝ → ℝ := fun x => max 0 (min x L)
  have hclCont : Continuous cl := by
    dsimp [cl]
    exact continuous_const.max (continuous_id.min continuous_const)
  let hmapN : ℝ → Set.Icc (0 : ℝ) ((n : ℝ) + 1) := fun x =>
    ⟨cl x, ⟨le_max_left _ _, max_le (by positivity)
      (le_trans (min_le_right _ _) hLn)⟩⟩
  have hmapN_cont : Continuous hmapN :=
    Continuous.subtype_mk hclCont fun _ => ⟨le_max_left _ _,
      max_le (by positivity) (le_trans (min_le_right _ _) hLn)⟩
  let hmapK : ℝ → Set.Icc (0 : ℝ) ((k : ℝ) + 1) := fun x =>
    ⟨cl x, ⟨le_max_left _ _, max_le (by positivity)
      (le_trans (min_le_right _ _) hLk)⟩⟩
  have hmapK_cont : Continuous hmapK :=
    Continuous.subtype_mk hclCont fun _ => ⟨le_max_left _ _,
      max_le (by positivity) (le_trans (min_le_right _ _) hLk)⟩
  have hfn : Continuous (fun x : ℝ => OscPath.at' (Y n ω) (hmapN x)) := by
    change Continuous (fun x =>
      (show C(Set.Icc (0 : ℝ) ((n : ℝ) + 1), OscDual d m) from Y n ω) (hmapN x))
    exact (show C(Set.Icc (0 : ℝ) ((n : ℝ) + 1), OscDual d m) from Y n ω).continuous.comp
      hmapN_cont
  have hfk : Continuous (fun x : ℝ => OscPath.at' (Y k ω) (hmapK x)) := by
    change Continuous (fun x =>
      (show C(Set.Icc (0 : ℝ) ((k : ℝ) + 1), OscDual d m) from Y k ω) (hmapK x))
    exact (show C(Set.Icc (0 : ℝ) ((k : ℝ) + 1), OscDual d m) from Y k ω).continuous.comp
      hmapK_cont
  have hrat : ∀ q : ℚ,
      OscPath.at' (Y n ω) (hmapN (q : ℝ)) =
        OscPath.at' (Y k ω) (hmapK (q : ℝ)) := by
    intro q
    have h := hcompat n k q
    simpa [hmapN, hmapK, cl, fp81s21_patchOverlapPoint, L] using h
  have heq : (fun x : ℝ => OscPath.at' (Y n ω) (hmapN x)) =
      fun x : ℝ => OscPath.at' (Y k ω) (hmapK x) :=
    Rat.denseRange_cast.equalizer hfn hfk (funext hrat)
  have htclip : cl t = t := by
    dsimp [cl]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have h := congrFun heq t
  simpa [htclip, hmapN, hmapK, cl] using h

/-- Countably many measurable-horizon modifications glue to a jointly measurable continuous
modification on the nonnegative half-line, extended constantly to negative times. -/
theorem fp81s21_patch_nat_modifications
    {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → OscDual d m)
    (Y : ∀ n : ℕ, Ω → OscPath d m ((n : ℝ) + 1))
    (hYmeas : ∀ n, Measurable (Y n))
    (hmod : ∀ (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1)),
      (fun ω => OscPath.at' (Y n ω) ⟨t, ht⟩) =ᵐ[P] X t) :
    ∃ Z : ℝ → Ω → OscDual d m,
      Measurable (Function.uncurry Z) ∧
      (∀ ω, Continuous (fun t => Z t ω)) ∧
      ∀ t, 0 ≤ t → Z t =ᵐ[P] X t := by
  classical
  let Compatible (ω : Ω) : Prop :=
    ∀ (n k : ℕ) (q : ℚ),
      OscPath.at' (Y n ω)
          ⟨fp81s21_patchOverlapPoint n k q,
            fp81s21_patchOverlapPoint_mem_left n k q⟩ =
        OscPath.at' (Y k ω)
          ⟨fp81s21_patchOverlapPoint n k q,
            fp81s21_patchOverlapPoint_mem_right n k q⟩
  have hcompatAE' : ∀ᵐ ω ∂P,
      ∀ (n k : ℕ) (q : ℚ),
        OscPath.at' (Y n ω)
            ⟨fp81s21_patchOverlapPoint n k q,
              fp81s21_patchOverlapPoint_mem_left n k q⟩ =
          OscPath.at' (Y k ω)
            ⟨fp81s21_patchOverlapPoint n k q,
              fp81s21_patchOverlapPoint_mem_right n k q⟩ := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun k => ae_all_iff.2 fun q => ?_
    let t := fp81s21_patchOverlapPoint n k q
    filter_upwards [hmod n t (fp81s21_patchOverlapPoint_mem_left n k q),
      hmod k t (fp81s21_patchOverlapPoint_mem_right n k q)] with ω hn hk
    exact hn.trans hk.symm
  have hcompatAE : ∀ᵐ ω ∂P, Compatible ω := by
    simpa only [Compatible] using hcompatAE'
  obtain ⟨Bad, hBad, hBadm, hBad0⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hcompatAE)
  have hcompatGood : ∀ ω, ω ∉ Bad → Compatible ω := by
    intro ω hω n k q
    by_contra hneq
    exact hω (hBad (by
      intro h
      exact hneq (h n k q)))
  have hgoodAE : ∀ᵐ ω ∂P, ω ∉ Bad := by
    rw [ae_iff]
    simpa using hBad0
  let Zraw : ℝ → Ω → OscDual d m := fun t ω =>
    if ω ∈ Bad then 0 else
      if ht : 0 ≤ t then
        OscPath.at' (Y (fp81s21_patchIndex t) ω)
          ⟨t, fp81s21_patchIndex_mem_of_nonneg ht⟩
      else 0
  let Z : ℝ → Ω → OscDual d m := fun t ω => Zraw (max t 0) ω
  have hcontN : ∀ (ω : Ω), ω ∉ Bad → ∀ n : ℕ,
      ContinuousOn (fun t => Zraw t ω) (Set.Icc (0 : ℝ) (n : ℝ)) := by
    intro ω hω n
    let M : ℕ := n + 1
    have hfixed : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) (n : ℝ)),
        Zraw t ω = OscPath.at' (Y M ω)
          ⟨t, ⟨ht.1, by dsimp [M]; push_cast; linarith [ht.2]⟩⟩ := by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      have hceil : Nat.ceil t ≤ n := Nat.ceil_le.2 (by exact_mod_cast ht.2)
      have hjle : fp81s21_patchIndex t ≤ M := by
        dsimp [fp81s21_patchIndex, M]
        rw [max_eq_left ht0]
        omega
      have hmin : min (fp81s21_patchIndex t) M = fp81s21_patchIndex t := Nat.min_eq_left hjle
      have htL : t ∈ Set.Icc (0 : ℝ)
          (((min (fp81s21_patchIndex t) M : ℕ) : ℝ) + 1) := by
        rw [hmin]
        have htj : t ≤ (fp81s21_patchIndex t : ℝ) := by
          dsimp [fp81s21_patchIndex]
          rw [max_eq_left ht0]
          have hc := Nat.le_ceil t
          push_cast
          linarith
        exact ⟨ht.1, by linarith⟩
      have hagree := fp81s21_patch_overlap_eq Y ω (hcompatGood ω hω)
        (fp81s21_patchIndex t) M htL
      simpa [Zraw, hω, ht0, M, hmin, fp81s21_patchIndex] using hagree
    let hmap : Set.Icc (0 : ℝ) (n : ℝ) → Set.Icc (0 : ℝ) ((M : ℝ) + 1) :=
      fun u => ⟨(u : ℝ), ⟨u.2.1, by
        dsimp [M]
        push_cast
        linarith [u.2.2]⟩⟩
    have hmap_cont : Continuous hmap := by
      exact Continuous.subtype_mk continuous_subtype_val fun u =>
        ⟨u.2.1, by dsimp [M]; push_cast; linarith [u.2.2]⟩
    have hcontFixed : Continuous (fun u : Set.Icc (0 : ℝ) (n : ℝ) =>
        OscPath.at' (Y M ω) (hmap u)) := by
      change Continuous (fun u =>
        (show C(Set.Icc (0 : ℝ) ((M : ℝ) + 1), OscDual d m) from Y M ω) (hmap u))
      exact (show C(Set.Icc (0 : ℝ) ((M : ℝ) + 1), OscDual d m) from Y M ω).continuous.comp
        hmap_cont
    have hEq : (fun u : Set.Icc (0 : ℝ) (n : ℝ) => Zraw u ω) =
        fun u => OscPath.at' (Y M ω) (hmap u) := by
      funext u
      exact hfixed u u.2
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun u : Set.Icc (0 : ℝ) (n : ℝ) => Zraw (u : ℝ) ω)
    rw [hEq]
    exact hcontFixed
  have hcontPos : ∀ ω, ω ∉ Bad → ContinuousOn (fun t => Zraw t ω) (Set.Ici (0 : ℝ)) := by
    intro ω hω
    exact fp81s21_contOn_Ici_of_nat (fun t => Zraw t ω) (hcontN ω hω)
  have hcontZ : ∀ ω, Continuous (fun t => Z t ω) := by
    intro ω
    by_cases hω : ω ∈ Bad
    · have heq : (fun t => Z t ω) = fun _ => (0 : OscDual d m) := by
        funext t
        simp [Z, Zraw, hω]
      simpa [heq] using (continuous_const : Continuous fun _ : ℝ => (0 : OscDual d m))
    · change Continuous (fun t => Zraw (max t 0) ω)
      exact (hcontPos ω hω).comp_continuous
        (continuous_id.max continuous_const) (fun t => Set.mem_Ici.mpr (le_max_right t 0))
  have hmeasZ : ∀ t, Measurable (fun ω => Z t ω) := by
    intro t
    have hEval : Measurable (fun ω =>
        if ht : 0 ≤ max t 0 then
          OscPath.at' (Y (fp81s21_patchIndex (max t 0)) ω)
            ⟨max t 0, fp81s21_patchIndex_mem_of_nonneg ht⟩
        else 0) := by
      simp only [dif_pos (le_max_right t 0)]
      exact (ContinuousMap.measurable_eval _).comp
        (hYmeas (fp81s21_patchIndex (max t 0)))
    exact Measurable.ite hBadm measurable_const hEval
  refine ⟨Z, measurable_uncurry_of_continuous_of_measurable hcontZ hmeasZ, hcontZ, ?_⟩
  intro t ht
  have htmax : max t 0 = t := max_eq_left ht
  have hidxmem : t ∈ Set.Icc (0 : ℝ)
      ((fp81s21_patchIndex (max t 0) : ℝ) + 1) := by
    constructor
    · exact ht
    · simpa only [htmax] using
        (fp81s21_patchIndex_mem_of_nonneg (le_max_right t 0)).2
  have hmodt : (fun ω => OscPath.at' (Y (fp81s21_patchIndex (max t 0)) ω)
      ⟨t, hidxmem⟩) =ᵐ[P] X t := hmod (fp81s21_patchIndex (max t 0)) t hidxmem
  filter_upwards [hgoodAE, hmodt] with ω hω hωmod
  simp only [Z, Zraw, htmax, if_neg hω, dif_pos ht]
  exact hωmod

#print axioms fp81s21_patch_nat_modifications

end HRS.Fp81.S21

end
