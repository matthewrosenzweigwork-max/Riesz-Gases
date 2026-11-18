import HRS.MC.D1E
import HRS.MC.D1T
import HRS.MC.D1T0

/-!
# Packet D1ASM: Lemma D.1 (`HRS.fdl_rep`), assembled from the Euclidean constants (`D1E`) and the torus
clause (`D1T` for `s > 0`, `D1T0` for `s = 0`).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.D1ASM

open HRS

variable {d : ℕ}

theorem fdl_rep_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) : ∃ b : ℝ, IsFDLConst ψ s b := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨b, hb0, hbφ, C, hC⟩ := MC.D1E.d1e_zero hd le_rfl hsd hψ rfl
    refine ⟨b, hb0, fun h => absurd h (lt_irrefl 0), fun _ => ⟨C, hC⟩, ?_⟩
    simpa using MC.D1T0.d1t0_zero hd hψ hb0 hbφ
  · obtain ⟨b, hb0, hb⟩ := MC.D1E.d1e_pos hd hs0 hsd hψ hpos
    refine ⟨b, hb0, fun _ => hb, fun h => absurd h hpos.ne', ?_⟩
    exact MC.D1T.d1t_pos hd hpos hsd hψ hb0 (fun x hx => (hb x hx).2)

example := (@fdl_rep_proof : type_of% @HRS.fdl_rep)

end HRS.MC.D1ASM
