import HRS.Appendix.B15BAux1

/-!
# Packet B15-DV: tie for the Donsker–Varadhan formula

The proof `b15b_klDiv_eq_iSup_proof` lives in `HRS/Appendix/B15BDV.lean` (Mathlib-only, imported by
`B15BAux1.lean`, whose `b15b_klDiv_eq_iSup` is now proved from it, so the packet-B chain is sorry-free).
-/

namespace HRS

example := (@b15b_klDiv_eq_iSup_proof : type_of% @b15b_klDiv_eq_iSup)

end HRS
