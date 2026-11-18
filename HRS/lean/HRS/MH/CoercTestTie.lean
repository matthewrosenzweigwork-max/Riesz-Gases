import HRS.MH.CoercTestW7e
import HRS.Whole.AppendixALemmas

/-!
# CoercTest tie: `p_assembly` has the frozen type of `whole_coercivity_pair`.
-/

example := (@HRS.MH.CoercTest.p_assembly : type_of% @HRS.Whole.AppendixALemmas.whole_coercivity_pair)
