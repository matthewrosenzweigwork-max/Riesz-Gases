import HRS.MS.CzElemBAux2

/-!
# ELEM-B tie

`HRS.CZ.ElemB.lp_tensor_absorption_proof` has exactly the type of the frozen
`HRS.Whole.AppendixA.lp_tensor_absorption` (`AppendixAAdjoint.lean:953`): the `example` below is the tie.
-/

example : type_of% @HRS.Whole.AppendixA.lp_tensor_absorption :=
  @HRS.CZ.ElemB.lp_tensor_absorption_proof
