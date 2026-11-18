import HRS.MS.TransOpAux28
import HRS.MS.WsStatFinal

/-!
# S611: the translated-path rows from S2.1

* `mov_translated_stationary_proof`: S6.11 stationary form, unconditional, from the proved S2.1 (i)
  (`HRS.MS.S21.whole_space_stationary_proof`) and the conditional reduction `mov_translated_stationary_of_S21`.
* `mov_translated_prepared_of_S21ii`: the conditional reduction of S6.11 prepared form to S2.1 (ii).
-/

noncomputable section

namespace HRS.MS.TransOp

theorem mov_translated_stationary_proof : type_of% @HRS.Whole.mov_translated_stationary :=
  mov_translated_stationary_of_S21 HRS.MS.S21.whole_space_stationary_proof

example := (@mov_translated_stationary_proof : type_of% @HRS.Whole.mov_translated_stationary)

theorem mov_translated_prepared_of_S21ii (h : HRS.Whole.WholeSpacePreparedStatement) :
    type_of% @HRS.Whole.mov_translated_prepared :=
  mov_translated_prepared_of_S21 h

end HRS.MS.TransOp

end
