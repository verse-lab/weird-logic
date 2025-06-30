import WeirdLogic.Lang

namespace WeirdLogic

lang_def C :=
  fun x a =>
    /- need to define choose a-/
    if a = true then
      x := x + 1
    else
      x := x +2




end WeirdLogic
