import Mathlib

namespace Obvious

def hello := "world"

syntax "obvious" : tactic

macro_rules
  | `(tactic| obvious) => `(tactic|
      first
      | ring; done
      | (
        ring_nf
        rw [Real.sq_sqrt]
        ring
        repeat obvious
        done
      )
      | (congr;(try (
        first
        | simp; done
        | (nlinarith; done)
        | (apply sq_nonneg; repeat obvious; done)
        | (apply div_nonneg; repeat obvious; done)
        | ((try field_simp); ring; done)
        | linarith; done))
    ))

end Obvious
