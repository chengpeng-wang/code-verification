import QuickselectUpper
import QuickselectLower

namespace Example04Rust

/-- The worst-case instruction count for the linked Rust Hoare Quickselect
    binary. The upper bound holds for every valid call and includes normal
    return. For each feasible length at least nine, some valid call meets
    the lower bound. Both bounds count through the first return, including
    RET, and use the same denominator `rank n = 2^floor(log₉ n)`. -/
theorem quickselect_worst_case :
    WorstCaseUpper (stepBudget 80) ∧ WorstCaseLower 2 :=
  ⟨quickselect_worst_case_upper, quickselect_worst_case_lower⟩

#print axioms quickselect_worst_case

end Example04Rust
