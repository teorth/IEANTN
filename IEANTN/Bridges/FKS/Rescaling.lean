/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Teddy Tennant
-/
import IEANTN.Nodes.FKS.v1.Conclusions
import IEANTN.Nodes.FKSRescaling.v1.Conclusions

/-!
# Bridge: `FKSRescaling.v1`'s two comparisons give `FKS.v1`'s

Each pair is the same proposition. Not designated on `FKS.v1` until `FKSRescaling.v1` has a
receipt: designating them sooner would replace a numerical leaf with an unverified one.
-/

namespace FKS

theorem rescaled_A_exceeds_printed_of_rescaling
    (h : FKSRescaling.v1.rescaled_A_exceeds_printed) : FKS.v1.rescaled_A_exceeds_printed :=
  h

theorem rescaled_C_is_short_of_two_of_rescaling
    (h : FKSRescaling.v1.rescaled_C_is_short_of_two) : FKS.v1.rescaled_C_is_short_of_two :=
  h

end FKS
