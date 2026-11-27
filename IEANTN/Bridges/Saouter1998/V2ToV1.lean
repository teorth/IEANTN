/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard
-/
import IEANTN.Nodes.Saouter1998.v1.Conclusions
import IEANTN.Nodes.Saouter1998.v2.Conclusions

/-!
# Bridge: `Saouter1998.v2.odd_up_to_1e20` gives the v1 conclusion

The two are the same proposition, with the same imports. Not designated on `Saouter1998.v1` until
`Saouter1998.v2` has a receipt: designating it sooner would replace a literature citation with an
unverified proof.
-/

namespace Saouter1998

theorem odd_up_to_1e20_v2_to_v1 (h : Saouter1998.v2.odd_up_to_1e20) :
    Saouter1998.v1.odd_up_to_1e20 :=
  h

end Saouter1998
