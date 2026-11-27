/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Teddy Tennant
-/
import IEANTN.Nodes.ButheNumerics.v1.Conclusions
import IEANTN.Nodes.ButheNumerics.v2.Conclusions

/-!
# Bridge: `ButheNumerics.v2.lemma_3_constant_nonpos` gives the v1 conclusion

The two are the same proposition. Not designated on `ButheNumerics.v1` until `ButheNumerics.v2`
has a receipt: designating it sooner would replace a numerical leaf with an unverified one.
-/

namespace ButheNumerics

theorem lemma_3_constant_nonpos_v2_to_v1 (h : ButheNumerics.v2.lemma_3_constant_nonpos) :
    ButheNumerics.v1.lemma_3_constant_nonpos :=
  h

end ButheNumerics
