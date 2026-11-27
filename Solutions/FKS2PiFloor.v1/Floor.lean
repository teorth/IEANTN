/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Anchors
import CellBounds
import CertifiedCells
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions

namespace FKS2PiFloor

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Every arithmetic cell is half-open, including prime right endpoints. -/
theorem row_bound {x : ℝ} (hlo : 2.7 ≤ x) (hhi : x < 404) : IEANTN.Eπ x ≤ row x := by
  by_cases h3 : x < 3
  · exact small_cell_bound (a := 2) (b := 3) (c := 1) (lo := 2.7)
      (L := 0 / 10000) (U := 0 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hlo, h3⟩
      (by decide +kernel) (by decide +kernel) (by simp [Li_two]) (by simp [Li_two])
      (by simpa using small_plus_2) (by simpa using small_minus_2)
  have hx3 : (3 : ℝ) ≤ x := le_of_not_gt h3
  by_cases h5 : x < 5
  · exact small_cell_bound (a := 3) (b := 5) (c := 2) (lo := 3)
      (L := 11130 / 10000) (U := 11238 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx3, h5⟩
      (by decide +kernel) (by decide +kernel) Li_3.1 Li_3.2
      small_plus_3 small_minus_3
  have hx5 : (5 : ℝ) ≤ x := le_of_not_gt h5
  by_cases h7 : x < 7
  · exact small_cell_bound (a := 5) (b := 7) (c := 3) (lo := 5)
      (L := 25809 / 10000) (U := 25979 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx5, h7⟩
      (by decide +kernel) (by decide +kernel) Li_5.1 Li_5.2
      small_plus_5 small_minus_5
  have hx7 : (7 : ℝ) ≤ x := le_of_not_gt h7
  by_cases h10 : x < 10
  · exact small_cell_bound (a := 7) (b := 10) (c := 4) (lo := 7)
      (L := 37021 / 10000) (U := 37217 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx7, h10⟩
      (by decide +kernel) (by decide +kernel) Li_7.1 Li_7.2
      small_plus_7 small_minus_7
  have hx10 : (10 : ℝ) ≤ x := le_of_not_gt h10
  by_cases h11 : x < 11
  · exact small_cell_bound (a := 10) (b := 11) (c := 4) (lo := 10)
      (L := 51096 / 10000) (U := 51314 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx10, h11⟩
      (by decide +kernel) (by decide +kernel) Li_10.1 Li_10.2
      small_plus_10 small_minus_10
  have hx11 : (11 : ℝ) ≤ x := le_of_not_gt h11
  by_cases h13 : x < 13
  · exact small_cell_bound (a := 11) (b := 13) (c := 5) (lo := 11)
      (L := 55347 / 10000) (U := 55571 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx11, h13⟩
      (by decide +kernel) (by decide +kernel) Li_11.1 Li_11.2
      small_plus_11 small_minus_11
  have hx13 : (13 : ℝ) ≤ x := le_of_not_gt h13
  by_cases h17 : x < 17
  · exact small_cell_bound (a := 13) (b := 17) (c := 6) (lo := 13)
      (L := 63398 / 10000) (U := 63631 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx13, h17⟩
      (by decide +kernel) (by decide +kernel) Li_13.1 Li_13.2
      small_plus_13 small_minus_13
  have hx17 : (17 : ℝ) ≤ x := le_of_not_gt h17
  by_cases h19 : x < 19
  · exact small_cell_bound (a := 17) (b := 19) (c := 7) (lo := 17)
      (L := 78190 / 10000) (U := 78438 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx17, h19⟩
      (by decide +kernel) (by decide +kernel) Li_17.1 Li_17.2
      small_plus_17 small_minus_17
  have hx19 : (19 : ℝ) ≤ x := le_of_not_gt h19
  by_cases h23 : x < 23
  · exact small_cell_bound (a := 19) (b := 23) (c := 8) (lo := 19)
      (L := 85108 / 10000) (U := 85363 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx19, h23⟩
      (by decide +kernel) (by decide +kernel) Li_19.1 Li_19.2
      small_plus_19 small_minus_19
  have hx23 : (23 : ℝ) ≤ x := le_of_not_gt h23
  by_cases h29 : x < 29
  · exact small_cell_bound (a := 23) (b := 29) (c := 9) (lo := 23)
      (L := 98250 / 10000) (U := 98518 / 10000)
      (by norm_num) (by norm_num) (by norm_num) ⟨hx23, h29⟩
      (by decide +kernel) (by decide +kernel) Li_23.1 Li_23.2
      small_plus_23 small_minus_23
  have hx29 : (29 : ℝ) ≤ x := le_of_not_gt h29
  have hL := global_lower_bound hx29
  have hU := global_upper_bound hx29
  by_cases h31 : x < 31
  · exact large_cell_bound (a := 29) (b := 31) (c := 10)
      (by norm_num) ⟨hx29, h31⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_29 large_minus_29
  have hx31 : (31 : ℝ) ≤ x := le_of_not_gt h31
  by_cases h37 : x < 37
  · exact large_cell_bound (a := 31) (b := 37) (c := 11)
      (by norm_num) ⟨hx31, h37⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_31 large_minus_31
  have hx37 : (37 : ℝ) ≤ x := le_of_not_gt h37
  by_cases h41 : x < 41
  · exact large_cell_bound (a := 37) (b := 41) (c := 12)
      (by norm_num) ⟨hx37, h41⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_37 large_minus_37
  have hx41 : (41 : ℝ) ≤ x := le_of_not_gt h41
  by_cases h43 : x < 43
  · exact large_cell_bound (a := 41) (b := 43) (c := 13)
      (by norm_num) ⟨hx41, h43⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_41 large_minus_41
  have hx43 : (43 : ℝ) ≤ x := le_of_not_gt h43
  by_cases h47 : x < 47
  · exact large_cell_bound (a := 43) (b := 47) (c := 14)
      (by norm_num) ⟨hx43, h47⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_43 large_minus_43
  have hx47 : (47 : ℝ) ≤ x := le_of_not_gt h47
  by_cases h53 : x < 53
  · exact large_cell_bound (a := 47) (b := 53) (c := 15)
      (by norm_num) ⟨hx47, h53⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_47 large_minus_47
  have hx53 : (53 : ℝ) ≤ x := le_of_not_gt h53
  by_cases h59 : x < 59
  · exact large_cell_bound (a := 53) (b := 59) (c := 16)
      (by norm_num) ⟨hx53, h59⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_53 large_minus_53
  have hx59 : (59 : ℝ) ≤ x := le_of_not_gt h59
  by_cases h61 : x < 61
  · exact large_cell_bound (a := 59) (b := 61) (c := 17)
      (by norm_num) ⟨hx59, h61⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_59 large_minus_59
  have hx61 : (61 : ℝ) ≤ x := le_of_not_gt h61
  by_cases h67 : x < 67
  · exact large_cell_bound (a := 61) (b := 67) (c := 18)
      (by norm_num) ⟨hx61, h67⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_61 large_minus_61
  have hx67 : (67 : ℝ) ≤ x := le_of_not_gt h67
  by_cases h71 : x < 71
  · exact large_cell_bound (a := 67) (b := 71) (c := 19)
      (by norm_num) ⟨hx67, h71⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_67 large_minus_67
  have hx71 : (71 : ℝ) ≤ x := le_of_not_gt h71
  by_cases h73 : x < 73
  · exact large_cell_bound (a := 71) (b := 73) (c := 20)
      (by norm_num) ⟨hx71, h73⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_71 large_minus_71
  have hx73 : (73 : ℝ) ≤ x := le_of_not_gt h73
  by_cases h79 : x < 79
  · exact large_cell_bound (a := 73) (b := 79) (c := 21)
      (by norm_num) ⟨hx73, h79⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_73 large_minus_73
  have hx79 : (79 : ℝ) ≤ x := le_of_not_gt h79
  by_cases h83 : x < 83
  · exact large_cell_bound (a := 79) (b := 83) (c := 22)
      (by norm_num) ⟨hx79, h83⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_79 large_minus_79
  have hx83 : (83 : ℝ) ≤ x := le_of_not_gt h83
  by_cases h89 : x < 89
  · exact large_cell_bound (a := 83) (b := 89) (c := 23)
      (by norm_num) ⟨hx83, h89⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_83 large_minus_83
  have hx89 : (89 : ℝ) ≤ x := le_of_not_gt h89
  by_cases h97 : x < 97
  · exact large_cell_bound (a := 89) (b := 97) (c := 24)
      (by norm_num) ⟨hx89, h97⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_89 large_minus_89
  have hx97 : (97 : ℝ) ≤ x := le_of_not_gt h97
  by_cases h101 : x < 101
  · exact large_cell_bound (a := 97) (b := 101) (c := 25)
      (by norm_num) ⟨hx97, h101⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_97 large_minus_97
  have hx101 : (101 : ℝ) ≤ x := le_of_not_gt h101
  by_cases h103 : x < 103
  · exact large_cell_bound (a := 101) (b := 103) (c := 26)
      (by norm_num) ⟨hx101, h103⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_101 large_minus_101
  have hx103 : (103 : ℝ) ≤ x := le_of_not_gt h103
  by_cases h107 : x < 107
  · exact large_cell_bound (a := 103) (b := 107) (c := 27)
      (by norm_num) ⟨hx103, h107⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_103 large_minus_103
  have hx107 : (107 : ℝ) ≤ x := le_of_not_gt h107
  by_cases h109 : x < 109
  · exact large_cell_bound (a := 107) (b := 109) (c := 28)
      (by norm_num) ⟨hx107, h109⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_107 large_minus_107
  have hx109 : (109 : ℝ) ≤ x := le_of_not_gt h109
  by_cases h113 : x < 113
  · exact large_cell_bound (a := 109) (b := 113) (c := 29)
      (by norm_num) ⟨hx109, h113⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_109 large_minus_109
  have hx113 : (113 : ℝ) ≤ x := le_of_not_gt h113
  by_cases h127 : x < 127
  · exact large_cell_bound (a := 113) (b := 127) (c := 30)
      (by norm_num) ⟨hx113, h127⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_113 large_minus_113
  have hx127 : (127 : ℝ) ≤ x := le_of_not_gt h127
  by_cases h131 : x < 131
  · exact large_cell_bound (a := 127) (b := 131) (c := 31)
      (by norm_num) ⟨hx127, h131⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_127 large_minus_127
  have hx131 : (131 : ℝ) ≤ x := le_of_not_gt h131
  by_cases h137 : x < 137
  · exact large_cell_bound (a := 131) (b := 137) (c := 32)
      (by norm_num) ⟨hx131, h137⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_131 large_minus_131
  have hx137 : (137 : ℝ) ≤ x := le_of_not_gt h137
  by_cases h139 : x < 139
  · exact large_cell_bound (a := 137) (b := 139) (c := 33)
      (by norm_num) ⟨hx137, h139⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_137 large_minus_137
  have hx139 : (139 : ℝ) ≤ x := le_of_not_gt h139
  by_cases h149 : x < 149
  · exact large_cell_bound (a := 139) (b := 149) (c := 34)
      (by norm_num) ⟨hx139, h149⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_139 large_minus_139
  have hx149 : (149 : ℝ) ≤ x := le_of_not_gt h149
  by_cases h151 : x < 151
  · exact large_cell_bound (a := 149) (b := 151) (c := 35)
      (by norm_num) ⟨hx149, h151⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_149 large_minus_149
  have hx151 : (151 : ℝ) ≤ x := le_of_not_gt h151
  by_cases h157 : x < 157
  · exact large_cell_bound (a := 151) (b := 157) (c := 36)
      (by norm_num) ⟨hx151, h157⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_151 large_minus_151
  have hx157 : (157 : ℝ) ≤ x := le_of_not_gt h157
  by_cases h163 : x < 163
  · exact large_cell_bound (a := 157) (b := 163) (c := 37)
      (by norm_num) ⟨hx157, h163⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_157 large_minus_157
  have hx163 : (163 : ℝ) ≤ x := le_of_not_gt h163
  by_cases h167 : x < 167
  · exact large_cell_bound (a := 163) (b := 167) (c := 38)
      (by norm_num) ⟨hx163, h167⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_163 large_minus_163
  have hx167 : (167 : ℝ) ≤ x := le_of_not_gt h167
  by_cases h173 : x < 173
  · exact large_cell_bound (a := 167) (b := 173) (c := 39)
      (by norm_num) ⟨hx167, h173⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_167 large_minus_167
  have hx173 : (173 : ℝ) ≤ x := le_of_not_gt h173
  by_cases h179 : x < 179
  · exact large_cell_bound (a := 173) (b := 179) (c := 40)
      (by norm_num) ⟨hx173, h179⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_173 large_minus_173
  have hx179 : (179 : ℝ) ≤ x := le_of_not_gt h179
  by_cases h181 : x < 181
  · exact large_cell_bound (a := 179) (b := 181) (c := 41)
      (by norm_num) ⟨hx179, h181⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_179 large_minus_179
  have hx181 : (181 : ℝ) ≤ x := le_of_not_gt h181
  by_cases h191 : x < 191
  · exact large_cell_bound (a := 181) (b := 191) (c := 42)
      (by norm_num) ⟨hx181, h191⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_181 large_minus_181
  have hx191 : (191 : ℝ) ≤ x := le_of_not_gt h191
  by_cases h193 : x < 193
  · exact large_cell_bound (a := 191) (b := 193) (c := 43)
      (by norm_num) ⟨hx191, h193⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_191 large_minus_191
  have hx193 : (193 : ℝ) ≤ x := le_of_not_gt h193
  by_cases h197 : x < 197
  · exact large_cell_bound (a := 193) (b := 197) (c := 44)
      (by norm_num) ⟨hx193, h197⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_193 large_minus_193
  have hx197 : (197 : ℝ) ≤ x := le_of_not_gt h197
  by_cases h199 : x < 199
  · exact large_cell_bound (a := 197) (b := 199) (c := 45)
      (by norm_num) ⟨hx197, h199⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_197 large_minus_197
  have hx199 : (199 : ℝ) ≤ x := le_of_not_gt h199
  by_cases h211 : x < 211
  · exact large_cell_bound (a := 199) (b := 211) (c := 46)
      (by norm_num) ⟨hx199, h211⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_199 large_minus_199
  have hx211 : (211 : ℝ) ≤ x := le_of_not_gt h211
  by_cases h223 : x < 223
  · exact large_cell_bound (a := 211) (b := 223) (c := 47)
      (by norm_num) ⟨hx211, h223⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_211 large_minus_211
  have hx223 : (223 : ℝ) ≤ x := le_of_not_gt h223
  by_cases h227 : x < 227
  · exact large_cell_bound (a := 223) (b := 227) (c := 48)
      (by norm_num) ⟨hx223, h227⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_223 large_minus_223
  have hx227 : (227 : ℝ) ≤ x := le_of_not_gt h227
  by_cases h229 : x < 229
  · exact large_cell_bound (a := 227) (b := 229) (c := 49)
      (by norm_num) ⟨hx227, h229⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_227 large_minus_227
  have hx229 : (229 : ℝ) ≤ x := le_of_not_gt h229
  by_cases h233 : x < 233
  · exact large_cell_bound (a := 229) (b := 233) (c := 50)
      (by norm_num) ⟨hx229, h233⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_229 large_minus_229
  have hx233 : (233 : ℝ) ≤ x := le_of_not_gt h233
  by_cases h239 : x < 239
  · exact large_cell_bound (a := 233) (b := 239) (c := 51)
      (by norm_num) ⟨hx233, h239⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_233 large_minus_233
  have hx239 : (239 : ℝ) ≤ x := le_of_not_gt h239
  by_cases h241 : x < 241
  · exact large_cell_bound (a := 239) (b := 241) (c := 52)
      (by norm_num) ⟨hx239, h241⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_239 large_minus_239
  have hx241 : (241 : ℝ) ≤ x := le_of_not_gt h241
  by_cases h251 : x < 251
  · exact large_cell_bound (a := 241) (b := 251) (c := 53)
      (by norm_num) ⟨hx241, h251⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_241 large_minus_241
  have hx251 : (251 : ℝ) ≤ x := le_of_not_gt h251
  by_cases h257 : x < 257
  · exact large_cell_bound (a := 251) (b := 257) (c := 54)
      (by norm_num) ⟨hx251, h257⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_251 large_minus_251
  have hx257 : (257 : ℝ) ≤ x := le_of_not_gt h257
  by_cases h263 : x < 263
  · exact large_cell_bound (a := 257) (b := 263) (c := 55)
      (by norm_num) ⟨hx257, h263⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_257 large_minus_257
  have hx263 : (263 : ℝ) ≤ x := le_of_not_gt h263
  by_cases h269 : x < 269
  · exact large_cell_bound (a := 263) (b := 269) (c := 56)
      (by norm_num) ⟨hx263, h269⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_263 large_minus_263
  have hx269 : (269 : ℝ) ≤ x := le_of_not_gt h269
  by_cases h271 : x < 271
  · exact large_cell_bound (a := 269) (b := 271) (c := 57)
      (by norm_num) ⟨hx269, h271⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_269 large_minus_269
  have hx271 : (271 : ℝ) ≤ x := le_of_not_gt h271
  by_cases h277 : x < 277
  · exact large_cell_bound (a := 271) (b := 277) (c := 58)
      (by norm_num) ⟨hx271, h277⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_271 large_minus_271
  have hx277 : (277 : ℝ) ≤ x := le_of_not_gt h277
  by_cases h281 : x < 281
  · exact large_cell_bound (a := 277) (b := 281) (c := 59)
      (by norm_num) ⟨hx277, h281⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_277 large_minus_277
  have hx281 : (281 : ℝ) ≤ x := le_of_not_gt h281
  by_cases h283 : x < 283
  · exact large_cell_bound (a := 281) (b := 283) (c := 60)
      (by norm_num) ⟨hx281, h283⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_281 large_minus_281
  have hx283 : (283 : ℝ) ≤ x := le_of_not_gt h283
  by_cases h293 : x < 293
  · exact large_cell_bound (a := 283) (b := 293) (c := 61)
      (by norm_num) ⟨hx283, h293⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_283 large_minus_283
  have hx293 : (293 : ℝ) ≤ x := le_of_not_gt h293
  by_cases h307 : x < 307
  · exact large_cell_bound (a := 293) (b := 307) (c := 62)
      (by norm_num) ⟨hx293, h307⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_293 large_minus_293
  have hx307 : (307 : ℝ) ≤ x := le_of_not_gt h307
  by_cases h311 : x < 311
  · exact large_cell_bound (a := 307) (b := 311) (c := 63)
      (by norm_num) ⟨hx307, h311⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_307 large_minus_307
  have hx311 : (311 : ℝ) ≤ x := le_of_not_gt h311
  by_cases h313 : x < 313
  · exact large_cell_bound (a := 311) (b := 313) (c := 64)
      (by norm_num) ⟨hx311, h313⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_311 large_minus_311
  have hx313 : (313 : ℝ) ≤ x := le_of_not_gt h313
  by_cases h317 : x < 317
  · exact large_cell_bound (a := 313) (b := 317) (c := 65)
      (by norm_num) ⟨hx313, h317⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_313 large_minus_313
  have hx317 : (317 : ℝ) ≤ x := le_of_not_gt h317
  by_cases h331 : x < 331
  · exact large_cell_bound (a := 317) (b := 331) (c := 66)
      (by norm_num) ⟨hx317, h331⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_317 large_minus_317
  have hx331 : (331 : ℝ) ≤ x := le_of_not_gt h331
  by_cases h337 : x < 337
  · exact large_cell_bound (a := 331) (b := 337) (c := 67)
      (by norm_num) ⟨hx331, h337⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_331 large_minus_331
  have hx337 : (337 : ℝ) ≤ x := le_of_not_gt h337
  by_cases h347 : x < 347
  · exact large_cell_bound (a := 337) (b := 347) (c := 68)
      (by norm_num) ⟨hx337, h347⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_337 large_minus_337
  have hx347 : (347 : ℝ) ≤ x := le_of_not_gt h347
  by_cases h349 : x < 349
  · exact large_cell_bound (a := 347) (b := 349) (c := 69)
      (by norm_num) ⟨hx347, h349⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_347 large_minus_347
  have hx349 : (349 : ℝ) ≤ x := le_of_not_gt h349
  by_cases h353 : x < 353
  · exact large_cell_bound (a := 349) (b := 353) (c := 70)
      (by norm_num) ⟨hx349, h353⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_349 large_minus_349
  have hx353 : (353 : ℝ) ≤ x := le_of_not_gt h353
  by_cases h359 : x < 359
  · exact large_cell_bound (a := 353) (b := 359) (c := 71)
      (by norm_num) ⟨hx353, h359⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_353 large_minus_353
  have hx359 : (359 : ℝ) ≤ x := le_of_not_gt h359
  by_cases h367 : x < 367
  · exact large_cell_bound (a := 359) (b := 367) (c := 72)
      (by norm_num) ⟨hx359, h367⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_359 large_minus_359
  have hx367 : (367 : ℝ) ≤ x := le_of_not_gt h367
  by_cases h373 : x < 373
  · exact large_cell_bound (a := 367) (b := 373) (c := 73)
      (by norm_num) ⟨hx367, h373⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_367 large_minus_367
  have hx373 : (373 : ℝ) ≤ x := le_of_not_gt h373
  by_cases h379 : x < 379
  · exact large_cell_bound (a := 373) (b := 379) (c := 74)
      (by norm_num) ⟨hx373, h379⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_373 large_minus_373
  have hx379 : (379 : ℝ) ≤ x := le_of_not_gt h379
  by_cases h383 : x < 383
  · exact large_cell_bound (a := 379) (b := 383) (c := 75)
      (by norm_num) ⟨hx379, h383⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_379 large_minus_379
  have hx383 : (383 : ℝ) ≤ x := le_of_not_gt h383
  by_cases h389 : x < 389
  · exact large_cell_bound (a := 383) (b := 389) (c := 76)
      (by norm_num) ⟨hx383, h389⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_383 large_minus_383
  have hx389 : (389 : ℝ) ≤ x := le_of_not_gt h389
  by_cases h397 : x < 397
  · exact large_cell_bound (a := 389) (b := 397) (c := 77)
      (by norm_num) ⟨hx389, h397⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_389 large_minus_389
  have hx397 : (397 : ℝ) ≤ x := le_of_not_gt h397
  by_cases h401 : x < 401
  · exact large_cell_bound (a := 397) (b := 401) (c := 78)
      (by norm_num) ⟨hx397, h401⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_397 large_minus_397
  have hx401 : (401 : ℝ) ≤ x := le_of_not_gt h401
  exact large_cell_bound (a := 401) (b := 404) (c := 79)
      (by norm_num) ⟨hx401, hhi⟩
      (by decide +kernel) (by decide +kernel) hL hU
      large_plus_401 large_minus_401

/-- The unchanged row-two floor from the FKS2 numerical node. -/
theorem table6_row2_floor : FKS2Numerics.v1.table6_row2_floor := by
  intro x hx
  have hlo : (2.7 : ℝ) ≤ x := lower_endpoint.trans hx.1
  have hhi : x < 404 := hx.2.trans_lt upper_endpoint
  have hx1 : (1 : ℝ) ≤ x := by linarith
  rw [show IEANTN.margin 0 = 1 by simp [IEANTN.margin], one_mul,
    admissibleBound_eq_row hx1]
  exact row_bound hlo hhi

end FKS2PiFloor
