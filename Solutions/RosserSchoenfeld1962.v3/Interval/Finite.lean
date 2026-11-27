/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import Interval.Data000
import Interval.Data001
import Interval.Data002
import Interval.Data003
import Interval.Data004
import Interval.Data005
import Interval.Data006
import Interval.Data007
import Interval.Data008
import Interval.Data009
import Interval.Data010
import Interval.Data011
import Interval.Data012
import Interval.Data013
import Interval.Data014
import Interval.Data015
import Interval.Data016
import Interval.Data017
import Interval.Data018
import Interval.Data019
import Interval.Data020
import Interval.Data021
import Interval.Data022
import Interval.Data023
import Interval.Data024
import Interval.Data025
import Interval.Data026
import Interval.Data027
import Interval.Data028
import Interval.Data029
import Interval.Data030
import Interval.Data031
import Interval.Data032
import Interval.Data033
import Interval.Data034
import Interval.Data035
import Interval.Data036
import Interval.Data037
import Interval.Data038
import Interval.Data039
import Interval.Data040
import Interval.Data041
import Interval.Data042
import Interval.Data043
import Interval.Data044
import Interval.Data045
import Interval.Data046
import Interval.Data047

namespace RSInterval

theorem finite (x : ℝ) (hx : (41:ℝ)/2 ≤ x) (hx' : x < 4096) :
    3*x/(5*Real.log x) < IEANTN.primeCounting (2*x) - IEANTN.primeCounting x := by
  by_cases h0 : x < (46:ℝ)/2
  · exact finite_000 x (by linarith) h0
  by_cases h1 : x < (49:ℝ)/2
  · exact finite_001 x (by linarith) h1
  by_cases h2 : x < (55:ℝ)/2
  · exact finite_002 x (by linarith) h2
  by_cases h3 : x < (59:ℝ)/2
  · exact finite_003 x (by linarith) h3
  by_cases h4 : x < (62:ℝ)/2
  · exact finite_004 x (by linarith) h4
  by_cases h5 : x < (69:ℝ)/2
  · exact finite_005 x (by linarith) h5
  by_cases h6 : x < (77:ℝ)/2
  · exact finite_006 x (by linarith) h6
  by_cases h7 : x < (86:ℝ)/2
  · exact finite_007 x (by linarith) h7
  by_cases h8 : x < (94:ℝ)/2
  · exact finite_008 x (by linarith) h8
  by_cases h9 : x < (103:ℝ)/2
  · exact finite_009 x (by linarith) h9
  by_cases h10 : x < (115:ℝ)/2
  · exact finite_010 x (by linarith) h10
  by_cases h11 : x < (129:ℝ)/2
  · exact finite_011 x (by linarith) h11
  by_cases h12 : x < (145:ℝ)/2
  · exact finite_012 x (by linarith) h12
  by_cases h13 : x < (163:ℝ)/2
  · exact finite_013 x (by linarith) h13
  by_cases h14 : x < (183:ℝ)/2
  · exact finite_014 x (by linarith) h14
  by_cases h15 : x < (205:ℝ)/2
  · exact finite_015 x (by linarith) h15
  by_cases h16 : x < (226:ℝ)/2
  · exact finite_016 x (by linarith) h16
  by_cases h17 : x < (249:ℝ)/2
  · exact finite_017 x (by linarith) h17
  by_cases h18 : x < (277:ℝ)/2
  · exact finite_018 x (by linarith) h18
  by_cases h19 : x < (311:ℝ)/2
  · exact finite_019 x (by linarith) h19
  by_cases h20 : x < (349:ℝ)/2
  · exact finite_020 x (by linarith) h20
  by_cases h21 : x < (392:ℝ)/2
  · exact finite_021 x (by linarith) h21
  by_cases h22 : x < (441:ℝ)/2
  · exact finite_022 x (by linarith) h22
  by_cases h23 : x < (496:ℝ)/2
  · exact finite_023 x (by linarith) h23
  by_cases h24 : x < (558:ℝ)/2
  · exact finite_024 x (by linarith) h24
  by_cases h25 : x < (627:ℝ)/2
  · exact finite_025 x (by linarith) h25
  by_cases h26 : x < (705:ℝ)/2
  · exact finite_026 x (by linarith) h26
  by_cases h27 : x < (793:ℝ)/2
  · exact finite_027 x (by linarith) h27
  by_cases h28 : x < (892:ℝ)/2
  · exact finite_028 x (by linarith) h28
  by_cases h29 : x < (1003:ℝ)/2
  · exact finite_029 x (by linarith) h29
  by_cases h30 : x < (1128:ℝ)/2
  · exact finite_030 x (by linarith) h30
  by_cases h31 : x < (1269:ℝ)/2
  · exact finite_031 x (by linarith) h31
  by_cases h32 : x < (1427:ℝ)/2
  · exact finite_032 x (by linarith) h32
  by_cases h33 : x < (1605:ℝ)/2
  · exact finite_033 x (by linarith) h33
  by_cases h34 : x < (1805:ℝ)/2
  · exact finite_034 x (by linarith) h34
  by_cases h35 : x < (2030:ℝ)/2
  · exact finite_035 x (by linarith) h35
  by_cases h36 : x < (2283:ℝ)/2
  · exact finite_036 x (by linarith) h36
  by_cases h37 : x < (2568:ℝ)/2
  · exact finite_037 x (by linarith) h37
  by_cases h38 : x < (2889:ℝ)/2
  · exact finite_038 x (by linarith) h38
  by_cases h39 : x < (3250:ℝ)/2
  · exact finite_039 x (by linarith) h39
  by_cases h40 : x < (3656:ℝ)/2
  · exact finite_040 x (by linarith) h40
  by_cases h41 : x < (4113:ℝ)/2
  · exact finite_041 x (by linarith) h41
  by_cases h42 : x < (4627:ℝ)/2
  · exact finite_042 x (by linarith) h42
  by_cases h43 : x < (5205:ℝ)/2
  · exact finite_043 x (by linarith) h43
  by_cases h44 : x < (5855:ℝ)/2
  · exact finite_044 x (by linarith) h44
  by_cases h45 : x < (6586:ℝ)/2
  · exact finite_045 x (by linarith) h45
  by_cases h46 : x < (7409:ℝ)/2
  · exact finite_046 x (by linarith) h46
  exact finite_047 x (by linarith) (by linarith)

end RSInterval
