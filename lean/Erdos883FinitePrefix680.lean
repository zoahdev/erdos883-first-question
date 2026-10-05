import Erdos883AKEndpoints
import Erdos883SmallCertificate07
import Erdos883SmallCertificate09
import Erdos883SmallCertificate11
import Erdos883SmallCertificate13
import Erdos883SmallCertificate15
import Erdos883SmallCertificate17
import Erdos883SmallCertificate19
import Erdos883SmallCertificate22
import Erdos883SmallCertificate25
import Erdos883SmallCertificate28
import Erdos883SmallCertificate31
import Erdos883SmallCertificate35
import Erdos883SmallCertificate39
import Erdos883SmallCertificate44
import Erdos883SmallCertificate49
import Erdos883SmallCertificate55
import Erdos883SmallCertificate61
import Erdos883SmallCertificate68
import Erdos883SmallCertificate75
import Erdos883SmallCertificate83
import Erdos883SmallCertificate92
import Erdos883SmallCertificate93
import Erdos883SmallCertificate103
import Erdos883SmallCertificate114
import Erdos883SmallCertificate115
import Erdos883SmallCertificate116
import Erdos883SmallCertificate117
import Erdos883SmallCertificate129
import Erdos883SmallCertificate130
import Erdos883SmallCertificate131
import Erdos883SmallCertificate132
import Erdos883SmallCertificate133
import Erdos883SmallCertificate134
import Erdos883SmallCertificate135
import Erdos883SmallCertificate136
import Erdos883SmallCertificate137
import Erdos883SmallCertificate138
import Erdos883SmallCertificate139
import Erdos883SmallCertificate140
import Erdos883SmallCertificate141
import Erdos883SmallCertificate142
import Erdos883SmallCertificate143
import Erdos883SmallCertificate158
import Erdos883SmallCertificate174
import Erdos883SmallCertificate192
import Erdos883SmallCertificate212
import Erdos883SmallCertificate234
import Erdos883SmallCertificate258
import Erdos883SmallCertificate284
import Erdos883SmallCertificate313
import Erdos883SmallCertificate345
import Erdos883SmallCertificate380
import Erdos883SmallCertificate419
import Erdos883SmallCertificate462
import Erdos883SmallCertificate509
import Erdos883SmallCertificate561
import Erdos883SmallCertificate618
import Erdos883SmallCertificate680

namespace Erdos883Verified

/-- A completely checked interval cover for the finite prefix through `680`. -/
theorem finiteIntervalCover_through680 (n : ℕ) (hn : 6 ≤ n) (hnU : n ≤ 680) :
    ∃ L U : ℕ, ∃ O ps : List ℕ,
      6 ≤ L ∧ L ≤ n ∧ n ≤ U ∧ O.Nodup ∧
      O.toFinset = oddUniverse U ∧ ExactIntervalCertificate L U O ps := by
  by_cases h7 : n ≤ 7
  · exact ⟨6, 7, smallOrder07, [3, 5, 7, 11], by omega, by omega, h7,
      smallOrder07_nodup, smallOrder07_set, exactCertificate06_07⟩
  by_cases h9 : n ≤ 9
  · exact ⟨8, 9, smallOrder09, [3, 5, 7, 11], by omega, by omega, h9,
      smallOrder09_nodup, smallOrder09_set, exactCertificate08_09⟩
  by_cases h11 : n ≤ 11
  · exact ⟨10, 11, smallOrder11, [3, 5, 7, 11], by omega, by omega, h11,
      smallOrder11_nodup, smallOrder11_set, exactCertificate10_11⟩
  by_cases h13 : n ≤ 13
  · exact ⟨12, 13, smallOrder13, [3, 5, 7, 11], by omega, by omega, h13,
      smallOrder13_nodup, smallOrder13_set, exactCertificate12_13⟩
  by_cases h15 : n ≤ 15
  · exact ⟨14, 15, smallOrder15, [3, 5, 7, 11], by omega, by omega, h15,
      smallOrder15_nodup, smallOrder15_set, exactCertificate14_15⟩
  by_cases h17 : n ≤ 17
  · exact ⟨16, 17, smallOrder17, [3, 5, 7, 11], by omega, by omega, h17,
      smallOrder17_nodup, smallOrder17_set, exactCertificate16_17⟩
  by_cases h19 : n ≤ 19
  · exact ⟨18, 19, smallOrder19, [3, 5, 7, 11], by omega, by omega, h19,
      smallOrder19_nodup, smallOrder19_set, exactCertificate18_19⟩
  by_cases h22 : n ≤ 22
  · exact ⟨20, 22, smallOrder22, [3, 5, 7, 11], by omega, by omega, h22,
      smallOrder22_nodup, smallOrder22_set, exactCertificate20_22⟩
  by_cases h25 : n ≤ 25
  · exact ⟨23, 25, smallOrder25, [3, 5, 7, 11], by omega, by omega, h25,
      smallOrder25_nodup, smallOrder25_set, exactCertificate23_25⟩
  by_cases h28 : n ≤ 28
  · exact ⟨26, 28, smallOrder28, [3, 5, 7, 11], by omega, by omega, h28,
      smallOrder28_nodup, smallOrder28_set, exactCertificate26_28⟩
  by_cases h31 : n ≤ 31
  · exact ⟨29, 31, smallOrder31, [3, 5, 7, 11], by omega, by omega, h31,
      smallOrder31_nodup, smallOrder31_set, exactCertificate29_31⟩
  by_cases h35 : n ≤ 35
  · exact ⟨32, 35, smallOrder35, [3, 5, 7, 11], by omega, by omega, h35,
      smallOrder35_nodup, smallOrder35_set, exactCertificate32_35⟩
  by_cases h39 : n ≤ 39
  · exact ⟨36, 39, smallOrder39, [3, 5, 7, 11], by omega, by omega, h39,
      smallOrder39_nodup, smallOrder39_set, exactCertificate36_39⟩
  by_cases h44 : n ≤ 44
  · exact ⟨40, 44, smallOrder44, [3, 5, 7, 11], by omega, by omega, h44,
      smallOrder44_nodup, smallOrder44_set, exactCertificate40_44⟩
  by_cases h49 : n ≤ 49
  · exact ⟨45, 49, smallOrder49, [3, 5, 7, 11], by omega, by omega, h49,
      smallOrder49_nodup, smallOrder49_set, exactCertificate45_49⟩
  by_cases h55 : n ≤ 55
  · exact ⟨50, 55, smallOrder55, [3, 5, 7, 11], by omega, by omega, h55,
      smallOrder55_nodup, smallOrder55_set, exactCertificate50_55⟩
  by_cases h61 : n ≤ 61
  · exact ⟨56, 61, smallOrder61, [3, 5, 7, 11], by omega, by omega, h61,
      smallOrder61_nodup, smallOrder61_set, exactCertificate56_61⟩
  by_cases h68 : n ≤ 68
  · exact ⟨62, 68, smallOrder68, [3, 5, 7, 11], by omega, by omega, h68,
      smallOrder68_nodup, smallOrder68_set, exactCertificate62_68⟩
  by_cases h75 : n ≤ 75
  · exact ⟨69, 75, smallOrder75, [3, 5, 7, 11], by omega, by omega, h75,
      smallOrder75_nodup, smallOrder75_set, exactCertificate69_75⟩
  by_cases h83 : n ≤ 83
  · exact ⟨76, 83, smallOrder83, [3, 5, 7, 11], by omega, by omega, h83,
      smallOrder83_nodup, smallOrder83_set, exactCertificate76_83⟩
  by_cases h92 : n ≤ 92
  · exact ⟨84, 92, smallOrder92, [3, 5, 7, 11], by omega, by omega, h92,
      smallOrder92_nodup, smallOrder92_set, exactCertificate84_92⟩
  by_cases h93 : n ≤ 93
  · exact ⟨93, 93, smallOrder93, [3, 5, 7, 11], by omega, by omega, h93,
      smallOrder93_nodup, smallOrder93_set, exactCertificate93_93⟩
  by_cases h103 : n ≤ 103
  · exact ⟨94, 103, smallOrder103, [3, 5, 7, 11], by omega, by omega, h103,
      smallOrder103_nodup, smallOrder103_set, exactCertificate94_103⟩
  by_cases h114 : n ≤ 114
  · exact ⟨104, 114, smallOrder114, [3, 5, 7, 11], by omega, by omega, h114,
      smallOrder114_nodup, smallOrder114_set, exactCertificate104_114⟩
  by_cases h115 : n ≤ 115
  · exact ⟨115, 115, smallOrder115, [3, 5, 7, 11], by omega, by omega, h115,
      smallOrder115_nodup, smallOrder115_set, exactCertificate115_115⟩
  by_cases h116 : n ≤ 116
  · exact ⟨116, 116, smallOrder116, [3, 5, 7, 11], by omega, by omega, h116,
      smallOrder116_nodup, smallOrder116_set, exactCertificate116_116⟩
  by_cases h117 : n ≤ 117
  · exact ⟨117, 117, smallOrder117, [3, 5, 7, 11], by omega, by omega, h117,
      smallOrder117_nodup, smallOrder117_set, exactCertificate117_117⟩
  by_cases h129 : n ≤ 129
  · exact ⟨118, 129, smallOrder129, [3, 5, 7, 11], by omega, by omega, h129,
      smallOrder129_nodup, smallOrder129_set, exactCertificate118_129⟩
  by_cases h130 : n ≤ 130
  · exact ⟨130, 130, smallOrder130, [3, 5, 7, 11], by omega, by omega, h130,
      smallOrder130_nodup, smallOrder130_set, exactCertificate130_130⟩
  by_cases h131 : n ≤ 131
  · exact ⟨131, 131, smallOrder131, [3, 5, 7, 11], by omega, by omega, h131,
      smallOrder131_nodup, smallOrder131_set, exactCertificate131_131⟩
  by_cases h132 : n ≤ 132
  · exact ⟨132, 132, smallOrder132, [3, 5, 7, 11], by omega, by omega, h132,
      smallOrder132_nodup, smallOrder132_set, exactCertificate132_132⟩
  by_cases h133 : n ≤ 133
  · exact ⟨133, 133, smallOrder133, [3, 5, 7, 11], by omega, by omega, h133,
      smallOrder133_nodup, smallOrder133_set, exactCertificate133_133⟩
  by_cases h134 : n ≤ 134
  · exact ⟨134, 134, smallOrder134, [3, 5, 7, 11], by omega, by omega, h134,
      smallOrder134_nodup, smallOrder134_set, exactCertificate134_134⟩
  by_cases h135 : n ≤ 135
  · exact ⟨135, 135, smallOrder135, [3, 5, 7, 11], by omega, by omega, h135,
      smallOrder135_nodup, smallOrder135_set, exactCertificate135_135⟩
  by_cases h136 : n ≤ 136
  · exact ⟨136, 136, smallOrder136, [3, 5, 7, 11], by omega, by omega, h136,
      smallOrder136_nodup, smallOrder136_set, exactCertificate136_136⟩
  by_cases h137 : n ≤ 137
  · exact ⟨137, 137, smallOrder137, [3, 5, 7, 11], by omega, by omega, h137,
      smallOrder137_nodup, smallOrder137_set, exactCertificate137_137⟩
  by_cases h138 : n ≤ 138
  · exact ⟨138, 138, smallOrder138, [3, 5, 7, 11], by omega, by omega, h138,
      smallOrder138_nodup, smallOrder138_set, exactCertificate138_138⟩
  by_cases h139 : n ≤ 139
  · exact ⟨139, 139, smallOrder139, [3, 5, 7, 11], by omega, by omega, h139,
      smallOrder139_nodup, smallOrder139_set, exactCertificate139_139⟩
  by_cases h140 : n ≤ 140
  · exact ⟨140, 140, smallOrder140, [3, 5, 7, 11], by omega, by omega, h140,
      smallOrder140_nodup, smallOrder140_set, exactCertificate140_140⟩
  by_cases h141 : n ≤ 141
  · exact ⟨141, 141, smallOrder141, [3, 5, 7, 11], by omega, by omega, h141,
      smallOrder141_nodup, smallOrder141_set, exactCertificate141_141⟩
  by_cases h142 : n ≤ 142
  · exact ⟨142, 142, smallOrder142, [3, 5, 7, 11], by omega, by omega, h142,
      smallOrder142_nodup, smallOrder142_set, exactCertificate142_142⟩
  by_cases h143 : n ≤ 143
  · exact ⟨143, 143, smallOrder143, [3, 5, 7, 11], by omega, by omega, h143,
      smallOrder143_nodup, smallOrder143_set, exactCertificate143_143⟩
  by_cases h158 : n ≤ 158
  · exact ⟨144, 158, smallOrder158, [3, 5, 7, 11], by omega, by omega, h158,
      smallOrder158_nodup, smallOrder158_set, exactCertificate144_158⟩
  by_cases h174 : n ≤ 174
  · exact ⟨159, 174, smallOrder174, [3, 5, 7, 11], by omega, by omega, h174,
      smallOrder174_nodup, smallOrder174_set, exactCertificate159_174⟩
  by_cases h192 : n ≤ 192
  · exact ⟨175, 192, smallOrder192, [3, 5, 7, 11], by omega, by omega, h192,
      smallOrder192_nodup, smallOrder192_set, exactCertificate175_192⟩
  by_cases h212 : n ≤ 212
  · exact ⟨193, 212, smallOrder212, [3, 5, 7, 11], by omega, by omega, h212,
      smallOrder212_nodup, smallOrder212_set, exactCertificate193_212⟩
  by_cases h234 : n ≤ 234
  · exact ⟨213, 234, smallOrder234, [3, 5, 7, 11], by omega, by omega, h234,
      smallOrder234_nodup, smallOrder234_set, exactCertificate213_234⟩
  by_cases h258 : n ≤ 258
  · exact ⟨235, 258, smallOrder258, [3, 5, 7, 11], by omega, by omega, h258,
      smallOrder258_nodup, smallOrder258_set, exactCertificate235_258⟩
  by_cases h284 : n ≤ 284
  · exact ⟨259, 284, smallOrder284, [3, 5, 7, 11], by omega, by omega, h284,
      smallOrder284_nodup, smallOrder284_set, exactCertificate259_284⟩
  by_cases h313 : n ≤ 313
  · exact ⟨285, 313, smallOrder313, [3, 5, 7, 11], by omega, by omega, h313,
      smallOrder313_nodup, smallOrder313_set, exactCertificate285_313⟩
  by_cases h345 : n ≤ 345
  · exact ⟨314, 345, smallOrder345, [3, 5, 7, 11], by omega, by omega, h345,
      smallOrder345_nodup, smallOrder345_set, exactCertificate314_345⟩
  by_cases h380 : n ≤ 380
  · exact ⟨346, 380, smallOrder380, [3, 5, 7, 11], by omega, by omega, h380,
      smallOrder380_nodup, smallOrder380_set, exactCertificate346_380⟩
  by_cases h419 : n ≤ 419
  · exact ⟨381, 419, smallOrder419, [3, 5, 7, 11], by omega, by omega, h419,
      smallOrder419_nodup, smallOrder419_set, exactCertificate381_419⟩
  by_cases h462 : n ≤ 462
  · exact ⟨420, 462, smallOrder462, [3, 5, 7, 11], by omega, by omega, h462,
      smallOrder462_nodup, smallOrder462_set, exactCertificate420_462⟩
  by_cases h509 : n ≤ 509
  · exact ⟨463, 509, smallOrder509, [3, 5, 7, 11], by omega, by omega, h509,
      smallOrder509_nodup, smallOrder509_set, exactCertificate463_509⟩
  by_cases h561 : n ≤ 561
  · exact ⟨510, 561, smallOrder561, [3, 5, 7, 11], by omega, by omega, h561,
      smallOrder561_nodup, smallOrder561_set, exactCertificate510_561⟩
  by_cases h618 : n ≤ 618
  · exact ⟨562, 618, smallOrder618, [3, 5, 7, 11], by omega, by omega, h618,
      smallOrder618_nodup, smallOrder618_set, exactCertificate562_618⟩
  exact ⟨619, 680, smallOrder680, [3, 5, 7, 11], by omega, by omega, hnU,
    smallOrder680_nodup, smallOrder680_set, exactCertificate619_680⟩

/-- The canonical first-question conclusion is unconditional throughout this prefix. -/
theorem firstQuestion_through680 (n : ℕ) (hnU : n ≤ 680)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 n)
    (hdense : n / 2 + n / 3 - n / 6 < A.card)
    (l : ℕ) (hl : Odd l) (h3 : 3 ≤ l) (hln : l ≤ n / 3 + 1) :
    l ∈ (Erdos883Target.coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  by_cases hsmall : n < 6
  · exact Erdos883Target.canonical_small_n hsmall A l hl h3 hln
  obtain ⟨k, hk, hkn, rfl⟩ :=
    (length_range_iff n l).mp ⟨hl, h3, hln⟩
  obtain ⟨L, U, O, ps, hL, hLn, hnU', hO, hOset, hcert⟩ :=
    finiteIntervalCover_through680 n (by omega) hnU
  exact exact_interval_criterion_with_proved_endpoints hL O ps hO hOset hcert
    hLn hnU' A hA hdense hk hkn

#print axioms finiteIntervalCover_through680
#print axioms firstQuestion_through680
end Erdos883Verified
