import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate345Resource000
import Erdos883SmallCertificate345Resource001
import Erdos883SmallCertificate345Resource002
import Erdos883SmallCertificate345Resource003
import Erdos883SmallCertificate345Resource004
import Erdos883SmallCertificate345Resource005
import Erdos883SmallCertificate345Resource006
import Erdos883SmallCertificate345Resource007
import Erdos883SmallCertificate345Resource008
import Erdos883SmallCertificate345Resource009
import Erdos883SmallCertificate345Resource010
import Erdos883SmallCertificate345Resource011
import Erdos883SmallCertificate345Resource012
import Erdos883SmallCertificate345Resource013
import Erdos883SmallCertificate345Resource014
import Erdos883SmallCertificate345Resource015
import Erdos883SmallCertificate345Resource016
import Erdos883SmallCertificate345Resource017
import Erdos883SmallCertificate345Resource018
import Erdos883SmallCertificate345Resource019
import Erdos883SmallCertificate345Resource020
import Erdos883SmallCertificate345Resource021
import Erdos883SmallCertificate345Resource022
import Erdos883SmallCertificate345Resource023
import Erdos883SmallCertificate345Resource024
import Erdos883SmallCertificate345Resource025
import Erdos883SmallCertificate345Resource026
import Erdos883SmallCertificate345Resource027
import Erdos883SmallCertificate345Resource028
import Erdos883SmallCertificate345Resource029
import Erdos883SmallCertificate345Resource030
import Erdos883SmallCertificate345Resource031
import Erdos883SmallCertificate345Resource032
import Erdos883SmallCertificate345Resource033
import Erdos883SmallCertificate345Resource034
import Erdos883SmallCertificate345Resource035
import Erdos883SmallCertificate345Resource036
import Erdos883SmallCertificate345Resource037
import Erdos883SmallCertificate345Resource038
import Erdos883SmallCertificate345Resource039
import Erdos883SmallCertificate345Resource040
import Erdos883SmallCertificate345Resource041
import Erdos883SmallCertificate345Resource042
import Erdos883SmallCertificate345Resource043
import Erdos883SmallCertificate345Resource044
import Erdos883SmallCertificate345Resource045
import Erdos883SmallCertificate345Resource046
import Erdos883SmallCertificate345Resource047
import Erdos883SmallCertificate345Resource048
import Erdos883SmallCertificate345Resource049
import Erdos883SmallCertificate345Resource050
import Erdos883SmallCertificate345Resource051
import Erdos883SmallCertificate345Resource052
import Erdos883SmallCertificate345Resource053
import Erdos883SmallCertificate345Resource054
import Erdos883SmallCertificate345Resource055
import Erdos883SmallCertificate345Resource056
import Erdos883SmallCertificate345Resource057
import Erdos883SmallCertificate345Resource058
import Erdos883SmallCertificate345Resource059
import Erdos883SmallCertificate345Resource060
import Erdos883SmallCertificate345Resource061
import Erdos883SmallCertificate345Resource062
import Erdos883SmallCertificate345Resource063
import Erdos883SmallCertificate345Resource064
import Erdos883SmallCertificate345Resource065
import Erdos883SmallCertificate345Resource066
import Erdos883SmallCertificate345Resource067
import Erdos883SmallCertificate345Resource068
import Erdos883SmallCertificate345Resource069
import Erdos883SmallCertificate345Resource070
import Erdos883SmallCertificate345Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder345 : List ℕ := coreData345.map (·.value)
theorem smallOrder345_nodup : smallOrder345.Nodup := by decide +kernel
theorem smallOrder345_set : smallOrder345.toFinset = oddUniverse 345 := by decide +kernel
private def resources345 (i : Fin 71) : PrefixResourceData := resourceOfCore (coreResources345 i)
private theorem dataValid345 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData345.map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValid345

private theorem validResource345_0 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 0) 0 312
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 314 smallOrder345 [3, 5, 7, 11] 0 312 false) coreChunks345_0 coreFlatten345_0 coreCheck345_0

private theorem validResource345_1 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 1) 32 312
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_0 coreChunks345_1 coreFlatten345_1 coreCheck345_1

private theorem validResource345_2 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 2) 33 311
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_1 coreChunks345_2 coreFlatten345_2 coreCheck345_2

private theorem validResource345_3 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 3) 42 310
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_2 coreChunks345_3 coreFlatten345_3 coreCheck345_3

private theorem validResource345_4 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 4) 43 309
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_3 coreChunks345_4 coreFlatten345_4 coreCheck345_4

private theorem validResource345_5 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 5) 46 308
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_4 coreChunks345_5 coreFlatten345_5 coreCheck345_5

private theorem validResource345_6 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 6) 65 273
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_5 coreChunks345_6 coreFlatten345_6 coreCheck345_6

private theorem validResource345_7 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 7) 68 264
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_6 coreChunks345_7 coreFlatten345_7 coreCheck345_7

private theorem validResource345_8 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 8) 69 254
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_7 coreChunks345_8 coreFlatten345_8 coreCheck345_8

private theorem validResource345_9 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 9) 70 246
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_8 coreChunks345_9 coreFlatten345_9 coreCheck345_9

private theorem validResource345_10 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 10) 72 243
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_9 coreChunks345_10 coreFlatten345_10 coreCheck345_10

private theorem validResource345_11 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 11) 73 240
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_10 coreChunks345_11 coreFlatten345_11 coreCheck345_11

private theorem validResource345_12 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 12) 74 239
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_11 coreChunks345_12 coreFlatten345_12 coreCheck345_12

private theorem validResource345_13 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 13) 75 237
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_12 coreChunks345_13 coreFlatten345_13 coreCheck345_13

private theorem validResource345_14 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 14) 76 234
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_13 coreChunks345_14 coreFlatten345_14 coreCheck345_14

private theorem validResource345_15 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 15) 79 233
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_14 coreChunks345_15 coreFlatten345_15 coreCheck345_15

private theorem validResource345_16 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 16) 80 231
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_15 coreChunks345_16 coreFlatten345_16 coreCheck345_16

private theorem validResource345_17 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 17) 81 227
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_16 coreChunks345_17 coreFlatten345_17 coreCheck345_17

private theorem validResource345_18 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 18) 84 221
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_17 coreChunks345_18 coreFlatten345_18 coreCheck345_18

private theorem validResource345_19 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 19) 85 220
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_18 coreChunks345_19 coreFlatten345_19 coreCheck345_19

private theorem validResource345_20 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 20) 87 218
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_19 coreChunks345_20 coreFlatten345_20 coreCheck345_20

private theorem validResource345_21 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 21) 0 155
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 314 smallOrder345 [3, 5, 7, 11] 0 155 true) coreChunks345_21 coreFlatten345_21 coreCheck345_21

private theorem validResource345_22 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 22) 48 155
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_21 coreChunks345_22 coreFlatten345_22 coreCheck345_22

private theorem validResource345_23 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 23) 49 154
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_22 coreChunks345_23 coreFlatten345_23 coreCheck345_23

private theorem validResource345_24 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 24) 54 153
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_23 coreChunks345_24 coreFlatten345_24 coreCheck345_24

private theorem validResource345_25 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 25) 55 152
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_24 coreChunks345_25 coreFlatten345_25 coreCheck345_25

private theorem validResource345_26 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 26) 57 151
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_25 coreChunks345_26 coreFlatten345_26 coreCheck345_26

private theorem validResource345_27 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 27) 58 150
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_26 coreChunks345_27 coreFlatten345_27 coreCheck345_27

private theorem validResource345_28 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 28) 59 148
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_27 coreChunks345_28 coreFlatten345_28 coreCheck345_28

private theorem validResource345_29 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 29) 60 147
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_28 coreChunks345_29 coreFlatten345_29 coreCheck345_29

private theorem validResource345_30 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 30) 61 146
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_29 coreChunks345_30 coreFlatten345_30 coreCheck345_30

private theorem validResource345_31 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 31) 62 143
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_30 coreChunks345_31 coreFlatten345_31 coreCheck345_31

private theorem validResource345_32 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 32) 64 140
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_31 coreChunks345_32 coreFlatten345_32 coreCheck345_32

private theorem validResource345_33 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 33) 66 136
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_32 coreChunks345_33 coreFlatten345_33 coreCheck345_33

private theorem validResource345_34 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 34) 68 132
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_33 coreChunks345_34 coreFlatten345_34 coreCheck345_34

private theorem validResource345_35 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 35) 69 126
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_34 coreChunks345_35 coreFlatten345_35 coreCheck345_35

private theorem validResource345_36 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 36) 70 122
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_35 coreChunks345_36 coreFlatten345_36 coreCheck345_36

private theorem validResource345_37 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 37) 72 121
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_36 coreChunks345_37 coreFlatten345_37 coreCheck345_37

private theorem validResource345_38 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 38) 73 119
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_37 coreChunks345_38 coreFlatten345_38 coreCheck345_38

private theorem validResource345_39 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 39) 74 118
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_38 coreChunks345_39 coreFlatten345_39 coreCheck345_39

private theorem validResource345_40 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 40) 75 117
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_39 coreChunks345_40 coreFlatten345_40 coreCheck345_40

private theorem validResource345_41 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 41) 80 115
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_40 coreChunks345_41 coreFlatten345_41 coreCheck345_41

private theorem validResource345_42 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 42) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 42) 81 113
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_41 coreChunks345_42 coreFlatten345_42 coreCheck345_42

private theorem validResource345_43 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 43) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 43) 84 110
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_42 coreChunks345_43 coreFlatten345_43 coreCheck345_43

private theorem validResource345_44 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 44) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 44) 85 109
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_43 coreChunks345_44 coreFlatten345_44 coreCheck345_44

private theorem validResource345_45 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 45) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 45) 87 108
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_44 coreChunks345_45 coreFlatten345_45 coreCheck345_45

private theorem validResource345_46 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 46) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 46) 88 107
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_45 coreChunks345_46 coreFlatten345_46 coreCheck345_46

private theorem validResource345_47 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 47) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 47) 89 106
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_46 coreChunks345_47 coreFlatten345_47 coreCheck345_47

private theorem validResource345_48 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 48) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 48) 90 105
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_47 coreChunks345_48 coreFlatten345_48 coreCheck345_48

private theorem validResource345_49 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 49) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 49) 93 101
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_48 coreChunks345_49 coreFlatten345_49 coreCheck345_49

private theorem validResource345_50 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 50) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 50) 94 99
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_49 coreChunks345_50 coreFlatten345_50 coreCheck345_50

private theorem validResource345_51 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 51) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 51) 98 97
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_50 coreChunks345_51 coreFlatten345_51 coreCheck345_51

private theorem validResource345_52 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 52) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 52) 101 96
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_51 coreChunks345_52 coreFlatten345_52 coreCheck345_52

private theorem validResource345_53 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 53) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 53) 102 95
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_52 coreChunks345_53 coreFlatten345_53 coreCheck345_53

private theorem validResource345_54 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 54) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 54) 105 94
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_53 coreChunks345_54 coreFlatten345_54 coreCheck345_54

private theorem validResource345_55 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 55) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 55) 106 93
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_54 coreChunks345_55 coreFlatten345_55 coreCheck345_55

private theorem validResource345_56 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 56) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 56) 107 92
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_55 coreChunks345_56 coreFlatten345_56 coreCheck345_56

private theorem validResource345_57 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 57) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 57) 108 91
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_56 coreChunks345_57 coreFlatten345_57 coreCheck345_57

private theorem validResource345_58 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 58) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 58) 115 90
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_57 coreChunks345_58 coreFlatten345_58 coreCheck345_58

private theorem validResource345_59 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 59) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 59) 120 72
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_58 coreChunks345_59 coreFlatten345_59 coreCheck345_59

private theorem validResource345_60 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 60) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 60) 129 71
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_59 coreChunks345_60 coreFlatten345_60 coreCheck345_60

private theorem validResource345_61 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 61) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 61) 138 70
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_60 coreChunks345_61 coreFlatten345_61 coreCheck345_61

private theorem validResource345_62 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 62) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 62) 146 69
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_61 coreChunks345_62 coreFlatten345_62 coreCheck345_62

private theorem validResource345_63 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 63) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 63) 150 68
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_62 coreChunks345_63 coreFlatten345_63 coreCheck345_63

private theorem validResource345_64 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 64) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 64) 152 67
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_63 coreChunks345_64 coreFlatten345_64 coreCheck345_64

private theorem validResource345_65 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 65) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 65) 164 66
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_64 coreChunks345_65 coreFlatten345_65 coreCheck345_65

private theorem validResource345_66 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 66) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 66) 0 90
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 314 smallOrder345 [3, 5, 7, 11] 1 90 true) coreChunks345_66 coreFlatten345_66 coreCheck345_66

private theorem validResource345_67 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 67) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 67) 0 105
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 314 smallOrder345 [3, 5, 7, 11] 2 105 true) coreChunks345_67 coreFlatten345_67 coreCheck345_67

private theorem validResource345_68 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 68) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 68) 112 105
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource345_67 coreChunks345_68 coreFlatten345_68 coreCheck345_68

private theorem validResource345_69 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 69) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 69) 0 234
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 314 smallOrder345 [3, 5, 7, 11] 3 234 false) coreChunks345_69 coreFlatten345_69 coreCheck345_69

private theorem validResource345_70 :
    PrefixResourceValid 314 smallOrder345 [3, 5, 7, 11] (resources345 70) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 314) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) (r := coreResources345 70) 0 115
    dataValid345 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 314 smallOrder345 [3, 5, 7, 11] 3 115 true) coreChunks345_70 coreFlatten345_70 coreCheck345_70

theorem finiteCheck314_345 : finiteIntervalCheck 314 345 smallOrder345 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 314) (U := 345) (O := smallOrder345)
    (ps := [3, 5, 7, 11]) resources345 coreSelector345
  · intro i
    fin_cases i
    · exact validResource345_0
    · exact validResource345_1
    · exact validResource345_2
    · exact validResource345_3
    · exact validResource345_4
    · exact validResource345_5
    · exact validResource345_6
    · exact validResource345_7
    · exact validResource345_8
    · exact validResource345_9
    · exact validResource345_10
    · exact validResource345_11
    · exact validResource345_12
    · exact validResource345_13
    · exact validResource345_14
    · exact validResource345_15
    · exact validResource345_16
    · exact validResource345_17
    · exact validResource345_18
    · exact validResource345_19
    · exact validResource345_20
    · exact validResource345_21
    · exact validResource345_22
    · exact validResource345_23
    · exact validResource345_24
    · exact validResource345_25
    · exact validResource345_26
    · exact validResource345_27
    · exact validResource345_28
    · exact validResource345_29
    · exact validResource345_30
    · exact validResource345_31
    · exact validResource345_32
    · exact validResource345_33
    · exact validResource345_34
    · exact validResource345_35
    · exact validResource345_36
    · exact validResource345_37
    · exact validResource345_38
    · exact validResource345_39
    · exact validResource345_40
    · exact validResource345_41
    · exact validResource345_42
    · exact validResource345_43
    · exact validResource345_44
    · exact validResource345_45
    · exact validResource345_46
    · exact validResource345_47
    · exact validResource345_48
    · exact validResource345_49
    · exact validResource345_50
    · exact validResource345_51
    · exact validResource345_52
    · exact validResource345_53
    · exact validResource345_54
    · exact validResource345_55
    · exact validResource345_56
    · exact validResource345_57
    · exact validResource345_58
    · exact validResource345_59
    · exact validResource345_60
    · exact validResource345_61
    · exact validResource345_62
    · exact validResource345_63
    · exact validResource345_64
    · exact validResource345_65
    · exact validResource345_66
    · exact validResource345_67
    · exact validResource345_68
    · exact validResource345_69
    · exact validResource345_70
  · intro b j
    exact resourceRequirements_of_core (coreRequirements345_0 b j)


theorem exactCertificate314_345 : ExactIntervalCertificate 314 345 smallOrder345 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck314_345
#print axioms smallOrder345_nodup
#print axioms smallOrder345_set
#print axioms finiteCheck314_345
#print axioms exactCertificate314_345
end Erdos883Verified
