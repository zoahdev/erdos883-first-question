import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate380Resource000
import Erdos883SmallCertificate380Resource001
import Erdos883SmallCertificate380Resource002
import Erdos883SmallCertificate380Resource003
import Erdos883SmallCertificate380Resource004
import Erdos883SmallCertificate380Resource005
import Erdos883SmallCertificate380Resource006
import Erdos883SmallCertificate380Resource007
import Erdos883SmallCertificate380Resource008
import Erdos883SmallCertificate380Resource009
import Erdos883SmallCertificate380Resource010
import Erdos883SmallCertificate380Resource011
import Erdos883SmallCertificate380Resource012
import Erdos883SmallCertificate380Resource013
import Erdos883SmallCertificate380Resource014
import Erdos883SmallCertificate380Resource015
import Erdos883SmallCertificate380Resource016
import Erdos883SmallCertificate380Resource017
import Erdos883SmallCertificate380Resource018
import Erdos883SmallCertificate380Resource019
import Erdos883SmallCertificate380Resource020
import Erdos883SmallCertificate380Resource021
import Erdos883SmallCertificate380Resource022
import Erdos883SmallCertificate380Resource023
import Erdos883SmallCertificate380Resource024
import Erdos883SmallCertificate380Resource025
import Erdos883SmallCertificate380Resource026
import Erdos883SmallCertificate380Resource027
import Erdos883SmallCertificate380Resource028
import Erdos883SmallCertificate380Resource029
import Erdos883SmallCertificate380Resource030
import Erdos883SmallCertificate380Resource031
import Erdos883SmallCertificate380Resource032
import Erdos883SmallCertificate380Resource033
import Erdos883SmallCertificate380Resource034
import Erdos883SmallCertificate380Resource035
import Erdos883SmallCertificate380Resource036
import Erdos883SmallCertificate380Resource037
import Erdos883SmallCertificate380Resource038
import Erdos883SmallCertificate380Resource039
import Erdos883SmallCertificate380Resource040
import Erdos883SmallCertificate380Resource041
import Erdos883SmallCertificate380Resource042
import Erdos883SmallCertificate380Resource043
import Erdos883SmallCertificate380Resource044
import Erdos883SmallCertificate380Resource045
import Erdos883SmallCertificate380Resource046
import Erdos883SmallCertificate380Resource047
import Erdos883SmallCertificate380Resource048
import Erdos883SmallCertificate380Resource049
import Erdos883SmallCertificate380Resource050
import Erdos883SmallCertificate380Resource051
import Erdos883SmallCertificate380Resource052
import Erdos883SmallCertificate380Resource053
import Erdos883SmallCertificate380Resource054
import Erdos883SmallCertificate380Resource055
import Erdos883SmallCertificate380Resource056
import Erdos883SmallCertificate380Resource057
import Erdos883SmallCertificate380Resource058
import Erdos883SmallCertificate380Resource059
import Erdos883SmallCertificate380Resource060
import Erdos883SmallCertificate380Resource061
import Erdos883SmallCertificate380Resource062
import Erdos883SmallCertificate380Resource063
import Erdos883SmallCertificate380Resource064
import Erdos883SmallCertificate380Resource065
import Erdos883SmallCertificate380Resource066
import Erdos883SmallCertificate380Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder380 : List ℕ := coreData380.map (·.value)
theorem smallOrder380_nodup : smallOrder380.Nodup := by decide +kernel
theorem smallOrder380_set : smallOrder380.toFinset = oddUniverse 380 := by decide +kernel
private def resources380 (i : Fin 67) : PrefixResourceData := resourceOfCore (coreResources380 i)
private theorem dataValid380 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData380.map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValid380

private theorem validResource380_0 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 0) 0 344
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 346 smallOrder380 [3, 5, 7, 11] 0 344 false) coreChunks380_0 coreFlatten380_0 coreCheck380_0

private theorem validResource380_1 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 1) 36 344
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_0 coreChunks380_1 coreFlatten380_1 coreCheck380_1

private theorem validResource380_2 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 2) 37 343
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_1 coreChunks380_2 coreFlatten380_2 coreCheck380_2

private theorem validResource380_3 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 3) 46 342
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_2 coreChunks380_3 coreFlatten380_3 coreCheck380_3

private theorem validResource380_4 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 4) 47 341
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_3 coreChunks380_4 coreFlatten380_4 coreCheck380_4

private theorem validResource380_5 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 5) 50 340
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_4 coreChunks380_5 coreFlatten380_5 coreCheck380_5

private theorem validResource380_6 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 6) 75 291
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_5 coreChunks380_6 coreFlatten380_6 coreCheck380_6

private theorem validResource380_7 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 7) 77 280
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_6 coreChunks380_7 coreFlatten380_7 coreCheck380_7

private theorem validResource380_8 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 8) 78 274
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_7 coreChunks380_8 coreFlatten380_8 coreCheck380_8

private theorem validResource380_9 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 9) 79 271
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_8 coreChunks380_9 coreFlatten380_9 coreCheck380_9

private theorem validResource380_10 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 10) 81 268
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_9 coreChunks380_10 coreFlatten380_10 coreCheck380_10

private theorem validResource380_11 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 11) 82 265
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_10 coreChunks380_11 coreFlatten380_11 coreCheck380_11

private theorem validResource380_12 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 12) 83 262
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_11 coreChunks380_12 coreFlatten380_12 coreCheck380_12

private theorem validResource380_13 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 13) 84 260
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_12 coreChunks380_13 coreFlatten380_13 coreCheck380_13

private theorem validResource380_14 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 14) 85 258
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_13 coreChunks380_14 coreFlatten380_14 coreCheck380_14

private theorem validResource380_15 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 15) 88 255
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_14 coreChunks380_15 coreFlatten380_15 coreCheck380_15

private theorem validResource380_16 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 16) 89 253
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_15 coreChunks380_16 coreFlatten380_16 coreCheck380_16

private theorem validResource380_17 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 17) 90 247
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_16 coreChunks380_17 coreFlatten380_17 coreCheck380_17

private theorem validResource380_18 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 18) 92 243
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_17 coreChunks380_18 coreFlatten380_18 coreCheck380_18

private theorem validResource380_19 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 19) 0 171
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 346 smallOrder380 [3, 5, 7, 11] 0 171 true) coreChunks380_19 coreFlatten380_19 coreCheck380_19

private theorem validResource380_20 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 20) 53 171
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_19 coreChunks380_20 coreFlatten380_20 coreCheck380_20

private theorem validResource380_21 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 21) 54 170
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_20 coreChunks380_21 coreFlatten380_21 coreCheck380_21

private theorem validResource380_22 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 22) 60 169
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_21 coreChunks380_22 coreFlatten380_22 coreCheck380_22

private theorem validResource380_23 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 23) 61 168
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_22 coreChunks380_23 coreFlatten380_23 coreCheck380_23

private theorem validResource380_24 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 24) 62 167
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_23 coreChunks380_24 coreFlatten380_24 coreCheck380_24

private theorem validResource380_25 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 25) 63 166
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_24 coreChunks380_25 coreFlatten380_25 coreCheck380_25

private theorem validResource380_26 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 26) 65 165
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_25 coreChunks380_26 coreFlatten380_26 coreCheck380_26

private theorem validResource380_27 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 27) 66 164
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_26 coreChunks380_27 coreFlatten380_27 coreCheck380_27

private theorem validResource380_28 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 28) 67 163
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_27 coreChunks380_28 coreFlatten380_28 coreCheck380_28

private theorem validResource380_29 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 29) 68 161
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_28 coreChunks380_29 coreFlatten380_29 coreCheck380_29

private theorem validResource380_30 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 30) 70 157
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_29 coreChunks380_30 coreFlatten380_30 coreCheck380_30

private theorem validResource380_31 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 31) 72 154
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_30 coreChunks380_31 coreFlatten380_31 coreCheck380_31

private theorem validResource380_32 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 32) 74 150
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_31 coreChunks380_32 coreFlatten380_32 coreCheck380_32

private theorem validResource380_33 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 33) 76 146
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_32 coreChunks380_33 coreFlatten380_33 coreCheck380_33

private theorem validResource380_34 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 34) 77 139
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_33 coreChunks380_34 coreFlatten380_34 coreCheck380_34

private theorem validResource380_35 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 35) 78 136
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_34 coreChunks380_35 coreFlatten380_35 coreCheck380_35

private theorem validResource380_36 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 36) 81 134
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_35 coreChunks380_36 coreFlatten380_36 coreCheck380_36

private theorem validResource380_37 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 37) 82 132
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_36 coreChunks380_37 coreFlatten380_37 coreCheck380_37

private theorem validResource380_38 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 38) 83 130
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_37 coreChunks380_38 coreFlatten380_38 coreCheck380_38

private theorem validResource380_39 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 39) 84 129
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_38 coreChunks380_39 coreFlatten380_39 coreCheck380_39

private theorem validResource380_40 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 40) 89 127
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_39 coreChunks380_40 coreFlatten380_40 coreCheck380_40

private theorem validResource380_41 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 41) 90 124
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_40 coreChunks380_41 coreFlatten380_41 coreCheck380_41

private theorem validResource380_42 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 42) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 42) 92 122
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_41 coreChunks380_42 coreFlatten380_42 coreCheck380_42

private theorem validResource380_43 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 43) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 43) 95 121
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_42 coreChunks380_43 coreFlatten380_43 coreCheck380_43

private theorem validResource380_44 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 44) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 44) 97 120
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_43 coreChunks380_44 coreFlatten380_44 coreCheck380_44

private theorem validResource380_45 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 45) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 45) 98 119
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_44 coreChunks380_45 coreFlatten380_45 coreCheck380_45

private theorem validResource380_46 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 46) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 46) 99 117
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_45 coreChunks380_46 coreFlatten380_46 coreCheck380_46

private theorem validResource380_47 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 47) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 47) 100 116
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_46 coreChunks380_47 coreFlatten380_47 coreCheck380_47

private theorem validResource380_48 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 48) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 48) 103 112
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_47 coreChunks380_48 coreFlatten380_48 coreCheck380_48

private theorem validResource380_49 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 49) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 49) 104 109
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_48 coreChunks380_49 coreFlatten380_49 coreCheck380_49

private theorem validResource380_50 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 50) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 50) 109 107
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_49 coreChunks380_50 coreFlatten380_50 coreCheck380_50

private theorem validResource380_51 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 51) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 51) 111 106
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_50 coreChunks380_51 coreFlatten380_51 coreCheck380_51

private theorem validResource380_52 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 52) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 52) 117 105
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_51 coreChunks380_52 coreFlatten380_52 coreCheck380_52

private theorem validResource380_53 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 53) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 53) 118 104
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_52 coreChunks380_53 coreFlatten380_53 coreCheck380_53

private theorem validResource380_54 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 54) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 54) 120 102
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_53 coreChunks380_54 coreFlatten380_54 coreCheck380_54

private theorem validResource380_55 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 55) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 55) 127 100
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_54 coreChunks380_55 coreFlatten380_55 coreCheck380_55

private theorem validResource380_56 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 56) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 56) 132 80
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_55 coreChunks380_56 coreFlatten380_56 coreCheck380_56

private theorem validResource380_57 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 57) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 57) 139 79
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_56 coreChunks380_57 coreFlatten380_57 coreCheck380_57

private theorem validResource380_58 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 58) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 58) 148 78
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_57 coreChunks380_58 coreFlatten380_58 coreCheck380_58

private theorem validResource380_59 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 59) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 59) 159 77
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_58 coreChunks380_59 coreFlatten380_59 coreCheck380_59

private theorem validResource380_60 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 60) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 60) 163 76
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_59 coreChunks380_60 coreFlatten380_60 coreCheck380_60

private theorem validResource380_61 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 61) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 61) 174 74
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_60 coreChunks380_61 coreFlatten380_61 coreCheck380_61

private theorem validResource380_62 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 62) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 62) 181 70
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource380_61 coreChunks380_62 coreFlatten380_62 coreCheck380_62

private theorem validResource380_63 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 63) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 63) 0 100
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 346 smallOrder380 [3, 5, 7, 11] 1 100 true) coreChunks380_63 coreFlatten380_63 coreCheck380_63

private theorem validResource380_64 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 64) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 64) 0 116
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 346 smallOrder380 [3, 5, 7, 11] 2 116 true) coreChunks380_64 coreFlatten380_64 coreCheck380_64

private theorem validResource380_65 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 65) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 65) 0 258
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 346 smallOrder380 [3, 5, 7, 11] 3 258 false) coreChunks380_65 coreFlatten380_65 coreCheck380_65

private theorem validResource380_66 :
    PrefixResourceValid 346 smallOrder380 [3, 5, 7, 11] (resources380 66) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 346) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) (r := coreResources380 66) 0 127
    dataValid380 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 346 smallOrder380 [3, 5, 7, 11] 3 127 true) coreChunks380_66 coreFlatten380_66 coreCheck380_66

theorem finiteCheck346_380 : finiteIntervalCheck 346 380 smallOrder380 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 346) (U := 380) (O := smallOrder380)
    (ps := [3, 5, 7, 11]) resources380 coreSelector380
  · intro i
    fin_cases i
    · exact validResource380_0
    · exact validResource380_1
    · exact validResource380_2
    · exact validResource380_3
    · exact validResource380_4
    · exact validResource380_5
    · exact validResource380_6
    · exact validResource380_7
    · exact validResource380_8
    · exact validResource380_9
    · exact validResource380_10
    · exact validResource380_11
    · exact validResource380_12
    · exact validResource380_13
    · exact validResource380_14
    · exact validResource380_15
    · exact validResource380_16
    · exact validResource380_17
    · exact validResource380_18
    · exact validResource380_19
    · exact validResource380_20
    · exact validResource380_21
    · exact validResource380_22
    · exact validResource380_23
    · exact validResource380_24
    · exact validResource380_25
    · exact validResource380_26
    · exact validResource380_27
    · exact validResource380_28
    · exact validResource380_29
    · exact validResource380_30
    · exact validResource380_31
    · exact validResource380_32
    · exact validResource380_33
    · exact validResource380_34
    · exact validResource380_35
    · exact validResource380_36
    · exact validResource380_37
    · exact validResource380_38
    · exact validResource380_39
    · exact validResource380_40
    · exact validResource380_41
    · exact validResource380_42
    · exact validResource380_43
    · exact validResource380_44
    · exact validResource380_45
    · exact validResource380_46
    · exact validResource380_47
    · exact validResource380_48
    · exact validResource380_49
    · exact validResource380_50
    · exact validResource380_51
    · exact validResource380_52
    · exact validResource380_53
    · exact validResource380_54
    · exact validResource380_55
    · exact validResource380_56
    · exact validResource380_57
    · exact validResource380_58
    · exact validResource380_59
    · exact validResource380_60
    · exact validResource380_61
    · exact validResource380_62
    · exact validResource380_63
    · exact validResource380_64
    · exact validResource380_65
    · exact validResource380_66
  · intro b j
    exact resourceRequirements_of_core (coreRequirements380_0 b j)


theorem exactCertificate346_380 : ExactIntervalCertificate 346 380 smallOrder380 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck346_380
#print axioms smallOrder380_nodup
#print axioms smallOrder380_set
#print axioms finiteCheck346_380
#print axioms exactCertificate346_380
end Erdos883Verified
