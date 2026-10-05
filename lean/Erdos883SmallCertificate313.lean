import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate313Resource000
import Erdos883SmallCertificate313Resource001
import Erdos883SmallCertificate313Resource002
import Erdos883SmallCertificate313Resource003
import Erdos883SmallCertificate313Resource004
import Erdos883SmallCertificate313Resource005
import Erdos883SmallCertificate313Resource006
import Erdos883SmallCertificate313Resource007
import Erdos883SmallCertificate313Resource008
import Erdos883SmallCertificate313Resource009
import Erdos883SmallCertificate313Resource010
import Erdos883SmallCertificate313Resource011
import Erdos883SmallCertificate313Resource012
import Erdos883SmallCertificate313Resource013
import Erdos883SmallCertificate313Resource014
import Erdos883SmallCertificate313Resource015
import Erdos883SmallCertificate313Resource016
import Erdos883SmallCertificate313Resource017
import Erdos883SmallCertificate313Resource018
import Erdos883SmallCertificate313Resource019
import Erdos883SmallCertificate313Resource020
import Erdos883SmallCertificate313Resource021
import Erdos883SmallCertificate313Resource022
import Erdos883SmallCertificate313Resource023
import Erdos883SmallCertificate313Resource024
import Erdos883SmallCertificate313Resource025
import Erdos883SmallCertificate313Resource026
import Erdos883SmallCertificate313Resource027
import Erdos883SmallCertificate313Resource028
import Erdos883SmallCertificate313Resource029
import Erdos883SmallCertificate313Resource030
import Erdos883SmallCertificate313Resource031
import Erdos883SmallCertificate313Resource032
import Erdos883SmallCertificate313Resource033
import Erdos883SmallCertificate313Resource034
import Erdos883SmallCertificate313Resource035
import Erdos883SmallCertificate313Resource036
import Erdos883SmallCertificate313Resource037
import Erdos883SmallCertificate313Resource038
import Erdos883SmallCertificate313Resource039
import Erdos883SmallCertificate313Resource040
import Erdos883SmallCertificate313Resource041
import Erdos883SmallCertificate313Resource042
import Erdos883SmallCertificate313Resource043
import Erdos883SmallCertificate313Resource044
import Erdos883SmallCertificate313Resource045
import Erdos883SmallCertificate313Resource046
import Erdos883SmallCertificate313Resource047
import Erdos883SmallCertificate313Resource048
import Erdos883SmallCertificate313Resource049
import Erdos883SmallCertificate313Resource050
import Erdos883SmallCertificate313Resource051
import Erdos883SmallCertificate313Resource052
import Erdos883SmallCertificate313Resource053
import Erdos883SmallCertificate313Resource054
import Erdos883SmallCertificate313Resource055
import Erdos883SmallCertificate313Resource056
import Erdos883SmallCertificate313Resource057
import Erdos883SmallCertificate313Resource058
import Erdos883SmallCertificate313Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder313 : List ℕ := coreData313.map (·.value)
theorem smallOrder313_nodup : smallOrder313.Nodup := by decide +kernel
theorem smallOrder313_set : smallOrder313.toFinset = oddUniverse 313 := by decide +kernel
private def resources313 (i : Fin 59) : PrefixResourceData := resourceOfCore (coreResources313 i)
private theorem dataValid313 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData313.map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValid313

private theorem validResource313_0 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 0) 0 283
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 285 smallOrder313 [3, 5, 7, 11] 0 283 false) coreChunks313_0 coreFlatten313_0 coreCheck313_0

private theorem validResource313_1 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 1) 32 283
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_0 coreChunks313_1 coreFlatten313_1 coreCheck313_1

private theorem validResource313_2 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 2) 33 282
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_1 coreChunks313_2 coreFlatten313_2 coreCheck313_2

private theorem validResource313_3 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 3) 42 281
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_2 coreChunks313_3 coreFlatten313_3 coreCheck313_3

private theorem validResource313_4 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 4) 43 280
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_3 coreChunks313_4 coreFlatten313_4 coreCheck313_4

private theorem validResource313_5 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 5) 66 229
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_4 coreChunks313_5 coreFlatten313_5 coreCheck313_5

private theorem validResource313_6 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 6) 67 227
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_5 coreChunks313_6 coreFlatten313_6 coreCheck313_6

private theorem validResource313_7 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 7) 68 216
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_6 coreChunks313_7 coreFlatten313_7 coreCheck313_7

private theorem validResource313_8 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 8) 69 215
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_7 coreChunks313_8 coreFlatten313_8 coreCheck313_8

private theorem validResource313_9 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 9) 70 213
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_8 coreChunks313_9 coreFlatten313_9 coreCheck313_9

private theorem validResource313_10 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 10) 72 211
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_9 coreChunks313_10 coreFlatten313_10 coreCheck313_10

private theorem validResource313_11 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 11) 73 210
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_10 coreChunks313_11 coreFlatten313_11 coreCheck313_11

private theorem validResource313_12 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 12) 74 206
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_11 coreChunks313_12 coreFlatten313_12 coreCheck313_12

private theorem validResource313_13 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 13) 77 200
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_12 coreChunks313_13 coreFlatten313_13 coreCheck313_13

private theorem validResource313_14 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 14) 79 198
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_13 coreChunks313_14 coreFlatten313_14 coreCheck313_14

private theorem validResource313_15 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 15) 0 140
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 285 smallOrder313 [3, 5, 7, 11] 0 140 true) coreChunks313_15 coreFlatten313_15 coreCheck313_15

private theorem validResource313_16 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 16) 46 140
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_15 coreChunks313_16 coreFlatten313_16 coreCheck313_16

private theorem validResource313_17 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 17) 47 139
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_16 coreChunks313_17 coreFlatten313_17 coreCheck313_17

private theorem validResource313_18 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 18) 51 138
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_17 coreChunks313_18 coreFlatten313_18 coreCheck313_18

private theorem validResource313_19 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 19) 52 137
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_18 coreChunks313_19 coreFlatten313_19 coreCheck313_19

private theorem validResource313_20 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 20) 55 136
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_19 coreChunks313_20 coreFlatten313_20 coreCheck313_20

private theorem validResource313_21 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 21) 56 135
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_20 coreChunks313_21 coreFlatten313_21 coreCheck313_21

private theorem validResource313_22 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 22) 57 134
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_21 coreChunks313_22 coreFlatten313_22 coreCheck313_22

private theorem validResource313_23 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 23) 58 132
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_22 coreChunks313_23 coreFlatten313_23 coreCheck313_23

private theorem validResource313_24 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 24) 59 129
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_23 coreChunks313_24 coreFlatten313_24 coreCheck313_24

private theorem validResource313_25 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 25) 61 127
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_24 coreChunks313_25 coreFlatten313_25 coreCheck313_25

private theorem validResource313_26 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 26) 63 124
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_25 coreChunks313_26 coreFlatten313_26 coreCheck313_26

private theorem validResource313_27 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 27) 65 120
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_26 coreChunks313_27 coreFlatten313_27 coreCheck313_27

private theorem validResource313_28 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 28) 66 114
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_27 coreChunks313_28 coreFlatten313_28 coreCheck313_28

private theorem validResource313_29 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 29) 67 113
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_28 coreChunks313_29 coreFlatten313_29 coreCheck313_29

private theorem validResource313_30 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 30) 68 107
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_29 coreChunks313_30 coreFlatten313_30 coreCheck313_30

private theorem validResource313_31 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 31) 69 106
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_30 coreChunks313_31 coreFlatten313_31 coreCheck313_31

private theorem validResource313_32 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 32) 72 105
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_31 coreChunks313_32 coreFlatten313_32 coreCheck313_32

private theorem validResource313_33 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 33) 73 104
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_32 coreChunks313_33 coreFlatten313_33 coreCheck313_33

private theorem validResource313_34 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 34) 74 102
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_33 coreChunks313_34 coreFlatten313_34 coreCheck313_34

private theorem validResource313_35 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 35) 77 99
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_34 coreChunks313_35 coreFlatten313_35 coreCheck313_35

private theorem validResource313_36 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 36) 79 98
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_35 coreChunks313_36 coreFlatten313_36 coreCheck313_36

private theorem validResource313_37 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 37) 81 96
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_36 coreChunks313_37 coreFlatten313_37 coreCheck313_37

private theorem validResource313_38 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 38) 82 95
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_37 coreChunks313_38 coreFlatten313_38 coreCheck313_38

private theorem validResource313_39 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 39) 85 92
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_38 coreChunks313_39 coreFlatten313_39 coreCheck313_39

private theorem validResource313_40 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 40) 86 91
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_39 coreChunks313_40 coreFlatten313_40 coreCheck313_40

private theorem validResource313_41 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 41) 89 89
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_40 coreChunks313_41 coreFlatten313_41 coreCheck313_41

private theorem validResource313_42 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 42) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 42) 92 88
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_41 coreChunks313_42 coreFlatten313_42 coreCheck313_42

private theorem validResource313_43 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 43) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 43) 94 86
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_42 coreChunks313_43 coreFlatten313_43 coreCheck313_43

private theorem validResource313_44 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 44) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 44) 96 85
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_43 coreChunks313_44 coreFlatten313_44 coreCheck313_44

private theorem validResource313_45 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 45) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 45) 98 84
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_44 coreChunks313_45 coreFlatten313_45 coreCheck313_45

private theorem validResource313_46 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 46) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 46) 99 83
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_45 coreChunks313_46 coreFlatten313_46 coreCheck313_46

private theorem validResource313_47 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 47) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 47) 105 82
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_46 coreChunks313_47 coreFlatten313_47 coreCheck313_47

private theorem validResource313_48 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 48) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 48) 110 65
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_47 coreChunks313_48 coreFlatten313_48 coreCheck313_48

private theorem validResource313_49 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 49) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 49) 117 64
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_48 coreChunks313_49 coreFlatten313_49 coreCheck313_49

private theorem validResource313_50 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 50) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 50) 126 63
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_49 coreChunks313_50 coreFlatten313_50 coreCheck313_50

private theorem validResource313_51 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 51) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 51) 134 62
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_50 coreChunks313_51 coreFlatten313_51 coreCheck313_51

private theorem validResource313_52 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 52) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 52) 138 61
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_51 coreChunks313_52 coreFlatten313_52 coreCheck313_52

private theorem validResource313_53 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 53) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 53) 150 60
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_52 coreChunks313_53 coreFlatten313_53 coreCheck313_53

private theorem validResource313_54 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 54) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 54) 0 82
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 285 smallOrder313 [3, 5, 7, 11] 1 82 true) coreChunks313_54 coreFlatten313_54 coreCheck313_54

private theorem validResource313_55 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 55) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 55) 0 95
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 285 smallOrder313 [3, 5, 7, 11] 2 95 true) coreChunks313_55 coreFlatten313_55 coreCheck313_55

private theorem validResource313_56 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 56) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 56) 102 95
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource313_55 coreChunks313_56 coreFlatten313_56 coreCheck313_56

private theorem validResource313_57 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 57) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 57) 0 213
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 285 smallOrder313 [3, 5, 7, 11] 3 213 false) coreChunks313_57 coreFlatten313_57 coreCheck313_57

private theorem validResource313_58 :
    PrefixResourceValid 285 smallOrder313 [3, 5, 7, 11] (resources313 58) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 285) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) (r := coreResources313 58) 0 105
    dataValid313 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 285 smallOrder313 [3, 5, 7, 11] 3 105 true) coreChunks313_58 coreFlatten313_58 coreCheck313_58

theorem finiteCheck285_313 : finiteIntervalCheck 285 313 smallOrder313 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 285) (U := 313) (O := smallOrder313)
    (ps := [3, 5, 7, 11]) resources313 coreSelector313
  · intro i
    fin_cases i
    · exact validResource313_0
    · exact validResource313_1
    · exact validResource313_2
    · exact validResource313_3
    · exact validResource313_4
    · exact validResource313_5
    · exact validResource313_6
    · exact validResource313_7
    · exact validResource313_8
    · exact validResource313_9
    · exact validResource313_10
    · exact validResource313_11
    · exact validResource313_12
    · exact validResource313_13
    · exact validResource313_14
    · exact validResource313_15
    · exact validResource313_16
    · exact validResource313_17
    · exact validResource313_18
    · exact validResource313_19
    · exact validResource313_20
    · exact validResource313_21
    · exact validResource313_22
    · exact validResource313_23
    · exact validResource313_24
    · exact validResource313_25
    · exact validResource313_26
    · exact validResource313_27
    · exact validResource313_28
    · exact validResource313_29
    · exact validResource313_30
    · exact validResource313_31
    · exact validResource313_32
    · exact validResource313_33
    · exact validResource313_34
    · exact validResource313_35
    · exact validResource313_36
    · exact validResource313_37
    · exact validResource313_38
    · exact validResource313_39
    · exact validResource313_40
    · exact validResource313_41
    · exact validResource313_42
    · exact validResource313_43
    · exact validResource313_44
    · exact validResource313_45
    · exact validResource313_46
    · exact validResource313_47
    · exact validResource313_48
    · exact validResource313_49
    · exact validResource313_50
    · exact validResource313_51
    · exact validResource313_52
    · exact validResource313_53
    · exact validResource313_54
    · exact validResource313_55
    · exact validResource313_56
    · exact validResource313_57
    · exact validResource313_58
  · intro b j
    exact resourceRequirements_of_core (coreRequirements313 b j)

theorem exactCertificate285_313 : ExactIntervalCertificate 285 313 smallOrder313 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck285_313
#print axioms smallOrder313_nodup
#print axioms smallOrder313_set
#print axioms finiteCheck285_313
#print axioms exactCertificate285_313
end Erdos883Verified
