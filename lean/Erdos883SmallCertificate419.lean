import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate419Resource000
import Erdos883SmallCertificate419Resource001
import Erdos883SmallCertificate419Resource002
import Erdos883SmallCertificate419Resource003
import Erdos883SmallCertificate419Resource004
import Erdos883SmallCertificate419Resource005
import Erdos883SmallCertificate419Resource006
import Erdos883SmallCertificate419Resource007
import Erdos883SmallCertificate419Resource008
import Erdos883SmallCertificate419Resource009
import Erdos883SmallCertificate419Resource010
import Erdos883SmallCertificate419Resource011
import Erdos883SmallCertificate419Resource012
import Erdos883SmallCertificate419Resource013
import Erdos883SmallCertificate419Resource014
import Erdos883SmallCertificate419Resource015
import Erdos883SmallCertificate419Resource016
import Erdos883SmallCertificate419Resource017
import Erdos883SmallCertificate419Resource018
import Erdos883SmallCertificate419Resource019
import Erdos883SmallCertificate419Resource020
import Erdos883SmallCertificate419Resource021
import Erdos883SmallCertificate419Resource022
import Erdos883SmallCertificate419Resource023
import Erdos883SmallCertificate419Resource024
import Erdos883SmallCertificate419Resource025
import Erdos883SmallCertificate419Resource026
import Erdos883SmallCertificate419Resource027
import Erdos883SmallCertificate419Resource028
import Erdos883SmallCertificate419Resource029
import Erdos883SmallCertificate419Resource030
import Erdos883SmallCertificate419Resource031
import Erdos883SmallCertificate419Resource032
import Erdos883SmallCertificate419Resource033
import Erdos883SmallCertificate419Resource034
import Erdos883SmallCertificate419Resource035
import Erdos883SmallCertificate419Resource036
import Erdos883SmallCertificate419Resource037
import Erdos883SmallCertificate419Resource038
import Erdos883SmallCertificate419Resource039
import Erdos883SmallCertificate419Resource040
import Erdos883SmallCertificate419Resource041
import Erdos883SmallCertificate419Resource042
import Erdos883SmallCertificate419Resource043
import Erdos883SmallCertificate419Resource044
import Erdos883SmallCertificate419Resource045
import Erdos883SmallCertificate419Resource046
import Erdos883SmallCertificate419Resource047
import Erdos883SmallCertificate419Resource048
import Erdos883SmallCertificate419Resource049
import Erdos883SmallCertificate419Resource050
import Erdos883SmallCertificate419Resource051
import Erdos883SmallCertificate419Resource052
import Erdos883SmallCertificate419Resource053
import Erdos883SmallCertificate419Resource054
import Erdos883SmallCertificate419Resource055
import Erdos883SmallCertificate419Resource056
import Erdos883SmallCertificate419Resource057
import Erdos883SmallCertificate419Resource058
import Erdos883SmallCertificate419Resource059
import Erdos883SmallCertificate419Resource060
import Erdos883SmallCertificate419Resource061
import Erdos883SmallCertificate419Resource062
import Erdos883SmallCertificate419Resource063
import Erdos883SmallCertificate419Resource064
import Erdos883SmallCertificate419Resource065
import Erdos883SmallCertificate419Resource066
import Erdos883SmallCertificate419Resource067
import Erdos883SmallCertificate419Resource068
import Erdos883SmallCertificate419Resource069
import Erdos883SmallCertificate419Resource070
import Erdos883SmallCertificate419Resource071
import Erdos883SmallCertificate419Resource072
import Erdos883SmallCertificate419Resource073
import Erdos883SmallCertificate419Resource074
import Erdos883SmallCertificate419Resource075
import Erdos883SmallCertificate419Resource076
import Erdos883SmallCertificate419Resource077
import Erdos883SmallCertificate419Resource078
import Erdos883SmallCertificate419Resource079
import Erdos883SmallCertificate419Requirements000
import Erdos883SmallCertificate419Requirements001
import Erdos883SmallCertificate419Requirements002
import Erdos883SmallCertificate419Requirements003
import Erdos883SmallCertificate419Requirements004
import Erdos883SmallCertificate419Requirements005
import Erdos883SmallCertificate419Requirements006
import Erdos883SmallCertificate419Requirements007
import Erdos883SmallCertificate419Requirements008
import Erdos883SmallCertificate419Requirements009
import Erdos883SmallCertificate419Requirements010
import Erdos883SmallCertificate419Requirements011
import Erdos883SmallCertificate419Requirements012
import Erdos883SmallCertificate419Requirements013
import Erdos883SmallCertificate419Requirements014
import Erdos883SmallCertificate419Requirements015
import Erdos883SmallCertificate419Requirements016
import Erdos883SmallCertificate419Requirements017
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder419 : List ℕ := coreData419.map (·.value)
theorem smallOrder419_nodup : smallOrder419.Nodup := by decide +kernel
theorem smallOrder419_set : smallOrder419.toFinset = oddUniverse 419 := by decide +kernel
private def resources419 (i : Fin 80) : PrefixResourceData := resourceOfCore (coreResources419 i)
private theorem dataValid419 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData419.map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValid419

private theorem validResource419_0 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 0) 0 379
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 381 smallOrder419 [3, 5, 7, 11] 0 379 false) coreChunks419_0 coreFlatten419_0 coreCheck419_0

private theorem validResource419_1 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 1) 40 379
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_0 coreChunks419_1 coreFlatten419_1 coreCheck419_1

private theorem validResource419_2 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 2) 41 378
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_1 coreChunks419_2 coreFlatten419_2 coreCheck419_2

private theorem validResource419_3 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 3) 51 377
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_2 coreChunks419_3 coreFlatten419_3 coreCheck419_3

private theorem validResource419_4 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 4) 52 376
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_3 coreChunks419_4 coreFlatten419_4 coreCheck419_4

private theorem validResource419_5 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 5) 56 375
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_4 coreChunks419_5 coreFlatten419_5 coreCheck419_5

private theorem validResource419_6 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 6) 79 331
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_5 coreChunks419_6 coreFlatten419_6 coreCheck419_6

private theorem validResource419_7 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 7) 82 320
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_6 coreChunks419_7 coreFlatten419_7 coreCheck419_7

private theorem validResource419_8 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 8) 83 312
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_7 coreChunks419_8 coreFlatten419_8 coreCheck419_8

private theorem validResource419_9 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 9) 84 304
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_8 coreChunks419_9 coreFlatten419_9 coreCheck419_9

private theorem validResource419_10 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 10) 86 301
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_9 coreChunks419_10 coreFlatten419_10 coreCheck419_10

private theorem validResource419_11 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 11) 87 299
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_10 coreChunks419_11 coreFlatten419_11 coreCheck419_11

private theorem validResource419_12 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 12) 88 296
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_11 coreChunks419_12 coreFlatten419_12 coreCheck419_12

private theorem validResource419_13 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 13) 90 295
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_12 coreChunks419_13 coreFlatten419_13 coreCheck419_13

private theorem validResource419_14 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 14) 91 291
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_13 coreChunks419_14 coreFlatten419_14 coreCheck419_14

private theorem validResource419_15 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 15) 92 288
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_14 coreChunks419_15 coreFlatten419_15 coreCheck419_15

private theorem validResource419_16 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 16) 93 287
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_15 coreChunks419_16 coreFlatten419_16 coreCheck419_16

private theorem validResource419_17 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 17) 94 284
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_16 coreChunks419_17 coreFlatten419_17 coreCheck419_17

private theorem validResource419_18 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 18) 98 280
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_17 coreChunks419_18 coreFlatten419_18 coreCheck419_18

private theorem validResource419_19 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 19) 100 274
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_18 coreChunks419_19 coreFlatten419_19 coreCheck419_19

private theorem validResource419_20 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 20) 101 268
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_19 coreChunks419_20 coreFlatten419_20 coreCheck419_20

private theorem validResource419_21 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 21) 103 267
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_20 coreChunks419_21 coreFlatten419_21 coreCheck419_21

private theorem validResource419_22 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 22) 104 266
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_21 coreChunks419_22 coreFlatten419_22 coreCheck419_22

private theorem validResource419_23 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 23) 105 265
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_22 coreChunks419_23 coreFlatten419_23 coreCheck419_23

private theorem validResource419_24 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 24) 0 188
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 381 smallOrder419 [3, 5, 7, 11] 0 188 true) coreChunks419_24 coreFlatten419_24 coreCheck419_24

private theorem validResource419_25 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 25) 58 188
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_24 coreChunks419_25 coreFlatten419_25 coreCheck419_25

private theorem validResource419_26 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 26) 59 187
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_25 coreChunks419_26 coreFlatten419_26 coreCheck419_26

private theorem validResource419_27 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 27) 64 186
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_26 coreChunks419_27 coreFlatten419_27 coreCheck419_27

private theorem validResource419_28 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 28) 65 185
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_27 coreChunks419_28 coreFlatten419_28 coreCheck419_28

private theorem validResource419_29 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 29) 67 184
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_28 coreChunks419_29 coreFlatten419_29 coreCheck419_29

private theorem validResource419_30 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 30) 68 183
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_29 coreChunks419_30 coreFlatten419_30 coreCheck419_30

private theorem validResource419_31 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 31) 70 182
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_30 coreChunks419_31 coreFlatten419_31 coreCheck419_31

private theorem validResource419_32 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 32) 71 181
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_31 coreChunks419_32 coreFlatten419_32 coreCheck419_32

private theorem validResource419_33 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 33) 72 179
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_32 coreChunks419_33 coreFlatten419_33 coreCheck419_33

private theorem validResource419_34 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 34) 73 178
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_33 coreChunks419_34 coreFlatten419_34 coreCheck419_34

private theorem validResource419_35 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 35) 74 176
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_34 coreChunks419_35 coreFlatten419_35 coreCheck419_35

private theorem validResource419_36 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 36) 76 172
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_35 coreChunks419_36 coreFlatten419_36 coreCheck419_36

private theorem validResource419_37 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 37) 78 169
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_36 coreChunks419_37 coreFlatten419_37 coreCheck419_37

private theorem validResource419_38 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 38) 80 165
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_37 coreChunks419_38 coreFlatten419_38 coreCheck419_38

private theorem validResource419_39 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 39) 82 160
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_38 coreChunks419_39 coreFlatten419_39 coreCheck419_39

private theorem validResource419_40 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 40) 83 155
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_39 coreChunks419_40 coreFlatten419_40 coreCheck419_40

private theorem validResource419_41 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 41) 84 151
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_40 coreChunks419_41 coreFlatten419_41 coreCheck419_41

private theorem validResource419_42 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 42) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 42) 86 149
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_41 coreChunks419_42 coreFlatten419_42 coreCheck419_42

private theorem validResource419_43 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 43) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 43) 87 148
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_42 coreChunks419_43 coreFlatten419_43 coreCheck419_43

private theorem validResource419_44 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 44) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 44) 88 147
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_43 coreChunks419_44 coreFlatten419_44 coreCheck419_44

private theorem validResource419_45 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 45) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 45) 90 146
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_44 coreChunks419_45 coreFlatten419_45 coreCheck419_45

private theorem validResource419_46 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 46) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 46) 91 144
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_45 coreChunks419_46 coreFlatten419_46 coreCheck419_46

private theorem validResource419_47 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 47) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 47) 93 142
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_46 coreChunks419_47 coreFlatten419_47 coreCheck419_47

private theorem validResource419_48 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 48) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 48) 94 140
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_47 coreChunks419_48 coreFlatten419_48 coreCheck419_48

private theorem validResource419_49 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 49) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 49) 98 139
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_48 coreChunks419_49 coreFlatten419_49 coreCheck419_49

private theorem validResource419_50 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 50) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 50) 100 136
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_49 coreChunks419_50 coreFlatten419_50 coreCheck419_50

private theorem validResource419_51 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 51) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 51) 101 134
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_50 coreChunks419_51 coreFlatten419_51 coreCheck419_51

private theorem validResource419_52 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 52) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 52) 104 133
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_51 coreChunks419_52 coreFlatten419_52 coreCheck419_52

private theorem validResource419_53 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 53) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 53) 105 132
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_52 coreChunks419_53 coreFlatten419_53 coreCheck419_53

private theorem validResource419_54 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 54) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 54) 107 131
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_53 coreChunks419_54 coreFlatten419_54 coreCheck419_54

private theorem validResource419_55 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 55) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 55) 108 130
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_54 coreChunks419_55 coreFlatten419_55 coreCheck419_55

private theorem validResource419_56 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 56) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 56) 110 128
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_55 coreChunks419_56 coreFlatten419_56 coreCheck419_56

private theorem validResource419_57 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 57) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 57) 113 122
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_56 coreChunks419_57 coreFlatten419_57 coreCheck419_57

private theorem validResource419_58 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 58) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 58) 114 120
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_57 coreChunks419_58 coreFlatten419_58 coreCheck419_58

private theorem validResource419_59 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 59) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 59) 119 118
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_58 coreChunks419_59 coreFlatten419_59 coreCheck419_59

private theorem validResource419_60 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 60) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 60) 122 117
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_59 coreChunks419_60 coreFlatten419_60 coreCheck419_60

private theorem validResource419_61 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 61) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 61) 125 116
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_60 coreChunks419_61 coreFlatten419_61 coreCheck419_61

private theorem validResource419_62 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 62) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 62) 127 114
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_61 coreChunks419_62 coreFlatten419_62 coreCheck419_62

private theorem validResource419_63 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 63) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 63) 129 113
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_62 coreChunks419_63 coreFlatten419_63 coreCheck419_63

private theorem validResource419_64 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 64) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 64) 130 112
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_63 coreChunks419_64 coreFlatten419_64 coreCheck419_64

private theorem validResource419_65 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 65) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 65) 132 111
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_64 coreChunks419_65 coreFlatten419_65 coreCheck419_65

private theorem validResource419_66 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 66) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 66) 139 109
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_65 coreChunks419_66 coreFlatten419_66 coreCheck419_66

private theorem validResource419_67 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 67) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 67) 144 87
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_66 coreChunks419_67 coreFlatten419_67 coreCheck419_67

private theorem validResource419_68 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 68) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 68) 154 86
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_67 coreChunks419_68 coreFlatten419_68 coreCheck419_68

private theorem validResource419_69 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 69) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 69) 163 85
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_68 coreChunks419_69 coreFlatten419_69 coreCheck419_69

private theorem validResource419_70 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 70) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 70) 174 84
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_69 coreChunks419_70 coreFlatten419_70 coreCheck419_70

private theorem validResource419_71 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 71) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 71) 178 83
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_70 coreChunks419_71 coreFlatten419_71 coreCheck419_71

private theorem validResource419_72 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 72) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 72) 180 82
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_71 coreChunks419_72 coreFlatten419_72 coreCheck419_72

private theorem validResource419_73 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 73) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 73) 181 75
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_72 coreChunks419_73 coreFlatten419_73 coreCheck419_73

private theorem validResource419_74 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 74) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 74) 0 109
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 381 smallOrder419 [3, 5, 7, 11] 1 109 true) coreChunks419_74 coreFlatten419_74 coreCheck419_74

private theorem validResource419_75 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 75) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 75) 0 128
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 381 smallOrder419 [3, 5, 7, 11] 2 128 true) coreChunks419_75 coreFlatten419_75 coreCheck419_75

private theorem validResource419_76 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 76) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 76) 134 128
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_75 coreChunks419_76 coreFlatten419_76 coreCheck419_76

private theorem validResource419_77 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 77) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 77) 136 127
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource419_76 coreChunks419_77 coreFlatten419_77 coreCheck419_77

private theorem validResource419_78 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 78) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 78) 0 284
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 381 smallOrder419 [3, 5, 7, 11] 3 284 false) coreChunks419_78 coreFlatten419_78 coreCheck419_78

private theorem validResource419_79 :
    PrefixResourceValid 381 smallOrder419 [3, 5, 7, 11] (resources419 79) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 381) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) (r := coreResources419 79) 0 140
    dataValid419 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 381 smallOrder419 [3, 5, 7, 11] 3 140 true) coreChunks419_79 coreFlatten419_79 coreCheck419_79

theorem finiteCheck381_419 : finiteIntervalCheck 381 419 smallOrder419 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 381) (U := 419) (O := smallOrder419)
    (ps := [3, 5, 7, 11]) resources419 coreSelector419
  · intro i
    fin_cases i
    · exact validResource419_0
    · exact validResource419_1
    · exact validResource419_2
    · exact validResource419_3
    · exact validResource419_4
    · exact validResource419_5
    · exact validResource419_6
    · exact validResource419_7
    · exact validResource419_8
    · exact validResource419_9
    · exact validResource419_10
    · exact validResource419_11
    · exact validResource419_12
    · exact validResource419_13
    · exact validResource419_14
    · exact validResource419_15
    · exact validResource419_16
    · exact validResource419_17
    · exact validResource419_18
    · exact validResource419_19
    · exact validResource419_20
    · exact validResource419_21
    · exact validResource419_22
    · exact validResource419_23
    · exact validResource419_24
    · exact validResource419_25
    · exact validResource419_26
    · exact validResource419_27
    · exact validResource419_28
    · exact validResource419_29
    · exact validResource419_30
    · exact validResource419_31
    · exact validResource419_32
    · exact validResource419_33
    · exact validResource419_34
    · exact validResource419_35
    · exact validResource419_36
    · exact validResource419_37
    · exact validResource419_38
    · exact validResource419_39
    · exact validResource419_40
    · exact validResource419_41
    · exact validResource419_42
    · exact validResource419_43
    · exact validResource419_44
    · exact validResource419_45
    · exact validResource419_46
    · exact validResource419_47
    · exact validResource419_48
    · exact validResource419_49
    · exact validResource419_50
    · exact validResource419_51
    · exact validResource419_52
    · exact validResource419_53
    · exact validResource419_54
    · exact validResource419_55
    · exact validResource419_56
    · exact validResource419_57
    · exact validResource419_58
    · exact validResource419_59
    · exact validResource419_60
    · exact validResource419_61
    · exact validResource419_62
    · exact validResource419_63
    · exact validResource419_64
    · exact validResource419_65
    · exact validResource419_66
    · exact validResource419_67
    · exact validResource419_68
    · exact validResource419_69
    · exact validResource419_70
    · exact validResource419_71
    · exact validResource419_72
    · exact validResource419_73
    · exact validResource419_74
    · exact validResource419_75
    · exact validResource419_76
    · exact validResource419_77
    · exact validResource419_78
    · exact validResource419_79
  · intro b j
    have hb : b.val < 140 := b.isLt
    by_cases h0 : b.val < 8
    · exact resourceRequirements_of_core (coreRequirements419_0 b (by omega) h0 j)
    by_cases h1 : b.val < 16
    · exact resourceRequirements_of_core (coreRequirements419_1 b (by omega) h1 j)
    by_cases h2 : b.val < 24
    · exact resourceRequirements_of_core (coreRequirements419_2 b (by omega) h2 j)
    by_cases h3 : b.val < 32
    · exact resourceRequirements_of_core (coreRequirements419_3 b (by omega) h3 j)
    by_cases h4 : b.val < 40
    · exact resourceRequirements_of_core (coreRequirements419_4 b (by omega) h4 j)
    by_cases h5 : b.val < 48
    · exact resourceRequirements_of_core (coreRequirements419_5 b (by omega) h5 j)
    by_cases h6 : b.val < 56
    · exact resourceRequirements_of_core (coreRequirements419_6 b (by omega) h6 j)
    by_cases h7 : b.val < 64
    · exact resourceRequirements_of_core (coreRequirements419_7 b (by omega) h7 j)
    by_cases h8 : b.val < 72
    · exact resourceRequirements_of_core (coreRequirements419_8 b (by omega) h8 j)
    by_cases h9 : b.val < 80
    · exact resourceRequirements_of_core (coreRequirements419_9 b (by omega) h9 j)
    by_cases h10 : b.val < 88
    · exact resourceRequirements_of_core (coreRequirements419_10 b (by omega) h10 j)
    by_cases h11 : b.val < 96
    · exact resourceRequirements_of_core (coreRequirements419_11 b (by omega) h11 j)
    by_cases h12 : b.val < 104
    · exact resourceRequirements_of_core (coreRequirements419_12 b (by omega) h12 j)
    by_cases h13 : b.val < 112
    · exact resourceRequirements_of_core (coreRequirements419_13 b (by omega) h13 j)
    by_cases h14 : b.val < 120
    · exact resourceRequirements_of_core (coreRequirements419_14 b (by omega) h14 j)
    by_cases h15 : b.val < 128
    · exact resourceRequirements_of_core (coreRequirements419_15 b (by omega) h15 j)
    by_cases h16 : b.val < 136
    · exact resourceRequirements_of_core (coreRequirements419_16 b (by omega) h16 j)
    exact resourceRequirements_of_core (coreRequirements419_17 b (by omega) hb j)


theorem exactCertificate381_419 : ExactIntervalCertificate 381 419 smallOrder419 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck381_419
#print axioms smallOrder419_nodup
#print axioms smallOrder419_set
#print axioms finiteCheck381_419
#print axioms exactCertificate381_419
end Erdos883Verified
