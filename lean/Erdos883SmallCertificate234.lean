import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate234Resource000
import Erdos883SmallCertificate234Resource001
import Erdos883SmallCertificate234Resource002
import Erdos883SmallCertificate234Resource003
import Erdos883SmallCertificate234Resource004
import Erdos883SmallCertificate234Resource005
import Erdos883SmallCertificate234Resource006
import Erdos883SmallCertificate234Resource007
import Erdos883SmallCertificate234Resource008
import Erdos883SmallCertificate234Resource009
import Erdos883SmallCertificate234Resource010
import Erdos883SmallCertificate234Resource011
import Erdos883SmallCertificate234Resource012
import Erdos883SmallCertificate234Resource013
import Erdos883SmallCertificate234Resource014
import Erdos883SmallCertificate234Resource015
import Erdos883SmallCertificate234Resource016
import Erdos883SmallCertificate234Resource017
import Erdos883SmallCertificate234Resource018
import Erdos883SmallCertificate234Resource019
import Erdos883SmallCertificate234Resource020
import Erdos883SmallCertificate234Resource021
import Erdos883SmallCertificate234Resource022
import Erdos883SmallCertificate234Resource023
import Erdos883SmallCertificate234Resource024
import Erdos883SmallCertificate234Resource025
import Erdos883SmallCertificate234Resource026
import Erdos883SmallCertificate234Resource027
import Erdos883SmallCertificate234Resource028
import Erdos883SmallCertificate234Resource029
import Erdos883SmallCertificate234Resource030
import Erdos883SmallCertificate234Resource031
import Erdos883SmallCertificate234Resource032
import Erdos883SmallCertificate234Resource033
import Erdos883SmallCertificate234Resource034
import Erdos883SmallCertificate234Resource035
import Erdos883SmallCertificate234Resource036
import Erdos883SmallCertificate234Resource037
import Erdos883SmallCertificate234Resource038
import Erdos883SmallCertificate234Resource039
import Erdos883SmallCertificate234Resource040
import Erdos883SmallCertificate234Resource041
import Erdos883SmallCertificate234Resource042
import Erdos883SmallCertificate234Resource043
import Erdos883SmallCertificate234Resource044
import Erdos883SmallCertificate234Resource045
import Erdos883SmallCertificate234Resource046
import Erdos883SmallCertificate234Resource047
import Erdos883SmallCertificate234Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder234 : List ℕ := coreData234.map (·.value)
theorem smallOrder234_nodup : smallOrder234.Nodup := by decide +kernel
theorem smallOrder234_set : smallOrder234.toFinset = oddUniverse 234 := by decide +kernel
private def resources234 (i : Fin 48) : PrefixResourceData := resourceOfCore (coreResources234 i)
private theorem dataValid234 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData234.map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValid234

private theorem validResource234_0 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 0) 0 211
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 213 smallOrder234 [3, 5, 7, 11] 0 211 false) coreChunks234_0 coreFlatten234_0 coreCheck234_0

private theorem validResource234_1 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 1) 25 211
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_0 coreChunks234_1 coreFlatten234_1 coreCheck234_1

private theorem validResource234_2 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 2) 26 210
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_1 coreChunks234_2 coreFlatten234_2 coreCheck234_2

private theorem validResource234_3 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 3) 32 209
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_2 coreChunks234_3 coreFlatten234_3 coreCheck234_3

private theorem validResource234_4 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 4) 51 168
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_3 coreChunks234_4 coreFlatten234_4 coreCheck234_4

private theorem validResource234_5 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 5) 52 158
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_4 coreChunks234_5 coreFlatten234_5 coreCheck234_5

private theorem validResource234_6 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 6) 54 157
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_5 coreChunks234_6 coreFlatten234_6 coreCheck234_6

private theorem validResource234_7 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 7) 55 156
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_6 coreChunks234_7 coreFlatten234_7 coreCheck234_7

private theorem validResource234_8 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 8) 56 153
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_7 coreChunks234_8 coreFlatten234_8 coreCheck234_8

private theorem validResource234_9 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 9) 58 147
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_8 coreChunks234_9 coreFlatten234_9 coreCheck234_9

private theorem validResource234_10 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 10) 0 104
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 213 smallOrder234 [3, 5, 7, 11] 0 104 true) coreChunks234_10 coreFlatten234_10 coreCheck234_10

private theorem validResource234_11 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 11) 36 104
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_10 coreChunks234_11 coreFlatten234_11 coreCheck234_11

private theorem validResource234_12 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 12) 37 103
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_11 coreChunks234_12 coreFlatten234_12 coreCheck234_12

private theorem validResource234_13 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 13) 41 102
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_12 coreChunks234_13 coreFlatten234_13 coreCheck234_13

private theorem validResource234_14 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 14) 42 101
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_13 coreChunks234_14 coreFlatten234_14 coreCheck234_14

private theorem validResource234_15 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 15) 43 100
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_14 coreChunks234_15 coreFlatten234_15 coreCheck234_15

private theorem validResource234_16 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 16) 44 99
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_15 coreChunks234_16 coreFlatten234_16 coreCheck234_16

private theorem validResource234_17 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 17) 45 97
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_16 coreChunks234_17 coreFlatten234_17 coreCheck234_17

private theorem validResource234_18 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 18) 46 95
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_17 coreChunks234_18 coreFlatten234_18 coreCheck234_18

private theorem validResource234_19 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 19) 48 92
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_18 coreChunks234_19 coreFlatten234_19 coreCheck234_19

private theorem validResource234_20 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 20) 50 89
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_19 coreChunks234_20 coreFlatten234_20 coreCheck234_20

private theorem validResource234_21 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 21) 51 83
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_20 coreChunks234_21 coreFlatten234_21 coreCheck234_21

private theorem validResource234_22 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 22) 54 78
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_21 coreChunks234_22 coreFlatten234_22 coreCheck234_22

private theorem validResource234_23 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 23) 55 77
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_22 coreChunks234_23 coreFlatten234_23 coreCheck234_23

private theorem validResource234_24 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 24) 56 76
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_23 coreChunks234_24 coreFlatten234_24 coreCheck234_24

private theorem validResource234_25 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 25) 58 73
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_24 coreChunks234_25 coreFlatten234_25 coreCheck234_25

private theorem validResource234_26 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 26) 59 72
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_25 coreChunks234_26 coreFlatten234_26 coreCheck234_26

private theorem validResource234_27 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 27) 60 71
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_26 coreChunks234_27 coreFlatten234_27 coreCheck234_27

private theorem validResource234_28 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 28) 61 70
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_27 coreChunks234_28 coreFlatten234_28 coreCheck234_28

private theorem validResource234_29 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 29) 64 68
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_28 coreChunks234_29 coreFlatten234_29 coreCheck234_29

private theorem validResource234_30 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 30) 65 67
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_29 coreChunks234_30 coreFlatten234_30 coreCheck234_30

private theorem validResource234_31 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 31) 67 65
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_30 coreChunks234_31 coreFlatten234_31 coreCheck234_31

private theorem validResource234_32 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 32) 69 64
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_31 coreChunks234_32 coreFlatten234_32 coreCheck234_32

private theorem validResource234_33 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 33) 71 63
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_32 coreChunks234_33 coreFlatten234_33 coreCheck234_33

private theorem validResource234_34 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 34) 73 62
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_33 coreChunks234_34 coreFlatten234_34 coreCheck234_34

private theorem validResource234_35 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 35) 74 61
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_34 coreChunks234_35 coreFlatten234_35 coreCheck234_35

private theorem validResource234_36 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 36) 78 60
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_35 coreChunks234_36 coreFlatten234_36 coreCheck234_36

private theorem validResource234_37 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 37) 82 49
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_36 coreChunks234_37 coreFlatten234_37 coreCheck234_37

private theorem validResource234_38 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 38) 87 48
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_37 coreChunks234_38 coreFlatten234_38 coreCheck234_38

private theorem validResource234_39 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 39) 94 47
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_38 coreChunks234_39 coreFlatten234_39 coreCheck234_39

private theorem validResource234_40 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 40) 100 46
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_39 coreChunks234_40 coreFlatten234_40 coreCheck234_40

private theorem validResource234_41 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 41) 113 45
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_40 coreChunks234_41 coreFlatten234_41 coreCheck234_41

private theorem validResource234_42 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 42) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 42) 0 60
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 213 smallOrder234 [3, 5, 7, 11] 1 60 true) coreChunks234_42 coreFlatten234_42 coreCheck234_42

private theorem validResource234_43 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 43) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 43) 0 70
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 213 smallOrder234 [3, 5, 7, 11] 2 70 true) coreChunks234_43 coreFlatten234_43 coreCheck234_43

private theorem validResource234_44 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 44) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 44) 76 70
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_43 coreChunks234_44 coreFlatten234_44 coreCheck234_44

private theorem validResource234_45 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 45) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 45) 0 158
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 213 smallOrder234 [3, 5, 7, 11] 3 158 false) coreChunks234_45 coreFlatten234_45 coreCheck234_45

private theorem validResource234_46 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 46) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 46) 0 78
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 213 smallOrder234 [3, 5, 7, 11] 3 78 true) coreChunks234_46 coreFlatten234_46 coreCheck234_46

private theorem validResource234_47 :
    PrefixResourceValid 213 smallOrder234 [3, 5, 7, 11] (resources234 47) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 213) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) (r := coreResources234 47) 67 78
    dataValid234 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource234_46 coreChunks234_47 coreFlatten234_47 coreCheck234_47

theorem finiteCheck213_234 : finiteIntervalCheck 213 234 smallOrder234 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 213) (U := 234) (O := smallOrder234)
    (ps := [3, 5, 7, 11]) resources234 coreSelector234
  · intro i
    fin_cases i
    · exact validResource234_0
    · exact validResource234_1
    · exact validResource234_2
    · exact validResource234_3
    · exact validResource234_4
    · exact validResource234_5
    · exact validResource234_6
    · exact validResource234_7
    · exact validResource234_8
    · exact validResource234_9
    · exact validResource234_10
    · exact validResource234_11
    · exact validResource234_12
    · exact validResource234_13
    · exact validResource234_14
    · exact validResource234_15
    · exact validResource234_16
    · exact validResource234_17
    · exact validResource234_18
    · exact validResource234_19
    · exact validResource234_20
    · exact validResource234_21
    · exact validResource234_22
    · exact validResource234_23
    · exact validResource234_24
    · exact validResource234_25
    · exact validResource234_26
    · exact validResource234_27
    · exact validResource234_28
    · exact validResource234_29
    · exact validResource234_30
    · exact validResource234_31
    · exact validResource234_32
    · exact validResource234_33
    · exact validResource234_34
    · exact validResource234_35
    · exact validResource234_36
    · exact validResource234_37
    · exact validResource234_38
    · exact validResource234_39
    · exact validResource234_40
    · exact validResource234_41
    · exact validResource234_42
    · exact validResource234_43
    · exact validResource234_44
    · exact validResource234_45
    · exact validResource234_46
    · exact validResource234_47
  · intro b j
    exact resourceRequirements_of_core (coreRequirements234 b j)

theorem exactCertificate213_234 : ExactIntervalCertificate 213 234 smallOrder234 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck213_234
#print axioms smallOrder234_nodup
#print axioms smallOrder234_set
#print axioms finiteCheck213_234
#print axioms exactCertificate213_234
end Erdos883Verified
