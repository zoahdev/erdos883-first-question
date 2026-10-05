import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate83OrderCheck
import Erdos883SmallCertificate83Metadata000
import Erdos883SmallCertificate83Resource000
import Erdos883SmallCertificate83Resource001
import Erdos883SmallCertificate83Resource002
import Erdos883SmallCertificate83Resource003
import Erdos883SmallCertificate83Resource004
import Erdos883SmallCertificate83Resource005
import Erdos883SmallCertificate83Resource006
import Erdos883SmallCertificate83Resource007
import Erdos883SmallCertificate83Resource008
import Erdos883SmallCertificate83Resource009
import Erdos883SmallCertificate83Resource010
import Erdos883SmallCertificate83Resource011
import Erdos883SmallCertificate83Resource012
import Erdos883SmallCertificate83Resource013
import Erdos883SmallCertificate83Resource014
import Erdos883SmallCertificate83Resource015
import Erdos883SmallCertificate83Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder83 : List ℕ := coreData83.map (·.value)
theorem smallOrder83_nodup : smallOrder83.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck83).1
theorem smallOrder83_set : smallOrder83.toFinset = oddUniverse 83 := (coreOrderPermutationCheck_sound coreOrderCheck83).2
private def resources83 (i : Fin 16) : PrefixResourceData := resourceOfCore (coreResources83 i)
private theorem dataValid83 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData83.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks83 coreMetadataFlatten83
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck83_0
#print axioms dataValid83

private theorem validResource83_0 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 0) 0 74
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 76 smallOrder83 [3, 5, 7, 11] 0 74 false) coreChunks83_0 coreFlatten83_0 coreCheck83_0

private theorem validResource83_1 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 1) 0 38
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 76 smallOrder83 [3, 5, 7, 11] 0 38 true) coreChunks83_1 coreFlatten83_1 coreCheck83_1

private theorem validResource83_2 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 2) 12 38
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_1 coreChunks83_2 coreFlatten83_2 coreCheck83_2

private theorem validResource83_3 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 3) 13 37
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_2 coreChunks83_3 coreFlatten83_3 coreCheck83_3

private theorem validResource83_4 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 4) 16 36
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_3 coreChunks83_4 coreFlatten83_4 coreCheck83_4

private theorem validResource83_5 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 5) 17 35
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_4 coreChunks83_5 coreFlatten83_5 coreCheck83_5

private theorem validResource83_6 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 6) 19 34
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_5 coreChunks83_6 coreFlatten83_6 coreCheck83_6

private theorem validResource83_7 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 7) 20 33
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_6 coreChunks83_7 coreFlatten83_7 coreCheck83_7

private theorem validResource83_8 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 8) 22 30
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_7 coreChunks83_8 coreFlatten83_8 coreCheck83_8

private theorem validResource83_9 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 9) 24 27
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_8 coreChunks83_9 coreFlatten83_9 coreCheck83_9

private theorem validResource83_10 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 10) 25 24
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_9 coreChunks83_10 coreFlatten83_10 coreCheck83_10

private theorem validResource83_11 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 11) 28 22
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_10 coreChunks83_11 coreFlatten83_11 coreCheck83_11

private theorem validResource83_12 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 12) 32 18
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_11 coreChunks83_12 coreFlatten83_12 coreCheck83_12

private theorem validResource83_13 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 13) 33 17
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource83_12 coreChunks83_13 coreFlatten83_13 coreCheck83_13

private theorem validResource83_14 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 14) 0 22
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 76 smallOrder83 [3, 5, 7, 11] 1 22 true) coreChunks83_14 coreFlatten83_14 coreCheck83_14

private theorem validResource83_15 :
    PrefixResourceValid 76 smallOrder83 [3, 5, 7, 11] (resources83 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 76) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) (r := coreResources83 15) 0 24
    dataValid83 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 76 smallOrder83 [3, 5, 7, 11] 2 24 true) coreChunks83_15 coreFlatten83_15 coreCheck83_15

theorem finiteCheck76_83 : finiteIntervalCheck 76 83 smallOrder83 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 76) (U := 83) (O := smallOrder83)
    (ps := [3, 5, 7, 11]) resources83 coreSelector83
  · intro i
    fin_cases i
    · exact validResource83_0
    · exact validResource83_1
    · exact validResource83_2
    · exact validResource83_3
    · exact validResource83_4
    · exact validResource83_5
    · exact validResource83_6
    · exact validResource83_7
    · exact validResource83_8
    · exact validResource83_9
    · exact validResource83_10
    · exact validResource83_11
    · exact validResource83_12
    · exact validResource83_13
    · exact validResource83_14
    · exact validResource83_15
  · intro b j
    exact resourceRequirements_of_core (coreRequirements83_0 b j)


theorem exactCertificate76_83 : ExactIntervalCertificate 76 83 smallOrder83 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck76_83
#print axioms smallOrder83_nodup
#print axioms smallOrder83_set
#print axioms finiteCheck76_83
#print axioms exactCertificate76_83
end Erdos883Verified
