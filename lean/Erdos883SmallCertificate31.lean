import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate31OrderCheck
import Erdos883SmallCertificate31Metadata000
import Erdos883SmallCertificate31Resource000
import Erdos883SmallCertificate31Resource001
import Erdos883SmallCertificate31Resource002
import Erdos883SmallCertificate31Resource003
import Erdos883SmallCertificate31Resource004
import Erdos883SmallCertificate31Resource005
import Erdos883SmallCertificate31Resource006
import Erdos883SmallCertificate31Resource007
import Erdos883SmallCertificate31Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder31 : List ℕ := coreData31.map (·.value)
theorem smallOrder31_nodup : smallOrder31.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck31).1
theorem smallOrder31_set : smallOrder31.toFinset = oddUniverse 31 := (coreOrderPermutationCheck_sound coreOrderCheck31).2
private def resources31 (i : Fin 8) : PrefixResourceData := resourceOfCore (coreResources31 i)
private theorem dataValid31 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData31.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks31 coreMetadataFlatten31
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck31_0
#print axioms dataValid31

private theorem validResource31_0 :
    PrefixResourceValid 29 smallOrder31 [3, 5, 7, 11] (resources31 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 29) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) (r := coreResources31 0) 0 27
    dataValid31 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 29 smallOrder31 [3, 5, 7, 11] 0 27 false) coreChunks31_0 coreFlatten31_0 coreCheck31_0

private theorem validResource31_1 :
    PrefixResourceValid 29 smallOrder31 [3, 5, 7, 11] (resources31 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 29) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) (r := coreResources31 1) 0 14
    dataValid31 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 29 smallOrder31 [3, 5, 7, 11] 0 14 true) coreChunks31_1 coreFlatten31_1 coreCheck31_1

private theorem validResource31_2 :
    PrefixResourceValid 29 smallOrder31 [3, 5, 7, 11] (resources31 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 29) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) (r := coreResources31 2) 6 14
    dataValid31 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource31_1 coreChunks31_2 coreFlatten31_2 coreCheck31_2

private theorem validResource31_3 :
    PrefixResourceValid 29 smallOrder31 [3, 5, 7, 11] (resources31 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 29) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) (r := coreResources31 3) 7 13
    dataValid31 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource31_2 coreChunks31_3 coreFlatten31_3 coreCheck31_3

private theorem validResource31_4 :
    PrefixResourceValid 29 smallOrder31 [3, 5, 7, 11] (resources31 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 29) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) (r := coreResources31 4) 8 12
    dataValid31 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource31_3 coreChunks31_4 coreFlatten31_4 coreCheck31_4

private theorem validResource31_5 :
    PrefixResourceValid 29 smallOrder31 [3, 5, 7, 11] (resources31 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 29) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) (r := coreResources31 5) 9 11
    dataValid31 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource31_4 coreChunks31_5 coreFlatten31_5 coreCheck31_5

private theorem validResource31_6 :
    PrefixResourceValid 29 smallOrder31 [3, 5, 7, 11] (resources31 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 29) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) (r := coreResources31 6) 11 10
    dataValid31 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource31_5 coreChunks31_6 coreFlatten31_6 coreCheck31_6

private theorem validResource31_7 :
    PrefixResourceValid 29 smallOrder31 [3, 5, 7, 11] (resources31 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 29) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) (r := coreResources31 7) 14 8
    dataValid31 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource31_6 coreChunks31_7 coreFlatten31_7 coreCheck31_7

theorem finiteCheck29_31 : finiteIntervalCheck 29 31 smallOrder31 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 29) (U := 31) (O := smallOrder31)
    (ps := [3, 5, 7, 11]) resources31 coreSelector31
  · intro i
    fin_cases i
    · exact validResource31_0
    · exact validResource31_1
    · exact validResource31_2
    · exact validResource31_3
    · exact validResource31_4
    · exact validResource31_5
    · exact validResource31_6
    · exact validResource31_7
  · intro b j
    exact resourceRequirements_of_core (coreRequirements31_0 b j)


theorem exactCertificate29_31 : ExactIntervalCertificate 29 31 smallOrder31 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck29_31
#print axioms smallOrder31_nodup
#print axioms smallOrder31_set
#print axioms finiteCheck29_31
#print axioms exactCertificate29_31
end Erdos883Verified
