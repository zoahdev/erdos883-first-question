import Erdos883SmallCertificate1100Data
import Erdos883SmallCertificate1100Resource194Chunk000
import Erdos883SmallCertificate1100Resource194Chunk001
import Erdos883SmallCertificate1100Resource194Chunk002
import Erdos883SmallCertificate1100Resource194Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_194 :
    (List.ofFn coreChunks1100_194).flatten =
      (coreData1100.take (coreResources1100 194).q).drop 488 := by
  decide +kernel

theorem coreCheck1100_194 :
    ∀ c : Fin 4, (coreChunks1100_194 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 194)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_194_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_194_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_194_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_194_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1100_194
#print axioms coreCheck1100_194
end Erdos883Verified
