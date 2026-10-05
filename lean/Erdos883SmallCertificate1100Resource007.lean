import Erdos883SmallCertificate1100Data
import Erdos883SmallCertificate1100Resource007Chunk000
import Erdos883SmallCertificate1100Resource007Chunk001
import Erdos883SmallCertificate1100Resource007Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_7 :
    (List.ofFn coreChunks1100_7).flatten =
      (coreData1100.take (coreResources1100 7).q).drop 145 := by
  decide +kernel

theorem coreCheck1100_7 :
    ∀ c : Fin 3, (coreChunks1100_7 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 7)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_7_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_7_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_7_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten1100_7
#print axioms coreCheck1100_7
end Erdos883Verified
