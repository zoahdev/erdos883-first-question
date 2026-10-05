import Erdos883SmallCertificate1100Data
import Erdos883SmallCertificate1100Resource000Chunk000
import Erdos883SmallCertificate1100Resource000Chunk001
import Erdos883SmallCertificate1100Resource000Chunk002
import Erdos883SmallCertificate1100Resource000Chunk003
import Erdos883SmallCertificate1100Resource000Chunk004
import Erdos883SmallCertificate1100Resource000Chunk005
import Erdos883SmallCertificate1100Resource000Chunk006
import Erdos883SmallCertificate1100Resource000Chunk007
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_0 :
    (List.ofFn coreChunks1100_0).flatten =
      (coreData1100.take (coreResources1100 0).q).drop 0 := by
  decide +kernel

theorem coreCheck1100_0 :
    ∀ c : Fin 8, (coreChunks1100_0 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_0_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_0_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_0_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_0_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_0_7, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1100_0
#print axioms coreCheck1100_0
end Erdos883Verified
