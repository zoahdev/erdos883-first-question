import Erdos883SmallCertificate1211Data
import Erdos883SmallCertificate1211Resource000Chunk000
import Erdos883SmallCertificate1211Resource000Chunk001
import Erdos883SmallCertificate1211Resource000Chunk002
import Erdos883SmallCertificate1211Resource000Chunk003
import Erdos883SmallCertificate1211Resource000Chunk004
import Erdos883SmallCertificate1211Resource000Chunk005
import Erdos883SmallCertificate1211Resource000Chunk006
import Erdos883SmallCertificate1211Resource000Chunk007
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_0 :
    (List.ofFn coreChunks1211_0).flatten =
      (coreData1211.take (coreResources1211 0).q).drop 0 := by
  decide +kernel

theorem coreCheck1211_0 :
    ∀ c : Fin 8, (coreChunks1211_0 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_0_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_0_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_0_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_0_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_0_7, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1211_0
#print axioms coreCheck1211_0
end Erdos883Verified
