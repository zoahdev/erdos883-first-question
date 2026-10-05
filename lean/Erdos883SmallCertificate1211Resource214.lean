import Erdos883SmallCertificate1211Data
import Erdos883SmallCertificate1211Resource214Chunk000
import Erdos883SmallCertificate1211Resource214Chunk001
import Erdos883SmallCertificate1211Resource214Chunk002
import Erdos883SmallCertificate1211Resource214Chunk003
import Erdos883SmallCertificate1211Resource214Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_214 :
    (List.ofFn coreChunks1211_214).flatten =
      (coreData1211.take (coreResources1211 214).q).drop 539 := by
  decide +kernel

theorem coreCheck1211_214 :
    ∀ c : Fin 5, (coreChunks1211_214 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 214)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_214_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_214_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_214_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_214_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_214_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1211_214
#print axioms coreCheck1211_214
end Erdos883Verified
