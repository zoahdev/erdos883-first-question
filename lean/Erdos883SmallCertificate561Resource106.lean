import Erdos883SmallCertificate561Data
import Erdos883SmallCertificate561Resource106Chunk000
import Erdos883SmallCertificate561Resource106Chunk001
import Erdos883SmallCertificate561Resource106Chunk002
import Erdos883SmallCertificate561Resource106Chunk003
import Erdos883SmallCertificate561Resource106Chunk004
import Erdos883SmallCertificate561Resource106Chunk005
import Erdos883SmallCertificate561Resource106Chunk006
import Erdos883SmallCertificate561Resource106Chunk007
import Erdos883SmallCertificate561Resource106Chunk008
import Erdos883SmallCertificate561Resource106Chunk009
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_106 :
    (List.ofFn coreChunks561_106).flatten =
      (coreData561.take (coreResources561 106).q).drop 0 := by
  decide +kernel

theorem coreCheck561_106 :
    ∀ c : Fin 10, (coreChunks561_106 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 106)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_106_9, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten561_106
#print axioms coreCheck561_106
end Erdos883Verified
