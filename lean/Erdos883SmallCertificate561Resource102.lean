import Erdos883SmallCertificate561Data
import Erdos883SmallCertificate561Resource102Chunk000
import Erdos883SmallCertificate561Resource102Chunk001
import Erdos883SmallCertificate561Resource102Chunk002
import Erdos883SmallCertificate561Resource102Chunk003
import Erdos883SmallCertificate561Resource102Chunk004
import Erdos883SmallCertificate561Resource102Chunk005
import Erdos883SmallCertificate561Resource102Chunk006
import Erdos883SmallCertificate561Resource102Chunk007
import Erdos883SmallCertificate561Resource102Chunk008
import Erdos883SmallCertificate561Resource102Chunk009
import Erdos883SmallCertificate561Resource102Chunk010
import Erdos883SmallCertificate561Resource102Chunk011
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_102 :
    (List.ofFn coreChunks561_102).flatten =
      (coreData561.take (coreResources561 102).q).drop 0 := by
  decide +kernel

theorem coreCheck561_102 :
    ∀ c : Fin 12, (coreChunks561_102 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 102)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_102_11, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten561_102
#print axioms coreCheck561_102
end Erdos883Verified
