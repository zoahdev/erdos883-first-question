import Erdos883SmallCertificate561Data
import Erdos883SmallCertificate561Resource101Chunk000
import Erdos883SmallCertificate561Resource101Chunk001
import Erdos883SmallCertificate561Resource101Chunk002
import Erdos883SmallCertificate561Resource101Chunk003
import Erdos883SmallCertificate561Resource101Chunk004
import Erdos883SmallCertificate561Resource101Chunk005
import Erdos883SmallCertificate561Resource101Chunk006
import Erdos883SmallCertificate561Resource101Chunk007
import Erdos883SmallCertificate561Resource101Chunk008
import Erdos883SmallCertificate561Resource101Chunk009
import Erdos883SmallCertificate561Resource101Chunk010
import Erdos883SmallCertificate561Resource101Chunk011
import Erdos883SmallCertificate561Resource101Chunk012
import Erdos883SmallCertificate561Resource101Chunk013
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_101 :
    (List.ofFn coreChunks561_101).flatten =
      (coreData561.take (coreResources561 101).q).drop 0 := by
  decide +kernel

theorem coreCheck561_101 :
    ∀ c : Fin 14, (coreChunks561_101 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 101)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_101_13, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten561_101
#print axioms coreCheck561_101
end Erdos883Verified
