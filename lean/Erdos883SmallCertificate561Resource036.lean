import Erdos883SmallCertificate561Data
import Erdos883SmallCertificate561Resource036Chunk000
import Erdos883SmallCertificate561Resource036Chunk001
import Erdos883SmallCertificate561Resource036Chunk002
import Erdos883SmallCertificate561Resource036Chunk003
import Erdos883SmallCertificate561Resource036Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_36 :
    (List.ofFn coreChunks561_36).flatten =
      (coreData561.take (coreResources561 36).q).drop 0 := by
  decide +kernel

theorem coreCheck561_36 :
    ∀ c : Fin 5, (coreChunks561_36 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 36)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_36_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_36_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_36_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_36_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_36_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten561_36
#print axioms coreCheck561_36
end Erdos883Verified
