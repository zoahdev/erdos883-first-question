import Erdos883SmallCertificate561Data
import Erdos883SmallCertificate561Resource000Chunk000
import Erdos883SmallCertificate561Resource000Chunk001
import Erdos883SmallCertificate561Resource000Chunk002
import Erdos883SmallCertificate561Resource000Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_0 :
    (List.ofFn coreChunks561_0).flatten =
      (coreData561.take (coreResources561 0).q).drop 0 := by
  decide +kernel

theorem coreCheck561_0 :
    ∀ c : Fin 4, (coreChunks561_0 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_0_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten561_0
#print axioms coreCheck561_0
end Erdos883Verified
