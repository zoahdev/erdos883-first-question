import Erdos883SmallCertificate908Data
import Erdos883SmallCertificate908Resource000Chunk000
import Erdos883SmallCertificate908Resource000Chunk001
import Erdos883SmallCertificate908Resource000Chunk002
import Erdos883SmallCertificate908Resource000Chunk003
import Erdos883SmallCertificate908Resource000Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_0 :
    (List.ofFn coreChunks908_0).flatten =
      (coreData908.take (coreResources908 0).q).drop 0 := by
  decide +kernel

theorem coreCheck908_0 :
    ∀ c : Fin 5, (coreChunks908_0 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_0_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_0_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten908_0
#print axioms coreCheck908_0
end Erdos883Verified
