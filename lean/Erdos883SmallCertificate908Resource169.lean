import Erdos883SmallCertificate908Data
import Erdos883SmallCertificate908Resource169Chunk000
import Erdos883SmallCertificate908Resource169Chunk001
import Erdos883SmallCertificate908Resource169Chunk002
import Erdos883SmallCertificate908Resource169Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_169 :
    (List.ofFn coreChunks908_169).flatten =
      (coreData908.take (coreResources908 169).q).drop 402 := by
  decide +kernel

theorem coreCheck908_169 :
    ∀ c : Fin 4, (coreChunks908_169 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 169)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_169_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_169_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_169_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_169_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten908_169
#print axioms coreCheck908_169
end Erdos883Verified
