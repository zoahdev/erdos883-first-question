import Erdos883SmallCertificate908Data
import Erdos883SmallCertificate908Resource063Chunk000
import Erdos883SmallCertificate908Resource063Chunk001
import Erdos883SmallCertificate908Resource063Chunk002
import Erdos883SmallCertificate908Resource063Chunk003
import Erdos883SmallCertificate908Resource063Chunk004
import Erdos883SmallCertificate908Resource063Chunk005
import Erdos883SmallCertificate908Resource063Chunk006
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_63 :
    (List.ofFn coreChunks908_63).flatten =
      (coreData908.take (coreResources908 63).q).drop 0 := by
  decide +kernel

theorem coreCheck908_63 :
    ∀ c : Fin 7, (coreChunks908_63 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 63)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_63_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_63_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_63_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_63_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_63_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_63_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_63_6, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten908_63
#print axioms coreCheck908_63
end Erdos883Verified
