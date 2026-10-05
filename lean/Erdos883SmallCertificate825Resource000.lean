import Erdos883SmallCertificate825Data
import Erdos883SmallCertificate825Resource000Chunk000
import Erdos883SmallCertificate825Resource000Chunk001
import Erdos883SmallCertificate825Resource000Chunk002
import Erdos883SmallCertificate825Resource000Chunk003
import Erdos883SmallCertificate825Resource000Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_0 :
    (List.ofFn coreChunks825_0).flatten =
      (coreData825.take (coreResources825 0).q).drop 0 := by
  decide +kernel

theorem coreCheck825_0 :
    ∀ c : Fin 5, (coreChunks825_0 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_0_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_0_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten825_0
#print axioms coreCheck825_0
end Erdos883Verified
