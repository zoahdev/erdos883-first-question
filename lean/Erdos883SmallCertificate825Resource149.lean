import Erdos883SmallCertificate825Data
import Erdos883SmallCertificate825Resource149Chunk000
import Erdos883SmallCertificate825Resource149Chunk001
import Erdos883SmallCertificate825Resource149Chunk002
import Erdos883SmallCertificate825Resource149Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_149 :
    (List.ofFn coreChunks825_149).flatten =
      (coreData825.take (coreResources825 149).q).drop 363 := by
  decide +kernel

theorem coreCheck825_149 :
    ∀ c : Fin 4, (coreChunks825_149 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 149)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_149_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_149_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_149_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_149_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten825_149
#print axioms coreCheck825_149
end Erdos883Verified
