import Erdos883SmallCertificate825Data
import Erdos883SmallCertificate825Resource056Chunk000
import Erdos883SmallCertificate825Resource056Chunk001
import Erdos883SmallCertificate825Resource056Chunk002
import Erdos883SmallCertificate825Resource056Chunk003
import Erdos883SmallCertificate825Resource056Chunk004
import Erdos883SmallCertificate825Resource056Chunk005
import Erdos883SmallCertificate825Resource056Chunk006
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_56 :
    (List.ofFn coreChunks825_56).flatten =
      (coreData825.take (coreResources825 56).q).drop 0 := by
  decide +kernel

theorem coreCheck825_56 :
    ∀ c : Fin 7, (coreChunks825_56 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 56)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_56_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_56_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_56_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_56_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_56_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_56_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_56_6, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten825_56
#print axioms coreCheck825_56
end Erdos883Verified
