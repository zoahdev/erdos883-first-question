import Erdos883SmallCertificate825Data
import Erdos883SmallCertificate825Resource155Chunk000
import Erdos883SmallCertificate825Resource155Chunk001
import Erdos883SmallCertificate825Resource155Chunk002
import Erdos883SmallCertificate825Resource155Chunk003
import Erdos883SmallCertificate825Resource155Chunk004
import Erdos883SmallCertificate825Resource155Chunk005
import Erdos883SmallCertificate825Resource155Chunk006
import Erdos883SmallCertificate825Resource155Chunk007
import Erdos883SmallCertificate825Resource155Chunk008
import Erdos883SmallCertificate825Resource155Chunk009
import Erdos883SmallCertificate825Resource155Chunk010
import Erdos883SmallCertificate825Resource155Chunk011
import Erdos883SmallCertificate825Resource155Chunk012
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_155 :
    (List.ofFn coreChunks825_155).flatten =
      (coreData825.take (coreResources825 155).q).drop 0 := by
  decide +kernel

theorem coreCheck825_155 :
    ∀ c : Fin 13, (coreChunks825_155 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 155)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_155_12, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten825_155
#print axioms coreCheck825_155
end Erdos883Verified
