import Erdos883SmallCertificate825Data
import Erdos883SmallCertificate825Resource156Chunk000
import Erdos883SmallCertificate825Resource156Chunk001
import Erdos883SmallCertificate825Resource156Chunk002
import Erdos883SmallCertificate825Resource156Chunk003
import Erdos883SmallCertificate825Resource156Chunk004
import Erdos883SmallCertificate825Resource156Chunk005
import Erdos883SmallCertificate825Resource156Chunk006
import Erdos883SmallCertificate825Resource156Chunk007
import Erdos883SmallCertificate825Resource156Chunk008
import Erdos883SmallCertificate825Resource156Chunk009
import Erdos883SmallCertificate825Resource156Chunk010
import Erdos883SmallCertificate825Resource156Chunk011
import Erdos883SmallCertificate825Resource156Chunk012
import Erdos883SmallCertificate825Resource156Chunk013
import Erdos883SmallCertificate825Resource156Chunk014
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_156 :
    (List.ofFn coreChunks825_156).flatten =
      (coreData825.take (coreResources825 156).q).drop 0 := by
  decide +kernel

theorem coreCheck825_156 :
    ∀ c : Fin 15, (coreChunks825_156 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 156)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_156_14, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten825_156
#print axioms coreCheck825_156
end Erdos883Verified
