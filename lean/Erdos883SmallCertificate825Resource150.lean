import Erdos883SmallCertificate825Data
import Erdos883SmallCertificate825Resource150Chunk000
import Erdos883SmallCertificate825Resource150Chunk001
import Erdos883SmallCertificate825Resource150Chunk002
import Erdos883SmallCertificate825Resource150Chunk003
import Erdos883SmallCertificate825Resource150Chunk004
import Erdos883SmallCertificate825Resource150Chunk005
import Erdos883SmallCertificate825Resource150Chunk006
import Erdos883SmallCertificate825Resource150Chunk007
import Erdos883SmallCertificate825Resource150Chunk008
import Erdos883SmallCertificate825Resource150Chunk009
import Erdos883SmallCertificate825Resource150Chunk010
import Erdos883SmallCertificate825Resource150Chunk011
import Erdos883SmallCertificate825Resource150Chunk012
import Erdos883SmallCertificate825Resource150Chunk013
import Erdos883SmallCertificate825Resource150Chunk014
import Erdos883SmallCertificate825Resource150Chunk015
import Erdos883SmallCertificate825Resource150Chunk016
import Erdos883SmallCertificate825Resource150Chunk017
import Erdos883SmallCertificate825Resource150Chunk018
import Erdos883SmallCertificate825Resource150Chunk019
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_150 :
    (List.ofFn coreChunks825_150).flatten =
      (coreData825.take (coreResources825 150).q).drop 0 := by
  decide +kernel

theorem coreCheck825_150 :
    ∀ c : Fin 20, (coreChunks825_150 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 150)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_150_19, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten825_150
#print axioms coreCheck825_150
end Erdos883Verified
