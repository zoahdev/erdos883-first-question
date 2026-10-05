import Erdos883SmallCertificate825Data
import Erdos883SmallCertificate825Resource151Chunk000
import Erdos883SmallCertificate825Resource151Chunk001
import Erdos883SmallCertificate825Resource151Chunk002
import Erdos883SmallCertificate825Resource151Chunk003
import Erdos883SmallCertificate825Resource151Chunk004
import Erdos883SmallCertificate825Resource151Chunk005
import Erdos883SmallCertificate825Resource151Chunk006
import Erdos883SmallCertificate825Resource151Chunk007
import Erdos883SmallCertificate825Resource151Chunk008
import Erdos883SmallCertificate825Resource151Chunk009
import Erdos883SmallCertificate825Resource151Chunk010
import Erdos883SmallCertificate825Resource151Chunk011
import Erdos883SmallCertificate825Resource151Chunk012
import Erdos883SmallCertificate825Resource151Chunk013
import Erdos883SmallCertificate825Resource151Chunk014
import Erdos883SmallCertificate825Resource151Chunk015
import Erdos883SmallCertificate825Resource151Chunk016
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_151 :
    (List.ofFn coreChunks825_151).flatten =
      (coreData825.take (coreResources825 151).q).drop 0 := by
  decide +kernel

theorem coreCheck825_151 :
    ∀ c : Fin 17, (coreChunks825_151 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 151)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk825_151_16, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten825_151
#print axioms coreCheck825_151
end Erdos883Verified
