import Erdos883SmallCertificate908Data
import Erdos883SmallCertificate908Resource170Chunk000
import Erdos883SmallCertificate908Resource170Chunk001
import Erdos883SmallCertificate908Resource170Chunk002
import Erdos883SmallCertificate908Resource170Chunk003
import Erdos883SmallCertificate908Resource170Chunk004
import Erdos883SmallCertificate908Resource170Chunk005
import Erdos883SmallCertificate908Resource170Chunk006
import Erdos883SmallCertificate908Resource170Chunk007
import Erdos883SmallCertificate908Resource170Chunk008
import Erdos883SmallCertificate908Resource170Chunk009
import Erdos883SmallCertificate908Resource170Chunk010
import Erdos883SmallCertificate908Resource170Chunk011
import Erdos883SmallCertificate908Resource170Chunk012
import Erdos883SmallCertificate908Resource170Chunk013
import Erdos883SmallCertificate908Resource170Chunk014
import Erdos883SmallCertificate908Resource170Chunk015
import Erdos883SmallCertificate908Resource170Chunk016
import Erdos883SmallCertificate908Resource170Chunk017
import Erdos883SmallCertificate908Resource170Chunk018
import Erdos883SmallCertificate908Resource170Chunk019
import Erdos883SmallCertificate908Resource170Chunk020
import Erdos883SmallCertificate908Resource170Chunk021
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_170 :
    (List.ofFn coreChunks908_170).flatten =
      (coreData908.take (coreResources908 170).q).drop 0 := by
  decide +kernel

theorem coreCheck908_170 :
    ∀ c : Fin 22, (coreChunks908_170 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 170)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_19, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_20, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_170_21, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten908_170
#print axioms coreCheck908_170
end Erdos883Verified
