import Erdos883SmallCertificate908Data
import Erdos883SmallCertificate908Resource171Chunk000
import Erdos883SmallCertificate908Resource171Chunk001
import Erdos883SmallCertificate908Resource171Chunk002
import Erdos883SmallCertificate908Resource171Chunk003
import Erdos883SmallCertificate908Resource171Chunk004
import Erdos883SmallCertificate908Resource171Chunk005
import Erdos883SmallCertificate908Resource171Chunk006
import Erdos883SmallCertificate908Resource171Chunk007
import Erdos883SmallCertificate908Resource171Chunk008
import Erdos883SmallCertificate908Resource171Chunk009
import Erdos883SmallCertificate908Resource171Chunk010
import Erdos883SmallCertificate908Resource171Chunk011
import Erdos883SmallCertificate908Resource171Chunk012
import Erdos883SmallCertificate908Resource171Chunk013
import Erdos883SmallCertificate908Resource171Chunk014
import Erdos883SmallCertificate908Resource171Chunk015
import Erdos883SmallCertificate908Resource171Chunk016
import Erdos883SmallCertificate908Resource171Chunk017
import Erdos883SmallCertificate908Resource171Chunk018
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_171 :
    (List.ofFn coreChunks908_171).flatten =
      (coreData908.take (coreResources908 171).q).drop 0 := by
  decide +kernel

theorem coreCheck908_171 :
    ∀ c : Fin 19, (coreChunks908_171 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 171)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_171_18, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten908_171
#print axioms coreCheck908_171
end Erdos883Verified
