import Erdos883SmallCertificate749Data
import Erdos883SmallCertificate749Resource146Chunk000
import Erdos883SmallCertificate749Resource146Chunk001
import Erdos883SmallCertificate749Resource146Chunk002
import Erdos883SmallCertificate749Resource146Chunk003
import Erdos883SmallCertificate749Resource146Chunk004
import Erdos883SmallCertificate749Resource146Chunk005
import Erdos883SmallCertificate749Resource146Chunk006
import Erdos883SmallCertificate749Resource146Chunk007
import Erdos883SmallCertificate749Resource146Chunk008
import Erdos883SmallCertificate749Resource146Chunk009
import Erdos883SmallCertificate749Resource146Chunk010
import Erdos883SmallCertificate749Resource146Chunk011
import Erdos883SmallCertificate749Resource146Chunk012
import Erdos883SmallCertificate749Resource146Chunk013
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_146 :
    (List.ofFn coreChunks749_146).flatten =
      (coreData749.take (coreResources749 146).q).drop 0 := by
  decide +kernel

theorem coreCheck749_146 :
    ∀ c : Fin 14, (coreChunks749_146 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 146)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_146_13, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten749_146
#print axioms coreCheck749_146
end Erdos883Verified
