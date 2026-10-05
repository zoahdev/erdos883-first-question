import Erdos883SmallCertificate749Data
import Erdos883SmallCertificate749Resource143Chunk000
import Erdos883SmallCertificate749Resource143Chunk001
import Erdos883SmallCertificate749Resource143Chunk002
import Erdos883SmallCertificate749Resource143Chunk003
import Erdos883SmallCertificate749Resource143Chunk004
import Erdos883SmallCertificate749Resource143Chunk005
import Erdos883SmallCertificate749Resource143Chunk006
import Erdos883SmallCertificate749Resource143Chunk007
import Erdos883SmallCertificate749Resource143Chunk008
import Erdos883SmallCertificate749Resource143Chunk009
import Erdos883SmallCertificate749Resource143Chunk010
import Erdos883SmallCertificate749Resource143Chunk011
import Erdos883SmallCertificate749Resource143Chunk012
import Erdos883SmallCertificate749Resource143Chunk013
import Erdos883SmallCertificate749Resource143Chunk014
import Erdos883SmallCertificate749Resource143Chunk015
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_143 :
    (List.ofFn coreChunks749_143).flatten =
      (coreData749.take (coreResources749 143).q).drop 0 := by
  decide +kernel

theorem coreCheck749_143 :
    ∀ c : Fin 16, (coreChunks749_143 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 143)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_143_15, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten749_143
#print axioms coreCheck749_143
end Erdos883Verified
