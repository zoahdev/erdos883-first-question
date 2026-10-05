import Erdos883SmallCertificate749Data
import Erdos883SmallCertificate749Resource142Chunk000
import Erdos883SmallCertificate749Resource142Chunk001
import Erdos883SmallCertificate749Resource142Chunk002
import Erdos883SmallCertificate749Resource142Chunk003
import Erdos883SmallCertificate749Resource142Chunk004
import Erdos883SmallCertificate749Resource142Chunk005
import Erdos883SmallCertificate749Resource142Chunk006
import Erdos883SmallCertificate749Resource142Chunk007
import Erdos883SmallCertificate749Resource142Chunk008
import Erdos883SmallCertificate749Resource142Chunk009
import Erdos883SmallCertificate749Resource142Chunk010
import Erdos883SmallCertificate749Resource142Chunk011
import Erdos883SmallCertificate749Resource142Chunk012
import Erdos883SmallCertificate749Resource142Chunk013
import Erdos883SmallCertificate749Resource142Chunk014
import Erdos883SmallCertificate749Resource142Chunk015
import Erdos883SmallCertificate749Resource142Chunk016
import Erdos883SmallCertificate749Resource142Chunk017
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_142 :
    (List.ofFn coreChunks749_142).flatten =
      (coreData749.take (coreResources749 142).q).drop 0 := by
  decide +kernel

theorem coreCheck749_142 :
    ∀ c : Fin 18, (coreChunks749_142 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 142)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_142_17, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten749_142
#print axioms coreCheck749_142
end Erdos883Verified
