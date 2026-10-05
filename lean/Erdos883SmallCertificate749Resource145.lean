import Erdos883SmallCertificate749Data
import Erdos883SmallCertificate749Resource145Chunk000
import Erdos883SmallCertificate749Resource145Chunk001
import Erdos883SmallCertificate749Resource145Chunk002
import Erdos883SmallCertificate749Resource145Chunk003
import Erdos883SmallCertificate749Resource145Chunk004
import Erdos883SmallCertificate749Resource145Chunk005
import Erdos883SmallCertificate749Resource145Chunk006
import Erdos883SmallCertificate749Resource145Chunk007
import Erdos883SmallCertificate749Resource145Chunk008
import Erdos883SmallCertificate749Resource145Chunk009
import Erdos883SmallCertificate749Resource145Chunk010
import Erdos883SmallCertificate749Resource145Chunk011
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_145 :
    (List.ofFn coreChunks749_145).flatten =
      (coreData749.take (coreResources749 145).q).drop 0 := by
  decide +kernel

theorem coreCheck749_145 :
    ∀ c : Fin 12, (coreChunks749_145 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 145)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_145_11, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten749_145
#print axioms coreCheck749_145
end Erdos883Verified
