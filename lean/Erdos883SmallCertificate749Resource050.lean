import Erdos883SmallCertificate749Data
import Erdos883SmallCertificate749Resource050Chunk000
import Erdos883SmallCertificate749Resource050Chunk001
import Erdos883SmallCertificate749Resource050Chunk002
import Erdos883SmallCertificate749Resource050Chunk003
import Erdos883SmallCertificate749Resource050Chunk004
import Erdos883SmallCertificate749Resource050Chunk005
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_50 :
    (List.ofFn coreChunks749_50).flatten =
      (coreData749.take (coreResources749 50).q).drop 0 := by
  decide +kernel

theorem coreCheck749_50 :
    ∀ c : Fin 6, (coreChunks749_50 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 50)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_50_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_50_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_50_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_50_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_50_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_50_5, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten749_50
#print axioms coreCheck749_50
end Erdos883Verified
