import Erdos883SmallCertificate749Data
import Erdos883SmallCertificate749Resource000Chunk000
import Erdos883SmallCertificate749Resource000Chunk001
import Erdos883SmallCertificate749Resource000Chunk002
import Erdos883SmallCertificate749Resource000Chunk003
import Erdos883SmallCertificate749Resource000Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_0 :
    (List.ofFn coreChunks749_0).flatten =
      (coreData749.take (coreResources749 0).q).drop 0 := by
  decide +kernel

theorem coreCheck749_0 :
    ∀ c : Fin 5, (coreChunks749_0 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_0_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_0_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten749_0
#print axioms coreCheck749_0
end Erdos883Verified
