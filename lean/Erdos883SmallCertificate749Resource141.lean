import Erdos883SmallCertificate749Data
import Erdos883SmallCertificate749Resource141Chunk000
import Erdos883SmallCertificate749Resource141Chunk001
import Erdos883SmallCertificate749Resource141Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_141 :
    (List.ofFn coreChunks749_141).flatten =
      (coreData749.take (coreResources749 141).q).drop 332 := by
  decide +kernel

theorem coreCheck749_141 :
    ∀ c : Fin 3, (coreChunks749_141 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 141)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_141_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_141_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk749_141_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten749_141
#print axioms coreCheck749_141
end Erdos883Verified
