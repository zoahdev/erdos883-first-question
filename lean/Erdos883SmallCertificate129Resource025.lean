import Erdos883SmallCertificate129Data
import Erdos883SmallCertificate129Resource025Chunk000
import Erdos883SmallCertificate129Resource025Chunk001
import Erdos883SmallCertificate129Resource025Chunk002
import Erdos883SmallCertificate129Resource025Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_25 :
    (List.ofFn coreChunks129_25).flatten =
      (coreData129.take (coreResources129 25).q).drop 0 := by
  decide +kernel

theorem coreCheck129_25 :
    ∀ c : Fin 4, (coreChunks129_25 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 25)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_25_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_25_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_25_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_25_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten129_25
#print axioms coreCheck129_25
end Erdos883Verified
