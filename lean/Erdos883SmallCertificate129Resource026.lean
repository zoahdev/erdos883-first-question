import Erdos883SmallCertificate129Data
import Erdos883SmallCertificate129Resource026Chunk000
import Erdos883SmallCertificate129Resource026Chunk001
import Erdos883SmallCertificate129Resource026Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_26 :
    (List.ofFn coreChunks129_26).flatten =
      (coreData129.take (coreResources129 26).q).drop 0 := by
  decide +kernel

theorem coreCheck129_26 :
    ∀ c : Fin 3, (coreChunks129_26 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 26)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_26_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_26_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_26_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten129_26
#print axioms coreCheck129_26
end Erdos883Verified
