import Erdos883SmallCertificate129Data
import Erdos883SmallCertificate129Resource027Chunk000
import Erdos883SmallCertificate129Resource027Chunk001
import Erdos883SmallCertificate129Resource027Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_27 :
    (List.ofFn coreChunks129_27).flatten =
      (coreData129.take (coreResources129 27).q).drop 0 := by
  decide +kernel

theorem coreCheck129_27 :
    ∀ c : Fin 3, (coreChunks129_27 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 27)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_27_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_27_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk129_27_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten129_27
#print axioms coreCheck129_27
end Erdos883Verified
