import Erdos883SmallCertificate192Data
import Erdos883SmallCertificate192Resource036Chunk000
import Erdos883SmallCertificate192Resource036Chunk001
import Erdos883SmallCertificate192Resource036Chunk002
import Erdos883SmallCertificate192Resource036Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_36 :
    (List.ofFn coreChunks192_36).flatten =
      (coreData192.take (coreResources192 36).q).drop 0 := by
  decide +kernel

theorem coreCheck192_36 :
    ∀ c : Fin 4, (coreChunks192_36 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 36)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_36_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_36_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_36_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_36_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten192_36
#print axioms coreCheck192_36
end Erdos883Verified
