import Erdos883SmallCertificate462Data
import Erdos883SmallCertificate462Resource028Chunk000
import Erdos883SmallCertificate462Resource028Chunk001
import Erdos883SmallCertificate462Resource028Chunk002
import Erdos883SmallCertificate462Resource028Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_28 :
    (List.ofFn coreChunks462_28).flatten =
      (coreData462.take (coreResources462 28).q).drop 0 := by
  decide +kernel

theorem coreCheck462_28 :
    ∀ c : Fin 4, (coreChunks462_28 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 28)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_28_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_28_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_28_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_28_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten462_28
#print axioms coreCheck462_28
end Erdos883Verified
