import Erdos883SmallCertificate462Data
import Erdos883SmallCertificate462Resource000Chunk000
import Erdos883SmallCertificate462Resource000Chunk001
import Erdos883SmallCertificate462Resource000Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_0 :
    (List.ofFn coreChunks462_0).flatten =
      (coreData462.take (coreResources462 0).q).drop 0 := by
  decide +kernel

theorem coreCheck462_0 :
    ∀ c : Fin 3, (coreChunks462_0 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_0_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten462_0
#print axioms coreCheck462_0
end Erdos883Verified
