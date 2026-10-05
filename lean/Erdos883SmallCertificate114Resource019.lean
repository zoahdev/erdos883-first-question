import Erdos883SmallCertificate114Data
import Erdos883SmallCertificate114Resource019Chunk000
import Erdos883SmallCertificate114Resource019Chunk001
import Erdos883SmallCertificate114Resource019Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_19 :
    (List.ofFn coreChunks114_19).flatten =
      (coreData114.take (coreResources114 19).q).drop 0 := by
  decide +kernel

theorem coreCheck114_19 :
    ∀ c : Fin 3, (coreChunks114_19 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 19)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk114_19_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk114_19_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk114_19_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten114_19
#print axioms coreCheck114_19
end Erdos883Verified
