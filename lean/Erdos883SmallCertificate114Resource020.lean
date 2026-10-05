import Erdos883SmallCertificate114Data
import Erdos883SmallCertificate114Resource020Chunk000
import Erdos883SmallCertificate114Resource020Chunk001
import Erdos883SmallCertificate114Resource020Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten114_20 :
    (List.ofFn coreChunks114_20).flatten =
      (coreData114.take (coreResources114 20).q).drop 0 := by
  decide +kernel

theorem coreCheck114_20 :
    ∀ c : Fin 3, (coreChunks114_20 c).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 20)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk114_20_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk114_20_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk114_20_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten114_20
#print axioms coreCheck114_20
end Erdos883Verified
