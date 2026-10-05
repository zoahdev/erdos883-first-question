import Erdos883SmallCertificate93Data
import Erdos883SmallCertificate93Resource017Chunk000
import Erdos883SmallCertificate93Resource017Chunk001
import Erdos883SmallCertificate93Resource017Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten93_17 :
    (List.ofFn coreChunks93_17).flatten =
      (coreData93.take (coreResources93 17).q).drop 0 := by
  decide +kernel

theorem coreCheck93_17 :
    ∀ c : Fin 3, (coreChunks93_17 c).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 17)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk93_17_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk93_17_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk93_17_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten93_17
#print axioms coreCheck93_17
end Erdos883Verified
