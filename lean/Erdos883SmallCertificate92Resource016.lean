import Erdos883SmallCertificate92Data
import Erdos883SmallCertificate92Resource016Chunk000
import Erdos883SmallCertificate92Resource016Chunk001
import Erdos883SmallCertificate92Resource016Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten92_16 :
    (List.ofFn coreChunks92_16).flatten =
      (coreData92.take (coreResources92 16).q).drop 0 := by
  decide +kernel

theorem coreCheck92_16 :
    ∀ c : Fin 3, (coreChunks92_16 c).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 16)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk92_16_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk92_16_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk92_16_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten92_16
#print axioms coreCheck92_16
end Erdos883Verified
