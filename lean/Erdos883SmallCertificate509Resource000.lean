import Erdos883SmallCertificate509Data
import Erdos883SmallCertificate509Resource000Chunk000
import Erdos883SmallCertificate509Resource000Chunk001
import Erdos883SmallCertificate509Resource000Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_0 :
    (List.ofFn coreChunks509_0).flatten =
      (coreData509.take (coreResources509 0).q).drop 0 := by
  decide +kernel

theorem coreCheck509_0 :
    ∀ c : Fin 3, (coreChunks509_0 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_0_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten509_0
#print axioms coreCheck509_0
end Erdos883Verified
