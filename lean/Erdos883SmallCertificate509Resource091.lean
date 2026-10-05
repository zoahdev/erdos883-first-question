import Erdos883SmallCertificate509Data
import Erdos883SmallCertificate509Resource091Chunk000
import Erdos883SmallCertificate509Resource091Chunk001
import Erdos883SmallCertificate509Resource091Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_91 :
    (List.ofFn coreChunks509_91).flatten =
      (coreData509.take (coreResources509 91).q).drop 219 := by
  decide +kernel

theorem coreCheck509_91 :
    ∀ c : Fin 3, (coreChunks509_91 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 91)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_91_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_91_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_91_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten509_91
#print axioms coreCheck509_91
end Erdos883Verified
