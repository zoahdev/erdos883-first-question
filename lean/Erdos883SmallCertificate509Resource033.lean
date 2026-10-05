import Erdos883SmallCertificate509Data
import Erdos883SmallCertificate509Resource033Chunk000
import Erdos883SmallCertificate509Resource033Chunk001
import Erdos883SmallCertificate509Resource033Chunk002
import Erdos883SmallCertificate509Resource033Chunk003
import Erdos883SmallCertificate509Resource033Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_33 :
    (List.ofFn coreChunks509_33).flatten =
      (coreData509.take (coreResources509 33).q).drop 0 := by
  decide +kernel

theorem coreCheck509_33 :
    ∀ c : Fin 5, (coreChunks509_33 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 33)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_33_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_33_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_33_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_33_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_33_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten509_33
#print axioms coreCheck509_33
end Erdos883Verified
