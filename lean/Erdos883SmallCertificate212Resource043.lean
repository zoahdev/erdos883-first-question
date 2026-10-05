import Erdos883SmallCertificate212Data
import Erdos883SmallCertificate212Resource043Chunk000
import Erdos883SmallCertificate212Resource043Chunk001
import Erdos883SmallCertificate212Resource043Chunk002
import Erdos883SmallCertificate212Resource043Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_43 :
    (List.ofFn coreChunks212_43).flatten =
      (coreData212.take (coreResources212 43).q).drop 0 := by
  decide +kernel

theorem coreCheck212_43 :
    ∀ c : Fin 4, (coreChunks212_43 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 43)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_43_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_43_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_43_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_43_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten212_43
#print axioms coreCheck212_43
end Erdos883Verified
