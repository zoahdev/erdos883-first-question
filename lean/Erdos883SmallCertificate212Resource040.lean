import Erdos883SmallCertificate212Data
import Erdos883SmallCertificate212Resource040Chunk000
import Erdos883SmallCertificate212Resource040Chunk001
import Erdos883SmallCertificate212Resource040Chunk002
import Erdos883SmallCertificate212Resource040Chunk003
import Erdos883SmallCertificate212Resource040Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_40 :
    (List.ofFn coreChunks212_40).flatten =
      (coreData212.take (coreResources212 40).q).drop 0 := by
  decide +kernel

theorem coreCheck212_40 :
    ∀ c : Fin 5, (coreChunks212_40 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 40)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_40_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_40_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_40_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_40_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_40_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten212_40
#print axioms coreCheck212_40
end Erdos883Verified
