import Erdos883SmallCertificate212Data
import Erdos883SmallCertificate212Resource039Chunk000
import Erdos883SmallCertificate212Resource039Chunk001
import Erdos883SmallCertificate212Resource039Chunk002
import Erdos883SmallCertificate212Resource039Chunk003
import Erdos883SmallCertificate212Resource039Chunk004
import Erdos883SmallCertificate212Resource039Chunk005
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_39 :
    (List.ofFn coreChunks212_39).flatten =
      (coreData212.take (coreResources212 39).q).drop 0 := by
  decide +kernel

theorem coreCheck212_39 :
    ∀ c : Fin 6, (coreChunks212_39 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 39)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_39_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_39_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_39_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_39_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_39_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk212_39_5, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten212_39
#print axioms coreCheck212_39
end Erdos883Verified
