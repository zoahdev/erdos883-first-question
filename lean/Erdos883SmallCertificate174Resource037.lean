import Erdos883SmallCertificate174Data
import Erdos883SmallCertificate174Resource037Chunk000
import Erdos883SmallCertificate174Resource037Chunk001
import Erdos883SmallCertificate174Resource037Chunk002
import Erdos883SmallCertificate174Resource037Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_37 :
    (List.ofFn coreChunks174_37).flatten =
      (coreData174.take (coreResources174 37).q).drop 0 := by
  decide +kernel

theorem coreCheck174_37 :
    ∀ c : Fin 4, (coreChunks174_37 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 37)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_37_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_37_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_37_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_37_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten174_37
#print axioms coreCheck174_37
end Erdos883Verified
