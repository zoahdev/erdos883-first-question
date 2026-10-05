import Erdos883SmallCertificate174Data
import Erdos883SmallCertificate174Resource031Chunk000
import Erdos883SmallCertificate174Resource031Chunk001
import Erdos883SmallCertificate174Resource031Chunk002
import Erdos883SmallCertificate174Resource031Chunk003
import Erdos883SmallCertificate174Resource031Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_31 :
    (List.ofFn coreChunks174_31).flatten =
      (coreData174.take (coreResources174 31).q).drop 0 := by
  decide +kernel

theorem coreCheck174_31 :
    ∀ c : Fin 5, (coreChunks174_31 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 31)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_31_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_31_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_31_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_31_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_31_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten174_31
#print axioms coreCheck174_31
end Erdos883Verified
