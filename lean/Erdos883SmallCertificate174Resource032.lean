import Erdos883SmallCertificate174Data
import Erdos883SmallCertificate174Resource032Chunk000
import Erdos883SmallCertificate174Resource032Chunk001
import Erdos883SmallCertificate174Resource032Chunk002
import Erdos883SmallCertificate174Resource032Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_32 :
    (List.ofFn coreChunks174_32).flatten =
      (coreData174.take (coreResources174 32).q).drop 0 := by
  decide +kernel

theorem coreCheck174_32 :
    ∀ c : Fin 4, (coreChunks174_32 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 32)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_32_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_32_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_32_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_32_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten174_32
#print axioms coreCheck174_32
end Erdos883Verified
