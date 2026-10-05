import Erdos883SmallCertificate174Data
import Erdos883SmallCertificate174Resource034Chunk000
import Erdos883SmallCertificate174Resource034Chunk001
import Erdos883SmallCertificate174Resource034Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten174_34 :
    (List.ofFn coreChunks174_34).flatten =
      (coreData174.take (coreResources174 34).q).drop 0 := by
  decide +kernel

theorem coreCheck174_34 :
    ∀ c : Fin 3, (coreChunks174_34 c).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 34)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_34_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_34_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk174_34_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten174_34
#print axioms coreCheck174_34
end Erdos883Verified
