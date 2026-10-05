import Erdos883SmallCertificate158Data
import Erdos883SmallCertificate158Resource031Chunk000
import Erdos883SmallCertificate158Resource031Chunk001
import Erdos883SmallCertificate158Resource031Chunk002
import Erdos883SmallCertificate158Resource031Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_31 :
    (List.ofFn coreChunks158_31).flatten =
      (coreData158.take (coreResources158 31).q).drop 0 := by
  decide +kernel

theorem coreCheck158_31 :
    ∀ c : Fin 4, (coreChunks158_31 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 31)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_31_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_31_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_31_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_31_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten158_31
#print axioms coreCheck158_31
end Erdos883Verified
