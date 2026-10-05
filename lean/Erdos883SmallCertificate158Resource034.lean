import Erdos883SmallCertificate158Data
import Erdos883SmallCertificate158Resource034Chunk000
import Erdos883SmallCertificate158Resource034Chunk001
import Erdos883SmallCertificate158Resource034Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_34 :
    (List.ofFn coreChunks158_34).flatten =
      (coreData158.take (coreResources158 34).q).drop 0 := by
  decide +kernel

theorem coreCheck158_34 :
    ∀ c : Fin 3, (coreChunks158_34 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 34)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_34_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_34_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_34_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten158_34
#print axioms coreCheck158_34
end Erdos883Verified
