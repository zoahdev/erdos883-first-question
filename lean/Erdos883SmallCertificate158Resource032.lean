import Erdos883SmallCertificate158Data
import Erdos883SmallCertificate158Resource032Chunk000
import Erdos883SmallCertificate158Resource032Chunk001
import Erdos883SmallCertificate158Resource032Chunk002
import Erdos883SmallCertificate158Resource032Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_32 :
    (List.ofFn coreChunks158_32).flatten =
      (coreData158.take (coreResources158 32).q).drop 0 := by
  decide +kernel

theorem coreCheck158_32 :
    ∀ c : Fin 4, (coreChunks158_32 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 32)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_32_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_32_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_32_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_32_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten158_32
#print axioms coreCheck158_32
end Erdos883Verified
