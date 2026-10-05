import Erdos883SmallCertificate158Data
import Erdos883SmallCertificate158Resource037Chunk000
import Erdos883SmallCertificate158Resource037Chunk001
import Erdos883SmallCertificate158Resource037Chunk002
import Erdos883SmallCertificate158Resource037Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten158_37 :
    (List.ofFn coreChunks158_37).flatten =
      (coreData158.take (coreResources158 37).q).drop 0 := by
  decide +kernel

theorem coreCheck158_37 :
    ∀ c : Fin 4, (coreChunks158_37 c).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 37)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_37_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_37_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_37_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk158_37_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten158_37
#print axioms coreCheck158_37
end Erdos883Verified
