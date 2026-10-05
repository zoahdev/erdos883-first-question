import Erdos883SmallCertificate680Data
import Erdos883SmallCertificate680Resource124Chunk000
import Erdos883SmallCertificate680Resource124Chunk001
import Erdos883SmallCertificate680Resource124Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_124 :
    (List.ofFn coreChunks680_124).flatten =
      (coreData680.take (coreResources680 124).q).drop 300 := by
  decide +kernel

theorem coreCheck680_124 :
    ∀ c : Fin 3, (coreChunks680_124 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 124)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_124_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_124_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_124_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten680_124
#print axioms coreCheck680_124
end Erdos883Verified
