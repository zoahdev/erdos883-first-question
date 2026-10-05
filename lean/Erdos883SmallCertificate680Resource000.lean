import Erdos883SmallCertificate680Data
import Erdos883SmallCertificate680Resource000Chunk000
import Erdos883SmallCertificate680Resource000Chunk001
import Erdos883SmallCertificate680Resource000Chunk002
import Erdos883SmallCertificate680Resource000Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_0 :
    (List.ofFn coreChunks680_0).flatten =
      (coreData680.take (coreResources680 0).q).drop 0 := by
  decide +kernel

theorem coreCheck680_0 :
    ∀ c : Fin 4, (coreChunks680_0 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_0_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten680_0
#print axioms coreCheck680_0
end Erdos883Verified
