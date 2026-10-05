import Erdos883SmallCertificate618Data
import Erdos883SmallCertificate618Resource000Chunk000
import Erdos883SmallCertificate618Resource000Chunk001
import Erdos883SmallCertificate618Resource000Chunk002
import Erdos883SmallCertificate618Resource000Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_0 :
    (List.ofFn coreChunks618_0).flatten =
      (coreData618.take (coreResources618 0).q).drop 0 := by
  decide +kernel

theorem coreCheck618_0 :
    ∀ c : Fin 4, (coreChunks618_0 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_0_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten618_0
#print axioms coreCheck618_0
end Erdos883Verified
