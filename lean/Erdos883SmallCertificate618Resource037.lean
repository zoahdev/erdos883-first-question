import Erdos883SmallCertificate618Data
import Erdos883SmallCertificate618Resource037Chunk000
import Erdos883SmallCertificate618Resource037Chunk001
import Erdos883SmallCertificate618Resource037Chunk002
import Erdos883SmallCertificate618Resource037Chunk003
import Erdos883SmallCertificate618Resource037Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_37 :
    (List.ofFn coreChunks618_37).flatten =
      (coreData618.take (coreResources618 37).q).drop 0 := by
  decide +kernel

theorem coreCheck618_37 :
    ∀ c : Fin 5, (coreChunks618_37 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 37)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_37_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_37_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_37_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_37_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_37_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten618_37
#print axioms coreCheck618_37
end Erdos883Verified
