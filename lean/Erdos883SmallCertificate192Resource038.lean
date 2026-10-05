import Erdos883SmallCertificate192Data
import Erdos883SmallCertificate192Resource038Chunk000
import Erdos883SmallCertificate192Resource038Chunk001
import Erdos883SmallCertificate192Resource038Chunk002
import Erdos883SmallCertificate192Resource038Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_38 :
    (List.ofFn coreChunks192_38).flatten =
      (coreData192.take (coreResources192 38).q).drop 0 := by
  decide +kernel

theorem coreCheck192_38 :
    ∀ c : Fin 4, (coreChunks192_38 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 38)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_38_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_38_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_38_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_38_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten192_38
#print axioms coreCheck192_38
end Erdos883Verified
