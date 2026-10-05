import Erdos883SmallCertificate192Data
import Erdos883SmallCertificate192Resource039Chunk000
import Erdos883SmallCertificate192Resource039Chunk001
import Erdos883SmallCertificate192Resource039Chunk002
import Erdos883SmallCertificate192Resource039Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_39 :
    (List.ofFn coreChunks192_39).flatten =
      (coreData192.take (coreResources192 39).q).drop 0 := by
  decide +kernel

theorem coreCheck192_39 :
    ∀ c : Fin 4, (coreChunks192_39 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 39)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_39_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_39_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_39_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_39_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten192_39
#print axioms coreCheck192_39
end Erdos883Verified
