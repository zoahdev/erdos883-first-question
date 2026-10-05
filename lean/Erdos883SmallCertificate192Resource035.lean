import Erdos883SmallCertificate192Data
import Erdos883SmallCertificate192Resource035Chunk000
import Erdos883SmallCertificate192Resource035Chunk001
import Erdos883SmallCertificate192Resource035Chunk002
import Erdos883SmallCertificate192Resource035Chunk003
import Erdos883SmallCertificate192Resource035Chunk004
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten192_35 :
    (List.ofFn coreChunks192_35).flatten =
      (coreData192.take (coreResources192 35).q).drop 0 := by
  decide +kernel

theorem coreCheck192_35 :
    ∀ c : Fin 5, (coreChunks192_35 c).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 35)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_35_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_35_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_35_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_35_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk192_35_4, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten192_35
#print axioms coreCheck192_35
end Erdos883Verified
