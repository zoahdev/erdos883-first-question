import Erdos883SmallCertificate103Data
import Erdos883SmallCertificate103Resource020Chunk000
import Erdos883SmallCertificate103Resource020Chunk001
import Erdos883SmallCertificate103Resource020Chunk002
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_20 :
    (List.ofFn coreChunks103_20).flatten =
      (coreData103.take (coreResources103 20).q).drop 0 := by
  decide +kernel

theorem coreCheck103_20 :
    ∀ c : Fin 3, (coreChunks103_20 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 20)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk103_20_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk103_20_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk103_20_2, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)
#print axioms coreFlatten103_20
#print axioms coreCheck103_20
end Erdos883Verified
