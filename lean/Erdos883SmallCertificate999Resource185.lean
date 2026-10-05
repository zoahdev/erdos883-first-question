import Erdos883SmallCertificate999Data
import Erdos883SmallCertificate999Resource185Chunk000
import Erdos883SmallCertificate999Resource185Chunk001
import Erdos883SmallCertificate999Resource185Chunk002
import Erdos883SmallCertificate999Resource185Chunk003
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_185 :
    (List.ofFn coreChunks999_185).flatten =
      (coreData999.take (coreResources999 185).q).drop 442 := by
  decide +kernel

theorem coreCheck999_185 :
    ∀ c : Fin 4, (coreChunks999_185 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 185)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_185_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_185_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_185_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_185_3, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)
#print axioms coreFlatten999_185
#print axioms coreCheck999_185
end Erdos883Verified
