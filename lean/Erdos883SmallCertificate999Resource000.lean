import Erdos883SmallCertificate999Data
import Erdos883SmallCertificate999Resource000Chunk000
import Erdos883SmallCertificate999Resource000Chunk001
import Erdos883SmallCertificate999Resource000Chunk002
import Erdos883SmallCertificate999Resource000Chunk003
import Erdos883SmallCertificate999Resource000Chunk004
import Erdos883SmallCertificate999Resource000Chunk005
import Erdos883SmallCertificate999Resource000Chunk006
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_0 :
    (List.ofFn coreChunks999_0).flatten =
      (coreData999.take (coreResources999 0).q).drop 0 := by
  decide +kernel

theorem coreCheck999_0 :
    ∀ c : Fin 7, (coreChunks999_0 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 0)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_0_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_0_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_0_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_0_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_0_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_0_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_0_6, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten999_0
#print axioms coreCheck999_0
end Erdos883Verified
