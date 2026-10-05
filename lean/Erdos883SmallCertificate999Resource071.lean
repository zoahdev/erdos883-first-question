import Erdos883SmallCertificate999Data
import Erdos883SmallCertificate999Resource071Chunk000
import Erdos883SmallCertificate999Resource071Chunk001
import Erdos883SmallCertificate999Resource071Chunk002
import Erdos883SmallCertificate999Resource071Chunk003
import Erdos883SmallCertificate999Resource071Chunk004
import Erdos883SmallCertificate999Resource071Chunk005
import Erdos883SmallCertificate999Resource071Chunk006
import Erdos883SmallCertificate999Resource071Chunk007
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_71 :
    (List.ofFn coreChunks999_71).flatten =
      (coreData999.take (coreResources999 71).q).drop 0 := by
  decide +kernel

theorem coreCheck999_71 :
    ∀ c : Fin 8, (coreChunks999_71 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 71)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_71_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_71_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_71_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_71_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_71_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_71_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_71_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_71_7, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten999_71
#print axioms coreCheck999_71
end Erdos883Verified
