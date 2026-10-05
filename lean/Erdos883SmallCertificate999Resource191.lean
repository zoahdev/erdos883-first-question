import Erdos883SmallCertificate999Data
import Erdos883SmallCertificate999Resource191Chunk000
import Erdos883SmallCertificate999Resource191Chunk001
import Erdos883SmallCertificate999Resource191Chunk002
import Erdos883SmallCertificate999Resource191Chunk003
import Erdos883SmallCertificate999Resource191Chunk004
import Erdos883SmallCertificate999Resource191Chunk005
import Erdos883SmallCertificate999Resource191Chunk006
import Erdos883SmallCertificate999Resource191Chunk007
import Erdos883SmallCertificate999Resource191Chunk008
import Erdos883SmallCertificate999Resource191Chunk009
import Erdos883SmallCertificate999Resource191Chunk010
import Erdos883SmallCertificate999Resource191Chunk011
import Erdos883SmallCertificate999Resource191Chunk012
import Erdos883SmallCertificate999Resource191Chunk013
import Erdos883SmallCertificate999Resource191Chunk014
import Erdos883SmallCertificate999Resource191Chunk015
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_191 :
    (List.ofFn coreChunks999_191).flatten =
      (coreData999.take (coreResources999 191).q).drop 0 := by
  decide +kernel

theorem coreCheck999_191 :
    ∀ c : Fin 16, (coreChunks999_191 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 191)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_191_15, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten999_191
#print axioms coreCheck999_191
end Erdos883Verified
