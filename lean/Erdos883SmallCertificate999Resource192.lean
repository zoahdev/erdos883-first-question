import Erdos883SmallCertificate999Data
import Erdos883SmallCertificate999Resource192Chunk000
import Erdos883SmallCertificate999Resource192Chunk001
import Erdos883SmallCertificate999Resource192Chunk002
import Erdos883SmallCertificate999Resource192Chunk003
import Erdos883SmallCertificate999Resource192Chunk004
import Erdos883SmallCertificate999Resource192Chunk005
import Erdos883SmallCertificate999Resource192Chunk006
import Erdos883SmallCertificate999Resource192Chunk007
import Erdos883SmallCertificate999Resource192Chunk008
import Erdos883SmallCertificate999Resource192Chunk009
import Erdos883SmallCertificate999Resource192Chunk010
import Erdos883SmallCertificate999Resource192Chunk011
import Erdos883SmallCertificate999Resource192Chunk012
import Erdos883SmallCertificate999Resource192Chunk013
import Erdos883SmallCertificate999Resource192Chunk014
import Erdos883SmallCertificate999Resource192Chunk015
import Erdos883SmallCertificate999Resource192Chunk016
import Erdos883SmallCertificate999Resource192Chunk017
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_192 :
    (List.ofFn coreChunks999_192).flatten =
      (coreData999.take (coreResources999 192).q).drop 0 := by
  decide +kernel

theorem coreCheck999_192 :
    ∀ c : Fin 18, (coreChunks999_192 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 192)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_192_17, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten999_192
#print axioms coreCheck999_192
end Erdos883Verified
