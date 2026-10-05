import Erdos883SmallCertificate999Data
import Erdos883SmallCertificate999Resource186Chunk000
import Erdos883SmallCertificate999Resource186Chunk001
import Erdos883SmallCertificate999Resource186Chunk002
import Erdos883SmallCertificate999Resource186Chunk003
import Erdos883SmallCertificate999Resource186Chunk004
import Erdos883SmallCertificate999Resource186Chunk005
import Erdos883SmallCertificate999Resource186Chunk006
import Erdos883SmallCertificate999Resource186Chunk007
import Erdos883SmallCertificate999Resource186Chunk008
import Erdos883SmallCertificate999Resource186Chunk009
import Erdos883SmallCertificate999Resource186Chunk010
import Erdos883SmallCertificate999Resource186Chunk011
import Erdos883SmallCertificate999Resource186Chunk012
import Erdos883SmallCertificate999Resource186Chunk013
import Erdos883SmallCertificate999Resource186Chunk014
import Erdos883SmallCertificate999Resource186Chunk015
import Erdos883SmallCertificate999Resource186Chunk016
import Erdos883SmallCertificate999Resource186Chunk017
import Erdos883SmallCertificate999Resource186Chunk018
import Erdos883SmallCertificate999Resource186Chunk019
import Erdos883SmallCertificate999Resource186Chunk020
import Erdos883SmallCertificate999Resource186Chunk021
import Erdos883SmallCertificate999Resource186Chunk022
import Erdos883SmallCertificate999Resource186Chunk023
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_186 :
    (List.ofFn coreChunks999_186).flatten =
      (coreData999.take (coreResources999 186).q).drop 0 := by
  decide +kernel

theorem coreCheck999_186 :
    ∀ c : Fin 24, (coreChunks999_186 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 186)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_19, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_20, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_21, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_22, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_186_23, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten999_186
#print axioms coreCheck999_186
end Erdos883Verified
