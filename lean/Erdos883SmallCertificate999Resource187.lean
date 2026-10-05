import Erdos883SmallCertificate999Data
import Erdos883SmallCertificate999Resource187Chunk000
import Erdos883SmallCertificate999Resource187Chunk001
import Erdos883SmallCertificate999Resource187Chunk002
import Erdos883SmallCertificate999Resource187Chunk003
import Erdos883SmallCertificate999Resource187Chunk004
import Erdos883SmallCertificate999Resource187Chunk005
import Erdos883SmallCertificate999Resource187Chunk006
import Erdos883SmallCertificate999Resource187Chunk007
import Erdos883SmallCertificate999Resource187Chunk008
import Erdos883SmallCertificate999Resource187Chunk009
import Erdos883SmallCertificate999Resource187Chunk010
import Erdos883SmallCertificate999Resource187Chunk011
import Erdos883SmallCertificate999Resource187Chunk012
import Erdos883SmallCertificate999Resource187Chunk013
import Erdos883SmallCertificate999Resource187Chunk014
import Erdos883SmallCertificate999Resource187Chunk015
import Erdos883SmallCertificate999Resource187Chunk016
import Erdos883SmallCertificate999Resource187Chunk017
import Erdos883SmallCertificate999Resource187Chunk018
import Erdos883SmallCertificate999Resource187Chunk019
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_187 :
    (List.ofFn coreChunks999_187).flatten =
      (coreData999.take (coreResources999 187).q).drop 0 := by
  decide +kernel

theorem coreCheck999_187 :
    ∀ c : Fin 20, (coreChunks999_187 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 187)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk999_187_19, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten999_187
#print axioms coreCheck999_187
end Erdos883Verified
