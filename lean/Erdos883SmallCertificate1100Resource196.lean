import Erdos883SmallCertificate1100Data
import Erdos883SmallCertificate1100Resource196Chunk000
import Erdos883SmallCertificate1100Resource196Chunk001
import Erdos883SmallCertificate1100Resource196Chunk002
import Erdos883SmallCertificate1100Resource196Chunk003
import Erdos883SmallCertificate1100Resource196Chunk004
import Erdos883SmallCertificate1100Resource196Chunk005
import Erdos883SmallCertificate1100Resource196Chunk006
import Erdos883SmallCertificate1100Resource196Chunk007
import Erdos883SmallCertificate1100Resource196Chunk008
import Erdos883SmallCertificate1100Resource196Chunk009
import Erdos883SmallCertificate1100Resource196Chunk010
import Erdos883SmallCertificate1100Resource196Chunk011
import Erdos883SmallCertificate1100Resource196Chunk012
import Erdos883SmallCertificate1100Resource196Chunk013
import Erdos883SmallCertificate1100Resource196Chunk014
import Erdos883SmallCertificate1100Resource196Chunk015
import Erdos883SmallCertificate1100Resource196Chunk016
import Erdos883SmallCertificate1100Resource196Chunk017
import Erdos883SmallCertificate1100Resource196Chunk018
import Erdos883SmallCertificate1100Resource196Chunk019
import Erdos883SmallCertificate1100Resource196Chunk020
import Erdos883SmallCertificate1100Resource196Chunk021
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_196 :
    (List.ofFn coreChunks1100_196).flatten =
      (coreData1100.take (coreResources1100 196).q).drop 0 := by
  decide +kernel

theorem coreCheck1100_196 :
    ∀ c : Fin 22, (coreChunks1100_196 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 196)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_19, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_20, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_196_21, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1100_196
#print axioms coreCheck1100_196
end Erdos883Verified
