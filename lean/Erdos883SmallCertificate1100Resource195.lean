import Erdos883SmallCertificate1100Data
import Erdos883SmallCertificate1100Resource195Chunk000
import Erdos883SmallCertificate1100Resource195Chunk001
import Erdos883SmallCertificate1100Resource195Chunk002
import Erdos883SmallCertificate1100Resource195Chunk003
import Erdos883SmallCertificate1100Resource195Chunk004
import Erdos883SmallCertificate1100Resource195Chunk005
import Erdos883SmallCertificate1100Resource195Chunk006
import Erdos883SmallCertificate1100Resource195Chunk007
import Erdos883SmallCertificate1100Resource195Chunk008
import Erdos883SmallCertificate1100Resource195Chunk009
import Erdos883SmallCertificate1100Resource195Chunk010
import Erdos883SmallCertificate1100Resource195Chunk011
import Erdos883SmallCertificate1100Resource195Chunk012
import Erdos883SmallCertificate1100Resource195Chunk013
import Erdos883SmallCertificate1100Resource195Chunk014
import Erdos883SmallCertificate1100Resource195Chunk015
import Erdos883SmallCertificate1100Resource195Chunk016
import Erdos883SmallCertificate1100Resource195Chunk017
import Erdos883SmallCertificate1100Resource195Chunk018
import Erdos883SmallCertificate1100Resource195Chunk019
import Erdos883SmallCertificate1100Resource195Chunk020
import Erdos883SmallCertificate1100Resource195Chunk021
import Erdos883SmallCertificate1100Resource195Chunk022
import Erdos883SmallCertificate1100Resource195Chunk023
import Erdos883SmallCertificate1100Resource195Chunk024
import Erdos883SmallCertificate1100Resource195Chunk025
import Erdos883SmallCertificate1100Resource195Chunk026
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_195 :
    (List.ofFn coreChunks1100_195).flatten =
      (coreData1100.take (coreResources1100 195).q).drop 0 := by
  decide +kernel

theorem coreCheck1100_195 :
    ∀ c : Fin 27, (coreChunks1100_195 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 195)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_19, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_20, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_21, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_22, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_23, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_24, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_25, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_195_26, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1100_195
#print axioms coreCheck1100_195
end Erdos883Verified
