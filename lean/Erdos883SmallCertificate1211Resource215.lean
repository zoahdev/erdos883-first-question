import Erdos883SmallCertificate1211Data
import Erdos883SmallCertificate1211Resource215Chunk000
import Erdos883SmallCertificate1211Resource215Chunk001
import Erdos883SmallCertificate1211Resource215Chunk002
import Erdos883SmallCertificate1211Resource215Chunk003
import Erdos883SmallCertificate1211Resource215Chunk004
import Erdos883SmallCertificate1211Resource215Chunk005
import Erdos883SmallCertificate1211Resource215Chunk006
import Erdos883SmallCertificate1211Resource215Chunk007
import Erdos883SmallCertificate1211Resource215Chunk008
import Erdos883SmallCertificate1211Resource215Chunk009
import Erdos883SmallCertificate1211Resource215Chunk010
import Erdos883SmallCertificate1211Resource215Chunk011
import Erdos883SmallCertificate1211Resource215Chunk012
import Erdos883SmallCertificate1211Resource215Chunk013
import Erdos883SmallCertificate1211Resource215Chunk014
import Erdos883SmallCertificate1211Resource215Chunk015
import Erdos883SmallCertificate1211Resource215Chunk016
import Erdos883SmallCertificate1211Resource215Chunk017
import Erdos883SmallCertificate1211Resource215Chunk018
import Erdos883SmallCertificate1211Resource215Chunk019
import Erdos883SmallCertificate1211Resource215Chunk020
import Erdos883SmallCertificate1211Resource215Chunk021
import Erdos883SmallCertificate1211Resource215Chunk022
import Erdos883SmallCertificate1211Resource215Chunk023
import Erdos883SmallCertificate1211Resource215Chunk024
import Erdos883SmallCertificate1211Resource215Chunk025
import Erdos883SmallCertificate1211Resource215Chunk026
import Erdos883SmallCertificate1211Resource215Chunk027
import Erdos883SmallCertificate1211Resource215Chunk028
import Erdos883SmallCertificate1211Resource215Chunk029
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_215 :
    (List.ofFn coreChunks1211_215).flatten =
      (coreData1211.take (coreResources1211 215).q).drop 0 := by
  decide +kernel

theorem coreCheck1211_215 :
    ∀ c : Fin 30, (coreChunks1211_215 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 215)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_19, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_20, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_21, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_22, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_23, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_24, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_25, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_26, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_27, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_28, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_215_29, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1211_215
#print axioms coreCheck1211_215
end Erdos883Verified
