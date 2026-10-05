import Erdos883SmallCertificate1211Data
import Erdos883SmallCertificate1211Resource225Chunk000
import Erdos883SmallCertificate1211Resource225Chunk001
import Erdos883SmallCertificate1211Resource225Chunk002
import Erdos883SmallCertificate1211Resource225Chunk003
import Erdos883SmallCertificate1211Resource225Chunk004
import Erdos883SmallCertificate1211Resource225Chunk005
import Erdos883SmallCertificate1211Resource225Chunk006
import Erdos883SmallCertificate1211Resource225Chunk007
import Erdos883SmallCertificate1211Resource225Chunk008
import Erdos883SmallCertificate1211Resource225Chunk009
import Erdos883SmallCertificate1211Resource225Chunk010
import Erdos883SmallCertificate1211Resource225Chunk011
import Erdos883SmallCertificate1211Resource225Chunk012
import Erdos883SmallCertificate1211Resource225Chunk013
import Erdos883SmallCertificate1211Resource225Chunk014
import Erdos883SmallCertificate1211Resource225Chunk015
import Erdos883SmallCertificate1211Resource225Chunk016
import Erdos883SmallCertificate1211Resource225Chunk017
import Erdos883SmallCertificate1211Resource225Chunk018
import Erdos883SmallCertificate1211Resource225Chunk019
import Erdos883SmallCertificate1211Resource225Chunk020
import Erdos883SmallCertificate1211Resource225Chunk021
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_225 :
    (List.ofFn coreChunks1211_225).flatten =
      (coreData1211.take (coreResources1211 225).q).drop 0 := by
  decide +kernel

theorem coreCheck1211_225 :
    ∀ c : Fin 22, (coreChunks1211_225 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 225)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_19, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_20, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_225_21, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1211_225
#print axioms coreCheck1211_225
end Erdos883Verified
