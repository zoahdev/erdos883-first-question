import Erdos883SmallCertificate1211Data
import Erdos883SmallCertificate1211Resource216Chunk000
import Erdos883SmallCertificate1211Resource216Chunk001
import Erdos883SmallCertificate1211Resource216Chunk002
import Erdos883SmallCertificate1211Resource216Chunk003
import Erdos883SmallCertificate1211Resource216Chunk004
import Erdos883SmallCertificate1211Resource216Chunk005
import Erdos883SmallCertificate1211Resource216Chunk006
import Erdos883SmallCertificate1211Resource216Chunk007
import Erdos883SmallCertificate1211Resource216Chunk008
import Erdos883SmallCertificate1211Resource216Chunk009
import Erdos883SmallCertificate1211Resource216Chunk010
import Erdos883SmallCertificate1211Resource216Chunk011
import Erdos883SmallCertificate1211Resource216Chunk012
import Erdos883SmallCertificate1211Resource216Chunk013
import Erdos883SmallCertificate1211Resource216Chunk014
import Erdos883SmallCertificate1211Resource216Chunk015
import Erdos883SmallCertificate1211Resource216Chunk016
import Erdos883SmallCertificate1211Resource216Chunk017
import Erdos883SmallCertificate1211Resource216Chunk018
import Erdos883SmallCertificate1211Resource216Chunk019
import Erdos883SmallCertificate1211Resource216Chunk020
import Erdos883SmallCertificate1211Resource216Chunk021
import Erdos883SmallCertificate1211Resource216Chunk022
import Erdos883SmallCertificate1211Resource216Chunk023
import Erdos883SmallCertificate1211Resource216Chunk024
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_216 :
    (List.ofFn coreChunks1211_216).flatten =
      (coreData1211.take (coreResources1211 216).q).drop 0 := by
  decide +kernel

theorem coreCheck1211_216 :
    ∀ c : Fin 25, (coreChunks1211_216 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 216)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_19, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_20, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_21, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_22, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_23, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_216_24, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1211_216
#print axioms coreCheck1211_216
end Erdos883Verified
