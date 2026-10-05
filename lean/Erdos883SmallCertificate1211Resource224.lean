import Erdos883SmallCertificate1211Data
import Erdos883SmallCertificate1211Resource224Chunk000
import Erdos883SmallCertificate1211Resource224Chunk001
import Erdos883SmallCertificate1211Resource224Chunk002
import Erdos883SmallCertificate1211Resource224Chunk003
import Erdos883SmallCertificate1211Resource224Chunk004
import Erdos883SmallCertificate1211Resource224Chunk005
import Erdos883SmallCertificate1211Resource224Chunk006
import Erdos883SmallCertificate1211Resource224Chunk007
import Erdos883SmallCertificate1211Resource224Chunk008
import Erdos883SmallCertificate1211Resource224Chunk009
import Erdos883SmallCertificate1211Resource224Chunk010
import Erdos883SmallCertificate1211Resource224Chunk011
import Erdos883SmallCertificate1211Resource224Chunk012
import Erdos883SmallCertificate1211Resource224Chunk013
import Erdos883SmallCertificate1211Resource224Chunk014
import Erdos883SmallCertificate1211Resource224Chunk015
import Erdos883SmallCertificate1211Resource224Chunk016
import Erdos883SmallCertificate1211Resource224Chunk017
import Erdos883SmallCertificate1211Resource224Chunk018
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_224 :
    (List.ofFn coreChunks1211_224).flatten =
      (coreData1211.take (coreResources1211 224).q).drop 0 := by
  decide +kernel

theorem coreCheck1211_224 :
    ∀ c : Fin 19, (coreChunks1211_224 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 224)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_224_18, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1211_224
#print axioms coreCheck1211_224
end Erdos883Verified
