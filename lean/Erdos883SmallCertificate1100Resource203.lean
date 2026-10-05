import Erdos883SmallCertificate1100Data
import Erdos883SmallCertificate1100Resource203Chunk000
import Erdos883SmallCertificate1100Resource203Chunk001
import Erdos883SmallCertificate1100Resource203Chunk002
import Erdos883SmallCertificate1100Resource203Chunk003
import Erdos883SmallCertificate1100Resource203Chunk004
import Erdos883SmallCertificate1100Resource203Chunk005
import Erdos883SmallCertificate1100Resource203Chunk006
import Erdos883SmallCertificate1100Resource203Chunk007
import Erdos883SmallCertificate1100Resource203Chunk008
import Erdos883SmallCertificate1100Resource203Chunk009
import Erdos883SmallCertificate1100Resource203Chunk010
import Erdos883SmallCertificate1100Resource203Chunk011
import Erdos883SmallCertificate1100Resource203Chunk012
import Erdos883SmallCertificate1100Resource203Chunk013
import Erdos883SmallCertificate1100Resource203Chunk014
import Erdos883SmallCertificate1100Resource203Chunk015
import Erdos883SmallCertificate1100Resource203Chunk016
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_203 :
    (List.ofFn coreChunks1100_203).flatten =
      (coreData1100.take (coreResources1100 203).q).drop 0 := by
  decide +kernel

theorem coreCheck1100_203 :
    ∀ c : Fin 17, (coreChunks1100_203 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 203)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_203_16, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1100_203
#print axioms coreCheck1100_203
end Erdos883Verified
