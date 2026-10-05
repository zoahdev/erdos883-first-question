import Erdos883SmallCertificate1100Data
import Erdos883SmallCertificate1100Resource204Chunk000
import Erdos883SmallCertificate1100Resource204Chunk001
import Erdos883SmallCertificate1100Resource204Chunk002
import Erdos883SmallCertificate1100Resource204Chunk003
import Erdos883SmallCertificate1100Resource204Chunk004
import Erdos883SmallCertificate1100Resource204Chunk005
import Erdos883SmallCertificate1100Resource204Chunk006
import Erdos883SmallCertificate1100Resource204Chunk007
import Erdos883SmallCertificate1100Resource204Chunk008
import Erdos883SmallCertificate1100Resource204Chunk009
import Erdos883SmallCertificate1100Resource204Chunk010
import Erdos883SmallCertificate1100Resource204Chunk011
import Erdos883SmallCertificate1100Resource204Chunk012
import Erdos883SmallCertificate1100Resource204Chunk013
import Erdos883SmallCertificate1100Resource204Chunk014
import Erdos883SmallCertificate1100Resource204Chunk015
import Erdos883SmallCertificate1100Resource204Chunk016
import Erdos883SmallCertificate1100Resource204Chunk017
import Erdos883SmallCertificate1100Resource204Chunk018
import Erdos883SmallCertificate1100Resource204Chunk019
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_204 :
    (List.ofFn coreChunks1100_204).flatten =
      (coreData1100.take (coreResources1100 204).q).drop 0 := by
  decide +kernel

theorem coreCheck1100_204 :
    ∀ c : Fin 20, (coreChunks1100_204 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 204)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_16, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_17, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_18, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_204_19, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1100_204
#print axioms coreCheck1100_204
end Erdos883Verified
