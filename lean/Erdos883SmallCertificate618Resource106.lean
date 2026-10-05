import Erdos883SmallCertificate618Data
import Erdos883SmallCertificate618Resource106Chunk000
import Erdos883SmallCertificate618Resource106Chunk001
import Erdos883SmallCertificate618Resource106Chunk002
import Erdos883SmallCertificate618Resource106Chunk003
import Erdos883SmallCertificate618Resource106Chunk004
import Erdos883SmallCertificate618Resource106Chunk005
import Erdos883SmallCertificate618Resource106Chunk006
import Erdos883SmallCertificate618Resource106Chunk007
import Erdos883SmallCertificate618Resource106Chunk008
import Erdos883SmallCertificate618Resource106Chunk009
import Erdos883SmallCertificate618Resource106Chunk010
import Erdos883SmallCertificate618Resource106Chunk011
import Erdos883SmallCertificate618Resource106Chunk012
import Erdos883SmallCertificate618Resource106Chunk013
import Erdos883SmallCertificate618Resource106Chunk014
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_106 :
    (List.ofFn coreChunks618_106).flatten =
      (coreData618.take (coreResources618 106).q).drop 0 := by
  decide +kernel

theorem coreCheck618_106 :
    ∀ c : Fin 15, (coreChunks618_106 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 106)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_106_14, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten618_106
#print axioms coreCheck618_106
end Erdos883Verified
