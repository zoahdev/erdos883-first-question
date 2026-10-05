import Erdos883SmallCertificate618Data
import Erdos883SmallCertificate618Resource109Chunk000
import Erdos883SmallCertificate618Resource109Chunk001
import Erdos883SmallCertificate618Resource109Chunk002
import Erdos883SmallCertificate618Resource109Chunk003
import Erdos883SmallCertificate618Resource109Chunk004
import Erdos883SmallCertificate618Resource109Chunk005
import Erdos883SmallCertificate618Resource109Chunk006
import Erdos883SmallCertificate618Resource109Chunk007
import Erdos883SmallCertificate618Resource109Chunk008
import Erdos883SmallCertificate618Resource109Chunk009
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_109 :
    (List.ofFn coreChunks618_109).flatten =
      (coreData618.take (coreResources618 109).q).drop 0 := by
  decide +kernel

theorem coreCheck618_109 :
    ∀ c : Fin 10, (coreChunks618_109 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 109)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_109_9, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten618_109
#print axioms coreCheck618_109
end Erdos883Verified
