import Erdos883SmallCertificate618Data
import Erdos883SmallCertificate618Resource110Chunk000
import Erdos883SmallCertificate618Resource110Chunk001
import Erdos883SmallCertificate618Resource110Chunk002
import Erdos883SmallCertificate618Resource110Chunk003
import Erdos883SmallCertificate618Resource110Chunk004
import Erdos883SmallCertificate618Resource110Chunk005
import Erdos883SmallCertificate618Resource110Chunk006
import Erdos883SmallCertificate618Resource110Chunk007
import Erdos883SmallCertificate618Resource110Chunk008
import Erdos883SmallCertificate618Resource110Chunk009
import Erdos883SmallCertificate618Resource110Chunk010
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_110 :
    (List.ofFn coreChunks618_110).flatten =
      (coreData618.take (coreResources618 110).q).drop 0 := by
  decide +kernel

theorem coreCheck618_110 :
    ∀ c : Fin 11, (coreChunks618_110 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 110)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_110_10, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten618_110
#print axioms coreCheck618_110
end Erdos883Verified
