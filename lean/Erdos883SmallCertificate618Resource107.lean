import Erdos883SmallCertificate618Data
import Erdos883SmallCertificate618Resource107Chunk000
import Erdos883SmallCertificate618Resource107Chunk001
import Erdos883SmallCertificate618Resource107Chunk002
import Erdos883SmallCertificate618Resource107Chunk003
import Erdos883SmallCertificate618Resource107Chunk004
import Erdos883SmallCertificate618Resource107Chunk005
import Erdos883SmallCertificate618Resource107Chunk006
import Erdos883SmallCertificate618Resource107Chunk007
import Erdos883SmallCertificate618Resource107Chunk008
import Erdos883SmallCertificate618Resource107Chunk009
import Erdos883SmallCertificate618Resource107Chunk010
import Erdos883SmallCertificate618Resource107Chunk011
import Erdos883SmallCertificate618Resource107Chunk012
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_107 :
    (List.ofFn coreChunks618_107).flatten =
      (coreData618.take (coreResources618 107).q).drop 0 := by
  decide +kernel

theorem coreCheck618_107 :
    ∀ c : Fin 13, (coreChunks618_107 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 107)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk618_107_12, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten618_107
#print axioms coreCheck618_107
end Erdos883Verified
