import Erdos883SmallCertificate680Data
import Erdos883SmallCertificate680Resource126Chunk000
import Erdos883SmallCertificate680Resource126Chunk001
import Erdos883SmallCertificate680Resource126Chunk002
import Erdos883SmallCertificate680Resource126Chunk003
import Erdos883SmallCertificate680Resource126Chunk004
import Erdos883SmallCertificate680Resource126Chunk005
import Erdos883SmallCertificate680Resource126Chunk006
import Erdos883SmallCertificate680Resource126Chunk007
import Erdos883SmallCertificate680Resource126Chunk008
import Erdos883SmallCertificate680Resource126Chunk009
import Erdos883SmallCertificate680Resource126Chunk010
import Erdos883SmallCertificate680Resource126Chunk011
import Erdos883SmallCertificate680Resource126Chunk012
import Erdos883SmallCertificate680Resource126Chunk013
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_126 :
    (List.ofFn coreChunks680_126).flatten =
      (coreData680.take (coreResources680 126).q).drop 0 := by
  decide +kernel

theorem coreCheck680_126 :
    ∀ c : Fin 14, (coreChunks680_126 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 126)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_126_13, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten680_126
#print axioms coreCheck680_126
end Erdos883Verified
