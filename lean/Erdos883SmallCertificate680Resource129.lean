import Erdos883SmallCertificate680Data
import Erdos883SmallCertificate680Resource129Chunk000
import Erdos883SmallCertificate680Resource129Chunk001
import Erdos883SmallCertificate680Resource129Chunk002
import Erdos883SmallCertificate680Resource129Chunk003
import Erdos883SmallCertificate680Resource129Chunk004
import Erdos883SmallCertificate680Resource129Chunk005
import Erdos883SmallCertificate680Resource129Chunk006
import Erdos883SmallCertificate680Resource129Chunk007
import Erdos883SmallCertificate680Resource129Chunk008
import Erdos883SmallCertificate680Resource129Chunk009
import Erdos883SmallCertificate680Resource129Chunk010
import Erdos883SmallCertificate680Resource129Chunk011
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_129 :
    (List.ofFn coreChunks680_129).flatten =
      (coreData680.take (coreResources680 129).q).drop 0 := by
  decide +kernel

theorem coreCheck680_129 :
    ∀ c : Fin 12, (coreChunks680_129 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 129)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_129_11, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten680_129
#print axioms coreCheck680_129
end Erdos883Verified
