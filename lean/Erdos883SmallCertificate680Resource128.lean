import Erdos883SmallCertificate680Data
import Erdos883SmallCertificate680Resource128Chunk000
import Erdos883SmallCertificate680Resource128Chunk001
import Erdos883SmallCertificate680Resource128Chunk002
import Erdos883SmallCertificate680Resource128Chunk003
import Erdos883SmallCertificate680Resource128Chunk004
import Erdos883SmallCertificate680Resource128Chunk005
import Erdos883SmallCertificate680Resource128Chunk006
import Erdos883SmallCertificate680Resource128Chunk007
import Erdos883SmallCertificate680Resource128Chunk008
import Erdos883SmallCertificate680Resource128Chunk009
import Erdos883SmallCertificate680Resource128Chunk010
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_128 :
    (List.ofFn coreChunks680_128).flatten =
      (coreData680.take (coreResources680 128).q).drop 0 := by
  decide +kernel

theorem coreCheck680_128 :
    ∀ c : Fin 11, (coreChunks680_128 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 128)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_128_10, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten680_128
#print axioms coreCheck680_128
end Erdos883Verified
