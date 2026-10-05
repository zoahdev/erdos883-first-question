import Erdos883SmallCertificate680Data
import Erdos883SmallCertificate680Resource125Chunk000
import Erdos883SmallCertificate680Resource125Chunk001
import Erdos883SmallCertificate680Resource125Chunk002
import Erdos883SmallCertificate680Resource125Chunk003
import Erdos883SmallCertificate680Resource125Chunk004
import Erdos883SmallCertificate680Resource125Chunk005
import Erdos883SmallCertificate680Resource125Chunk006
import Erdos883SmallCertificate680Resource125Chunk007
import Erdos883SmallCertificate680Resource125Chunk008
import Erdos883SmallCertificate680Resource125Chunk009
import Erdos883SmallCertificate680Resource125Chunk010
import Erdos883SmallCertificate680Resource125Chunk011
import Erdos883SmallCertificate680Resource125Chunk012
import Erdos883SmallCertificate680Resource125Chunk013
import Erdos883SmallCertificate680Resource125Chunk014
import Erdos883SmallCertificate680Resource125Chunk015
import Erdos883SmallCertificate680Resource125Chunk016
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_125 :
    (List.ofFn coreChunks680_125).flatten =
      (coreData680.take (coreResources680 125).q).drop 0 := by
  decide +kernel

theorem coreCheck680_125 :
    ∀ c : Fin 17, (coreChunks680_125 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 125)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_15, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_125_16, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten680_125
#print axioms coreCheck680_125
end Erdos883Verified
