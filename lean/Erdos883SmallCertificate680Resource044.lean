import Erdos883SmallCertificate680Data
import Erdos883SmallCertificate680Resource044Chunk000
import Erdos883SmallCertificate680Resource044Chunk001
import Erdos883SmallCertificate680Resource044Chunk002
import Erdos883SmallCertificate680Resource044Chunk003
import Erdos883SmallCertificate680Resource044Chunk004
import Erdos883SmallCertificate680Resource044Chunk005
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_44 :
    (List.ofFn coreChunks680_44).flatten =
      (coreData680.take (coreResources680 44).q).drop 0 := by
  decide +kernel

theorem coreCheck680_44 :
    ∀ c : Fin 6, (coreChunks680_44 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 44)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_44_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_44_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_44_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_44_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_44_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk680_44_5, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten680_44
#print axioms coreCheck680_44
end Erdos883Verified
