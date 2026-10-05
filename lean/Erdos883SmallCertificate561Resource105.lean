import Erdos883SmallCertificate561Data
import Erdos883SmallCertificate561Resource105Chunk000
import Erdos883SmallCertificate561Resource105Chunk001
import Erdos883SmallCertificate561Resource105Chunk002
import Erdos883SmallCertificate561Resource105Chunk003
import Erdos883SmallCertificate561Resource105Chunk004
import Erdos883SmallCertificate561Resource105Chunk005
import Erdos883SmallCertificate561Resource105Chunk006
import Erdos883SmallCertificate561Resource105Chunk007
import Erdos883SmallCertificate561Resource105Chunk008
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten561_105 :
    (List.ofFn coreChunks561_105).flatten =
      (coreData561.take (coreResources561 105).q).drop 0 := by
  decide +kernel

theorem coreCheck561_105 :
    ∀ c : Fin 9, (coreChunks561_105 c).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 105)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk561_105_8, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten561_105
#print axioms coreCheck561_105
end Erdos883Verified
