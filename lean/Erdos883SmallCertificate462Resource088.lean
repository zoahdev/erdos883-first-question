import Erdos883SmallCertificate462Data
import Erdos883SmallCertificate462Resource088Chunk000
import Erdos883SmallCertificate462Resource088Chunk001
import Erdos883SmallCertificate462Resource088Chunk002
import Erdos883SmallCertificate462Resource088Chunk003
import Erdos883SmallCertificate462Resource088Chunk004
import Erdos883SmallCertificate462Resource088Chunk005
import Erdos883SmallCertificate462Resource088Chunk006
import Erdos883SmallCertificate462Resource088Chunk007
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_88 :
    (List.ofFn coreChunks462_88).flatten =
      (coreData462.take (coreResources462 88).q).drop 0 := by
  decide +kernel

theorem coreCheck462_88 :
    ∀ c : Fin 8, (coreChunks462_88 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 88)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_88_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_88_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_88_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_88_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_88_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_88_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_88_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_88_7, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten462_88
#print axioms coreCheck462_88
end Erdos883Verified
