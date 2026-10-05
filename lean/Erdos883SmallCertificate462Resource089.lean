import Erdos883SmallCertificate462Data
import Erdos883SmallCertificate462Resource089Chunk000
import Erdos883SmallCertificate462Resource089Chunk001
import Erdos883SmallCertificate462Resource089Chunk002
import Erdos883SmallCertificate462Resource089Chunk003
import Erdos883SmallCertificate462Resource089Chunk004
import Erdos883SmallCertificate462Resource089Chunk005
import Erdos883SmallCertificate462Resource089Chunk006
import Erdos883SmallCertificate462Resource089Chunk007
import Erdos883SmallCertificate462Resource089Chunk008
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_89 :
    (List.ofFn coreChunks462_89).flatten =
      (coreData462.take (coreResources462 89).q).drop 0 := by
  decide +kernel

theorem coreCheck462_89 :
    ∀ c : Fin 9, (coreChunks462_89 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 89)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_89_8, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten462_89
#print axioms coreCheck462_89
end Erdos883Verified
