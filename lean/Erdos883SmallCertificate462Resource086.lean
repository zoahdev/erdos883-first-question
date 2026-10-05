import Erdos883SmallCertificate462Data
import Erdos883SmallCertificate462Resource086Chunk000
import Erdos883SmallCertificate462Resource086Chunk001
import Erdos883SmallCertificate462Resource086Chunk002
import Erdos883SmallCertificate462Resource086Chunk003
import Erdos883SmallCertificate462Resource086Chunk004
import Erdos883SmallCertificate462Resource086Chunk005
import Erdos883SmallCertificate462Resource086Chunk006
import Erdos883SmallCertificate462Resource086Chunk007
import Erdos883SmallCertificate462Resource086Chunk008
import Erdos883SmallCertificate462Resource086Chunk009
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_86 :
    (List.ofFn coreChunks462_86).flatten =
      (coreData462.take (coreResources462 86).q).drop 0 := by
  decide +kernel

theorem coreCheck462_86 :
    ∀ c : Fin 10, (coreChunks462_86 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 86)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_86_9, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten462_86
#print axioms coreCheck462_86
end Erdos883Verified
