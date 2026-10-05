import Erdos883SmallCertificate462Data
import Erdos883SmallCertificate462Resource085Chunk000
import Erdos883SmallCertificate462Resource085Chunk001
import Erdos883SmallCertificate462Resource085Chunk002
import Erdos883SmallCertificate462Resource085Chunk003
import Erdos883SmallCertificate462Resource085Chunk004
import Erdos883SmallCertificate462Resource085Chunk005
import Erdos883SmallCertificate462Resource085Chunk006
import Erdos883SmallCertificate462Resource085Chunk007
import Erdos883SmallCertificate462Resource085Chunk008
import Erdos883SmallCertificate462Resource085Chunk009
import Erdos883SmallCertificate462Resource085Chunk010
import Erdos883SmallCertificate462Resource085Chunk011
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten462_85 :
    (List.ofFn coreChunks462_85).flatten =
      (coreData462.take (coreResources462 85).q).drop 0 := by
  decide +kernel

theorem coreCheck462_85 :
    ∀ c : Fin 12, (coreChunks462_85 c).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 85)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk462_85_11, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten462_85
#print axioms coreCheck462_85
end Erdos883Verified
