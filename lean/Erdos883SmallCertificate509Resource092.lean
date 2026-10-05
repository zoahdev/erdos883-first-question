import Erdos883SmallCertificate509Data
import Erdos883SmallCertificate509Resource092Chunk000
import Erdos883SmallCertificate509Resource092Chunk001
import Erdos883SmallCertificate509Resource092Chunk002
import Erdos883SmallCertificate509Resource092Chunk003
import Erdos883SmallCertificate509Resource092Chunk004
import Erdos883SmallCertificate509Resource092Chunk005
import Erdos883SmallCertificate509Resource092Chunk006
import Erdos883SmallCertificate509Resource092Chunk007
import Erdos883SmallCertificate509Resource092Chunk008
import Erdos883SmallCertificate509Resource092Chunk009
import Erdos883SmallCertificate509Resource092Chunk010
import Erdos883SmallCertificate509Resource092Chunk011
import Erdos883SmallCertificate509Resource092Chunk012
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_92 :
    (List.ofFn coreChunks509_92).flatten =
      (coreData509.take (coreResources509 92).q).drop 0 := by
  decide +kernel

theorem coreCheck509_92 :
    ∀ c : Fin 13, (coreChunks509_92 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 92)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_92_12, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten509_92
#print axioms coreCheck509_92
end Erdos883Verified
