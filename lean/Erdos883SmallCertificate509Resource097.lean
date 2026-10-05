import Erdos883SmallCertificate509Data
import Erdos883SmallCertificate509Resource097Chunk000
import Erdos883SmallCertificate509Resource097Chunk001
import Erdos883SmallCertificate509Resource097Chunk002
import Erdos883SmallCertificate509Resource097Chunk003
import Erdos883SmallCertificate509Resource097Chunk004
import Erdos883SmallCertificate509Resource097Chunk005
import Erdos883SmallCertificate509Resource097Chunk006
import Erdos883SmallCertificate509Resource097Chunk007
import Erdos883SmallCertificate509Resource097Chunk008
import Erdos883SmallCertificate509Resource097Chunk009
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_97 :
    (List.ofFn coreChunks509_97).flatten =
      (coreData509.take (coreResources509 97).q).drop 0 := by
  decide +kernel

theorem coreCheck509_97 :
    ∀ c : Fin 10, (coreChunks509_97 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 97)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_97_9, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten509_97
#print axioms coreCheck509_97
end Erdos883Verified
