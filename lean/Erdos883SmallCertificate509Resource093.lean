import Erdos883SmallCertificate509Data
import Erdos883SmallCertificate509Resource093Chunk000
import Erdos883SmallCertificate509Resource093Chunk001
import Erdos883SmallCertificate509Resource093Chunk002
import Erdos883SmallCertificate509Resource093Chunk003
import Erdos883SmallCertificate509Resource093Chunk004
import Erdos883SmallCertificate509Resource093Chunk005
import Erdos883SmallCertificate509Resource093Chunk006
import Erdos883SmallCertificate509Resource093Chunk007
import Erdos883SmallCertificate509Resource093Chunk008
import Erdos883SmallCertificate509Resource093Chunk009
import Erdos883SmallCertificate509Resource093Chunk010
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_93 :
    (List.ofFn coreChunks509_93).flatten =
      (coreData509.take (coreResources509 93).q).drop 0 := by
  decide +kernel

theorem coreCheck509_93 :
    ∀ c : Fin 11, (coreChunks509_93 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 93)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_93_10, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten509_93
#print axioms coreCheck509_93
end Erdos883Verified
