import Erdos883SmallCertificate509Data
import Erdos883SmallCertificate509Resource096Chunk000
import Erdos883SmallCertificate509Resource096Chunk001
import Erdos883SmallCertificate509Resource096Chunk002
import Erdos883SmallCertificate509Resource096Chunk003
import Erdos883SmallCertificate509Resource096Chunk004
import Erdos883SmallCertificate509Resource096Chunk005
import Erdos883SmallCertificate509Resource096Chunk006
import Erdos883SmallCertificate509Resource096Chunk007
import Erdos883SmallCertificate509Resource096Chunk008
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_96 :
    (List.ofFn coreChunks509_96).flatten =
      (coreData509.take (coreResources509 96).q).drop 0 := by
  decide +kernel

theorem coreCheck509_96 :
    ∀ c : Fin 9, (coreChunks509_96 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 96)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk509_96_8, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten509_96
#print axioms coreCheck509_96
end Erdos883Verified
