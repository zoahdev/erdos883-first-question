import Erdos883SmallCertificate1211Data
import Erdos883SmallCertificate1211Resource083Chunk000
import Erdos883SmallCertificate1211Resource083Chunk001
import Erdos883SmallCertificate1211Resource083Chunk002
import Erdos883SmallCertificate1211Resource083Chunk003
import Erdos883SmallCertificate1211Resource083Chunk004
import Erdos883SmallCertificate1211Resource083Chunk005
import Erdos883SmallCertificate1211Resource083Chunk006
import Erdos883SmallCertificate1211Resource083Chunk007
import Erdos883SmallCertificate1211Resource083Chunk008
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1211_83 :
    (List.ofFn coreChunks1211_83).flatten =
      (coreData1211.take (coreResources1211 83).q).drop 0 := by
  decide +kernel

theorem coreCheck1211_83 :
    ∀ c : Fin 9, (coreChunks1211_83 c).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 83)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1211_83_8, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1211_83
#print axioms coreCheck1211_83
end Erdos883Verified
