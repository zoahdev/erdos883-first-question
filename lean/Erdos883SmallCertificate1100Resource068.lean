import Erdos883SmallCertificate1100Data
import Erdos883SmallCertificate1100Resource068Chunk000
import Erdos883SmallCertificate1100Resource068Chunk001
import Erdos883SmallCertificate1100Resource068Chunk002
import Erdos883SmallCertificate1100Resource068Chunk003
import Erdos883SmallCertificate1100Resource068Chunk004
import Erdos883SmallCertificate1100Resource068Chunk005
import Erdos883SmallCertificate1100Resource068Chunk006
import Erdos883SmallCertificate1100Resource068Chunk007
import Erdos883SmallCertificate1100Resource068Chunk008
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_68 :
    (List.ofFn coreChunks1100_68).flatten =
      (coreData1100.take (coreResources1100 68).q).drop 0 := by
  decide +kernel

theorem coreCheck1100_68 :
    ∀ c : Fin 9, (coreChunks1100_68 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 68)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk1100_68_8, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten1100_68
#print axioms coreCheck1100_68
end Erdos883Verified
