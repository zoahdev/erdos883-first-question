import Erdos883SmallCertificate908Data
import Erdos883SmallCertificate908Resource176Chunk000
import Erdos883SmallCertificate908Resource176Chunk001
import Erdos883SmallCertificate908Resource176Chunk002
import Erdos883SmallCertificate908Resource176Chunk003
import Erdos883SmallCertificate908Resource176Chunk004
import Erdos883SmallCertificate908Resource176Chunk005
import Erdos883SmallCertificate908Resource176Chunk006
import Erdos883SmallCertificate908Resource176Chunk007
import Erdos883SmallCertificate908Resource176Chunk008
import Erdos883SmallCertificate908Resource176Chunk009
import Erdos883SmallCertificate908Resource176Chunk010
import Erdos883SmallCertificate908Resource176Chunk011
import Erdos883SmallCertificate908Resource176Chunk012
import Erdos883SmallCertificate908Resource176Chunk013
import Erdos883SmallCertificate908Resource176Chunk014
import Erdos883SmallCertificate908Resource176Chunk015
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_176 :
    (List.ofFn coreChunks908_176).flatten =
      (coreData908.take (coreResources908 176).q).drop 0 := by
  decide +kernel

theorem coreCheck908_176 :
    ∀ c : Fin 16, (coreChunks908_176 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 176)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_14, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_176_15, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten908_176
#print axioms coreCheck908_176
end Erdos883Verified
