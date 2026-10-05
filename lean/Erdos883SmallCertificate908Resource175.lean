import Erdos883SmallCertificate908Data
import Erdos883SmallCertificate908Resource175Chunk000
import Erdos883SmallCertificate908Resource175Chunk001
import Erdos883SmallCertificate908Resource175Chunk002
import Erdos883SmallCertificate908Resource175Chunk003
import Erdos883SmallCertificate908Resource175Chunk004
import Erdos883SmallCertificate908Resource175Chunk005
import Erdos883SmallCertificate908Resource175Chunk006
import Erdos883SmallCertificate908Resource175Chunk007
import Erdos883SmallCertificate908Resource175Chunk008
import Erdos883SmallCertificate908Resource175Chunk009
import Erdos883SmallCertificate908Resource175Chunk010
import Erdos883SmallCertificate908Resource175Chunk011
import Erdos883SmallCertificate908Resource175Chunk012
import Erdos883SmallCertificate908Resource175Chunk013
import Erdos883SmallCertificate908Resource175Chunk014
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_175 :
    (List.ofFn coreChunks908_175).flatten =
      (coreData908.take (coreResources908 175).q).drop 0 := by
  decide +kernel

theorem coreCheck908_175 :
    ∀ c : Fin 15, (coreChunks908_175 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 175)) = true := by
  exact (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_0, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_1, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_2, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_3, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_4, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_5, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_6, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_7, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_8, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_9, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_10, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_11, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_12, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_13, (Fin.forall_fin_succ.mpr ⟨coreCheckChunk908_175_14, (by intro c; exact Fin.elim0 c)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
#print axioms coreFlatten908_175
#print axioms coreCheck908_175
end Erdos883Verified
