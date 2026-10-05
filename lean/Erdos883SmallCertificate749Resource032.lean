import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_32 :
    (List.ofFn coreChunks749_32).flatten =
      (coreData749.take (coreResources749 32).q).drop 158 := by
  decide +kernel

theorem coreCheck749_32 :
    ∀ c : Fin 1, (coreChunks749_32 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 32)) = true := by
  decide +kernel
#print axioms coreFlatten749_32
#print axioms coreCheck749_32
end Erdos883Verified
