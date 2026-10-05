import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_139 :
    (List.ofFn coreChunks749_139).flatten =
      (coreData749.take (coreResources749 139).q).drop 323 := by
  decide +kernel

theorem coreCheck749_139 :
    ∀ c : Fin 1, (coreChunks749_139 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 139)) = true := by
  decide +kernel
#print axioms coreFlatten749_139
#print axioms coreCheck749_139
end Erdos883Verified
