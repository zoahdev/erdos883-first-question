import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_115 :
    (List.ofFn coreChunks749_115).flatten =
      (coreData749.take (coreResources749 115).q).drop 214 := by
  decide +kernel

theorem coreCheck749_115 :
    ∀ c : Fin 1, (coreChunks749_115 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 115)) = true := by
  decide +kernel
#print axioms coreFlatten749_115
#print axioms coreCheck749_115
end Erdos883Verified
