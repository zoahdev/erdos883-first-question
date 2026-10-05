import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_121 :
    (List.ofFn coreChunks749_121).flatten =
      (coreData749.take (coreResources749 121).q).drop 233 := by
  decide +kernel

theorem coreCheck749_121 :
    ∀ c : Fin 1, (coreChunks749_121 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 121)) = true := by
  decide +kernel
#print axioms coreFlatten749_121
#print axioms coreCheck749_121
end Erdos883Verified
