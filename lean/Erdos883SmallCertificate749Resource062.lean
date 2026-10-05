import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_62 :
    (List.ofFn coreChunks749_62).flatten =
      (coreData749.take (coreResources749 62).q).drop 120 := by
  decide +kernel

theorem coreCheck749_62 :
    ∀ c : Fin 1, (coreChunks749_62 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 62)) = true := by
  decide +kernel
#print axioms coreFlatten749_62
#print axioms coreCheck749_62
end Erdos883Verified
