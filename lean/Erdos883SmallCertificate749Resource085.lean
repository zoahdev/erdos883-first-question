import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_85 :
    (List.ofFn coreChunks749_85).flatten =
      (coreData749.take (coreResources749 85).q).drop 150 := by
  decide +kernel

theorem coreCheck749_85 :
    ∀ c : Fin 1, (coreChunks749_85 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 85)) = true := by
  decide +kernel
#print axioms coreFlatten749_85
#print axioms coreCheck749_85
end Erdos883Verified
