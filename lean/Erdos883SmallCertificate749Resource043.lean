import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_43 :
    (List.ofFn coreChunks749_43).flatten =
      (coreData749.take (coreResources749 43).q).drop 172 := by
  decide +kernel

theorem coreCheck749_43 :
    ∀ c : Fin 1, (coreChunks749_43 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 43)) = true := by
  decide +kernel
#print axioms coreFlatten749_43
#print axioms coreCheck749_43
end Erdos883Verified
