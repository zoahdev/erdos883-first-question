import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_33 :
    (List.ofFn coreChunks749_33).flatten =
      (coreData749.take (coreResources749 33).q).drop 159 := by
  decide +kernel

theorem coreCheck749_33 :
    ∀ c : Fin 1, (coreChunks749_33 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 33)) = true := by
  decide +kernel
#print axioms coreFlatten749_33
#print axioms coreCheck749_33
end Erdos883Verified
