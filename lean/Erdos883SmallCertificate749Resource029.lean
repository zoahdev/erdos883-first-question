import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_29 :
    (List.ofFn coreChunks749_29).flatten =
      (coreData749.take (coreResources749 29).q).drop 154 := by
  decide +kernel

theorem coreCheck749_29 :
    ∀ c : Fin 1, (coreChunks749_29 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 29)) = true := by
  decide +kernel
#print axioms coreFlatten749_29
#print axioms coreCheck749_29
end Erdos883Verified
