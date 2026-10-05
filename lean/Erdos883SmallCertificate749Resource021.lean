import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_21 :
    (List.ofFn coreChunks749_21).flatten =
      (coreData749.take (coreResources749 21).q).drop 144 := by
  decide +kernel

theorem coreCheck749_21 :
    ∀ c : Fin 1, (coreChunks749_21 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 21)) = true := by
  decide +kernel
#print axioms coreFlatten749_21
#print axioms coreCheck749_21
end Erdos883Verified
