import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_40 :
    (List.ofFn coreChunks749_40).flatten =
      (coreData749.take (coreResources749 40).q).drop 167 := by
  decide +kernel

theorem coreCheck749_40 :
    ∀ c : Fin 1, (coreChunks749_40 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 40)) = true := by
  decide +kernel
#print axioms coreFlatten749_40
#print axioms coreCheck749_40
end Erdos883Verified
