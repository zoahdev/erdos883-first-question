import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_6 :
    (List.ofFn coreChunks749_6).flatten =
      (coreData749.take (coreResources749 6).q).drop 95 := by
  decide +kernel

theorem coreCheck749_6 :
    ∀ c : Fin 1, (coreChunks749_6 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 6)) = true := by
  decide +kernel
#print axioms coreFlatten749_6
#print axioms coreCheck749_6
end Erdos883Verified
