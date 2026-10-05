import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_34 :
    (List.ofFn coreChunks749_34).flatten =
      (coreData749.take (coreResources749 34).q).drop 160 := by
  decide +kernel

theorem coreCheck749_34 :
    ∀ c : Fin 1, (coreChunks749_34 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 34)) = true := by
  decide +kernel
#print axioms coreFlatten749_34
#print axioms coreCheck749_34
end Erdos883Verified
