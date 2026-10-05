import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_46 :
    (List.ofFn coreChunks749_46).flatten =
      (coreData749.take (coreResources749 46).q).drop 180 := by
  decide +kernel

theorem coreCheck749_46 :
    ∀ c : Fin 1, (coreChunks749_46 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 46)) = true := by
  decide +kernel
#print axioms coreFlatten749_46
#print axioms coreCheck749_46
end Erdos883Verified
