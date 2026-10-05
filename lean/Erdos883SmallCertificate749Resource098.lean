import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_98 :
    (List.ofFn coreChunks749_98).flatten =
      (coreData749.take (coreResources749 98).q).drop 169 := by
  decide +kernel

theorem coreCheck749_98 :
    ∀ c : Fin 1, (coreChunks749_98 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 98)) = true := by
  decide +kernel
#print axioms coreFlatten749_98
#print axioms coreCheck749_98
end Erdos883Verified
