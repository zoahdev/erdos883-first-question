import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_110 :
    (List.ofFn coreChunks749_110).flatten =
      (coreData749.take (coreResources749 110).q).drop 195 := by
  decide +kernel

theorem coreCheck749_110 :
    ∀ c : Fin 1, (coreChunks749_110 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 110)) = true := by
  decide +kernel
#print axioms coreFlatten749_110
#print axioms coreCheck749_110
end Erdos883Verified
