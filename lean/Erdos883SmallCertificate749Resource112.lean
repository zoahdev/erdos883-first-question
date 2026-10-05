import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_112 :
    (List.ofFn coreChunks749_112).flatten =
      (coreData749.take (coreResources749 112).q).drop 200 := by
  decide +kernel

theorem coreCheck749_112 :
    ∀ c : Fin 1, (coreChunks749_112 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 112)) = true := by
  decide +kernel
#print axioms coreFlatten749_112
#print axioms coreCheck749_112
end Erdos883Verified
