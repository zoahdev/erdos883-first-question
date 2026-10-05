import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_138 :
    (List.ofFn coreChunks749_138).flatten =
      (coreData749.take (coreResources749 138).q).drop 322 := by
  decide +kernel

theorem coreCheck749_138 :
    ∀ c : Fin 1, (coreChunks749_138 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 138)) = true := by
  decide +kernel
#print axioms coreFlatten749_138
#print axioms coreCheck749_138
end Erdos883Verified
