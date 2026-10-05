import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_47 :
    (List.ofFn coreChunks749_47).flatten =
      (coreData749.take (coreResources749 47).q).drop 182 := by
  decide +kernel

theorem coreCheck749_47 :
    ∀ c : Fin 1, (coreChunks749_47 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 47)) = true := by
  decide +kernel
#print axioms coreFlatten749_47
#print axioms coreCheck749_47
end Erdos883Verified
