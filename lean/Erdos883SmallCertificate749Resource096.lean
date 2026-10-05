import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_96 :
    (List.ofFn coreChunks749_96).flatten =
      (coreData749.take (coreResources749 96).q).drop 167 := by
  decide +kernel

theorem coreCheck749_96 :
    ∀ c : Fin 1, (coreChunks749_96 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 96)) = true := by
  decide +kernel
#print axioms coreFlatten749_96
#print axioms coreCheck749_96
end Erdos883Verified
