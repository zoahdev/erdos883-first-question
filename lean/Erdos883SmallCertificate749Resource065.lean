import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_65 :
    (List.ofFn coreChunks749_65).flatten =
      (coreData749.take (coreResources749 65).q).drop 123 := by
  decide +kernel

theorem coreCheck749_65 :
    ∀ c : Fin 1, (coreChunks749_65 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 65)) = true := by
  decide +kernel
#print axioms coreFlatten749_65
#print axioms coreCheck749_65
end Erdos883Verified
