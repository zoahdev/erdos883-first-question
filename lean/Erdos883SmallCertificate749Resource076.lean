import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_76 :
    (List.ofFn coreChunks749_76).flatten =
      (coreData749.take (coreResources749 76).q).drop 138 := by
  decide +kernel

theorem coreCheck749_76 :
    ∀ c : Fin 1, (coreChunks749_76 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 76)) = true := by
  decide +kernel
#print axioms coreFlatten749_76
#print axioms coreCheck749_76
end Erdos883Verified
