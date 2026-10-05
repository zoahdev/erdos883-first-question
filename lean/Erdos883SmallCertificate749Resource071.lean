import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_71 :
    (List.ofFn coreChunks749_71).flatten =
      (coreData749.take (coreResources749 71).q).drop 132 := by
  decide +kernel

theorem coreCheck749_71 :
    ∀ c : Fin 1, (coreChunks749_71 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 71)) = true := by
  decide +kernel
#print axioms coreFlatten749_71
#print axioms coreCheck749_71
end Erdos883Verified
