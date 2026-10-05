import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_134 :
    (List.ofFn coreChunks749_134).flatten =
      (coreData749.take (coreResources749 134).q).drop 312 := by
  decide +kernel

theorem coreCheck749_134 :
    ∀ c : Fin 1, (coreChunks749_134 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 134)) = true := by
  decide +kernel
#print axioms coreFlatten749_134
#print axioms coreCheck749_134
end Erdos883Verified
