import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_45 :
    (List.ofFn coreChunks749_45).flatten =
      (coreData749.take (coreResources749 45).q).drop 178 := by
  decide +kernel

theorem coreCheck749_45 :
    ∀ c : Fin 1, (coreChunks749_45 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 45)) = true := by
  decide +kernel
#print axioms coreFlatten749_45
#print axioms coreCheck749_45
end Erdos883Verified
