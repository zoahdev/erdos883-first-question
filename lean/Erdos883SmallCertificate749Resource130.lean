import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_130 :
    (List.ofFn coreChunks749_130).flatten =
      (coreData749.take (coreResources749 130).q).drop 302 := by
  decide +kernel

theorem coreCheck749_130 :
    ∀ c : Fin 1, (coreChunks749_130 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 130)) = true := by
  decide +kernel
#print axioms coreFlatten749_130
#print axioms coreCheck749_130
end Erdos883Verified
