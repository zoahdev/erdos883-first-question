import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_63 :
    (List.ofFn coreChunks749_63).flatten =
      (coreData749.take (coreResources749 63).q).drop 121 := by
  decide +kernel

theorem coreCheck749_63 :
    ∀ c : Fin 1, (coreChunks749_63 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 63)) = true := by
  decide +kernel
#print axioms coreFlatten749_63
#print axioms coreCheck749_63
end Erdos883Verified
