import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_37 :
    (List.ofFn coreChunks749_37).flatten =
      (coreData749.take (coreResources749 37).q).drop 163 := by
  decide +kernel

theorem coreCheck749_37 :
    ∀ c : Fin 1, (coreChunks749_37 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 37)) = true := by
  decide +kernel
#print axioms coreFlatten749_37
#print axioms coreCheck749_37
end Erdos883Verified
