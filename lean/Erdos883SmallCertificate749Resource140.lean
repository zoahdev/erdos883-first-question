import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_140 :
    (List.ofFn coreChunks749_140).flatten =
      (coreData749.take (coreResources749 140).q).drop 331 := by
  decide +kernel

theorem coreCheck749_140 :
    ∀ c : Fin 1, (coreChunks749_140 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 140)) = true := by
  decide +kernel
#print axioms coreFlatten749_140
#print axioms coreCheck749_140
end Erdos883Verified
