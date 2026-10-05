import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_128 :
    (List.ofFn coreChunks749_128).flatten =
      (coreData749.take (coreResources749 128).q).drop 282 := by
  decide +kernel

theorem coreCheck749_128 :
    ∀ c : Fin 1, (coreChunks749_128 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 128)) = true := by
  decide +kernel
#print axioms coreFlatten749_128
#print axioms coreCheck749_128
end Erdos883Verified
