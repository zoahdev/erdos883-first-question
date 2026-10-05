import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_84 :
    (List.ofFn coreChunks908_84).flatten =
      (coreData908.take (coreResources908 84).q).drop 152 := by
  decide +kernel

theorem coreCheck908_84 :
    ∀ c : Fin 1, (coreChunks908_84 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 84)) = true := by
  decide +kernel
#print axioms coreFlatten908_84
#print axioms coreCheck908_84
end Erdos883Verified
