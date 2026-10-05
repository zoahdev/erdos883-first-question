import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_133 :
    (List.ofFn coreChunks908_133).flatten =
      (coreData908.take (coreResources908 133).q).drop 233 := by
  decide +kernel

theorem coreCheck908_133 :
    ∀ c : Fin 1, (coreChunks908_133 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 133)) = true := by
  decide +kernel
#print axioms coreFlatten908_133
#print axioms coreCheck908_133
end Erdos883Verified
