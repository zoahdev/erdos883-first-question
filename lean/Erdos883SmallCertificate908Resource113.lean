import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_113 :
    (List.ofFn coreChunks908_113).flatten =
      (coreData908.take (coreResources908 113).q).drop 196 := by
  decide +kernel

theorem coreCheck908_113 :
    ∀ c : Fin 1, (coreChunks908_113 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 113)) = true := by
  decide +kernel
#print axioms coreFlatten908_113
#print axioms coreCheck908_113
end Erdos883Verified
