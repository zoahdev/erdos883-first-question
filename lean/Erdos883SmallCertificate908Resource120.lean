import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_120 :
    (List.ofFn coreChunks908_120).flatten =
      (coreData908.take (coreResources908 120).q).drop 204 := by
  decide +kernel

theorem coreCheck908_120 :
    ∀ c : Fin 1, (coreChunks908_120 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 120)) = true := by
  decide +kernel
#print axioms coreFlatten908_120
#print axioms coreCheck908_120
end Erdos883Verified
