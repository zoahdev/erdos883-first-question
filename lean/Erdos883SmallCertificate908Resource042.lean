import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_42 :
    (List.ofFn coreChunks908_42).flatten =
      (coreData908.take (coreResources908 42).q).drop 195 := by
  decide +kernel

theorem coreCheck908_42 :
    ∀ c : Fin 1, (coreChunks908_42 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 42)) = true := by
  decide +kernel
#print axioms coreFlatten908_42
#print axioms coreCheck908_42
end Erdos883Verified
