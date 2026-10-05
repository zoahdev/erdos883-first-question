import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_123 :
    (List.ofFn coreChunks908_123).flatten =
      (coreData908.take (coreResources908 123).q).drop 209 := by
  decide +kernel

theorem coreCheck908_123 :
    ∀ c : Fin 1, (coreChunks908_123 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 123)) = true := by
  decide +kernel
#print axioms coreFlatten908_123
#print axioms coreCheck908_123
end Erdos883Verified
