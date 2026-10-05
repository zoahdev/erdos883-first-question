import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_28 :
    (List.ofFn coreChunks908_28).flatten =
      (coreData908.take (coreResources908 28).q).drop 177 := by
  decide +kernel

theorem coreCheck908_28 :
    ∀ c : Fin 1, (coreChunks908_28 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 28)) = true := by
  decide +kernel
#print axioms coreFlatten908_28
#print axioms coreCheck908_28
end Erdos883Verified
