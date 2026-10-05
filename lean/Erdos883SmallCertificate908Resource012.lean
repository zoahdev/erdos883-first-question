import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_12 :
    (List.ofFn coreChunks908_12).flatten =
      (coreData908.take (coreResources908 12).q).drop 156 := by
  decide +kernel

theorem coreCheck908_12 :
    ∀ c : Fin 1, (coreChunks908_12 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 12)) = true := by
  decide +kernel
#print axioms coreFlatten908_12
#print axioms coreCheck908_12
end Erdos883Verified
