import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_90 :
    (List.ofFn coreChunks908_90).flatten =
      (coreData908.take (coreResources908 90).q).drop 159 := by
  decide +kernel

theorem coreCheck908_90 :
    ∀ c : Fin 1, (coreChunks908_90 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 90)) = true := by
  decide +kernel
#print axioms coreFlatten908_90
#print axioms coreCheck908_90
end Erdos883Verified
