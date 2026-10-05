import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_116 :
    (List.ofFn coreChunks908_116).flatten =
      (coreData908.take (coreResources908 116).q).drop 200 := by
  decide +kernel

theorem coreCheck908_116 :
    ∀ c : Fin 1, (coreChunks908_116 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 116)) = true := by
  decide +kernel
#print axioms coreFlatten908_116
#print axioms coreCheck908_116
end Erdos883Verified
