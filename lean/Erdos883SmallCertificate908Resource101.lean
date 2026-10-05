import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_101 :
    (List.ofFn coreChunks908_101).flatten =
      (coreData908.take (coreResources908 101).q).drop 177 := by
  decide +kernel

theorem coreCheck908_101 :
    ∀ c : Fin 1, (coreChunks908_101 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 101)) = true := by
  decide +kernel
#print axioms coreFlatten908_101
#print axioms coreCheck908_101
end Erdos883Verified
