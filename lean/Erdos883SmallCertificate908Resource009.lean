import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_9 :
    (List.ofFn coreChunks908_9).flatten =
      (coreData908.take (coreResources908 9).q).drop 152 := by
  decide +kernel

theorem coreCheck908_9 :
    ∀ c : Fin 1, (coreChunks908_9 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 9)) = true := by
  decide +kernel
#print axioms coreFlatten908_9
#print axioms coreCheck908_9
end Erdos883Verified
