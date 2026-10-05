import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_102 :
    (List.ofFn coreChunks908_102).flatten =
      (coreData908.take (coreResources908 102).q).drop 180 := by
  decide +kernel

theorem coreCheck908_102 :
    ∀ c : Fin 1, (coreChunks908_102 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 102)) = true := by
  decide +kernel
#print axioms coreFlatten908_102
#print axioms coreCheck908_102
end Erdos883Verified
