import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_57 :
    (List.ofFn coreChunks908_57).flatten =
      (coreData908.take (coreResources908 57).q).drop 217 := by
  decide +kernel

theorem coreCheck908_57 :
    ∀ c : Fin 1, (coreChunks908_57 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 57)) = true := by
  decide +kernel
#print axioms coreFlatten908_57
#print axioms coreCheck908_57
end Erdos883Verified
