import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_72 :
    (List.ofFn coreChunks908_72).flatten =
      (coreData908.take (coreResources908 72).q).drop 137 := by
  decide +kernel

theorem coreCheck908_72 :
    ∀ c : Fin 1, (coreChunks908_72 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 72)) = true := by
  decide +kernel
#print axioms coreFlatten908_72
#print axioms coreCheck908_72
end Erdos883Verified
