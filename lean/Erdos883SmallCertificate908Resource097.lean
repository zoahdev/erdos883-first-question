import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_97 :
    (List.ofFn coreChunks908_97).flatten =
      (coreData908.take (coreResources908 97).q).drop 170 := by
  decide +kernel

theorem coreCheck908_97 :
    ∀ c : Fin 1, (coreChunks908_97 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 97)) = true := by
  decide +kernel
#print axioms coreFlatten908_97
#print axioms coreCheck908_97
end Erdos883Verified
