import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_153 :
    (List.ofFn coreChunks908_153).flatten =
      (coreData908.take (coreResources908 153).q).drop 320 := by
  decide +kernel

theorem coreCheck908_153 :
    ∀ c : Fin 2, (coreChunks908_153 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 153)) = true := by
  decide +kernel
#print axioms coreFlatten908_153
#print axioms coreCheck908_153
end Erdos883Verified
