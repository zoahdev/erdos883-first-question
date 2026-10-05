import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_108 :
    (List.ofFn coreChunks908_108).flatten =
      (coreData908.take (coreResources908 108).q).drop 188 := by
  decide +kernel

theorem coreCheck908_108 :
    ∀ c : Fin 1, (coreChunks908_108 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 108)) = true := by
  decide +kernel
#print axioms coreFlatten908_108
#print axioms coreCheck908_108
end Erdos883Verified
