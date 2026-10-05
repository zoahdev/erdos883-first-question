import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_165 :
    (List.ofFn coreChunks908_165).flatten =
      (coreData908.take (coreResources908 165).q).drop 389 := by
  decide +kernel

theorem coreCheck908_165 :
    ∀ c : Fin 1, (coreChunks908_165 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 165)) = true := by
  decide +kernel
#print axioms coreFlatten908_165
#print axioms coreCheck908_165
end Erdos883Verified
