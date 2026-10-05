import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_168 :
    (List.ofFn coreChunks908_168).flatten =
      (coreData908.take (coreResources908 168).q).drop 400 := by
  decide +kernel

theorem coreCheck908_168 :
    ∀ c : Fin 1, (coreChunks908_168 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 168)) = true := by
  decide +kernel
#print axioms coreFlatten908_168
#print axioms coreCheck908_168
end Erdos883Verified
