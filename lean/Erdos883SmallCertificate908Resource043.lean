import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_43 :
    (List.ofFn coreChunks908_43).flatten =
      (coreData908.take (coreResources908 43).q).drop 196 := by
  decide +kernel

theorem coreCheck908_43 :
    ∀ c : Fin 1, (coreChunks908_43 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 43)) = true := by
  decide +kernel
#print axioms coreFlatten908_43
#print axioms coreCheck908_43
end Erdos883Verified
