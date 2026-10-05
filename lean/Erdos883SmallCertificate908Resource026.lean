import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_26 :
    (List.ofFn coreChunks908_26).flatten =
      (coreData908.take (coreResources908 26).q).drop 173 := by
  decide +kernel

theorem coreCheck908_26 :
    ∀ c : Fin 1, (coreChunks908_26 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 26)) = true := by
  decide +kernel
#print axioms coreFlatten908_26
#print axioms coreCheck908_26
end Erdos883Verified
