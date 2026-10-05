import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_18 :
    (List.ofFn coreChunks908_18).flatten =
      (coreData908.take (coreResources908 18).q).drop 165 := by
  decide +kernel

theorem coreCheck908_18 :
    ∀ c : Fin 1, (coreChunks908_18 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 18)) = true := by
  decide +kernel
#print axioms coreFlatten908_18
#print axioms coreCheck908_18
end Erdos883Verified
