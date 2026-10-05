import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_33 :
    (List.ofFn coreChunks908_33).flatten =
      (coreData908.take (coreResources908 33).q).drop 182 := by
  decide +kernel

theorem coreCheck908_33 :
    ∀ c : Fin 1, (coreChunks908_33 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 33)) = true := by
  decide +kernel
#print axioms coreFlatten908_33
#print axioms coreCheck908_33
end Erdos883Verified
