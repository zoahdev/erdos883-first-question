import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_22 :
    (List.ofFn coreChunks908_22).flatten =
      (coreData908.take (coreResources908 22).q).drop 169 := by
  decide +kernel

theorem coreCheck908_22 :
    ∀ c : Fin 1, (coreChunks908_22 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 22)) = true := by
  decide +kernel
#print axioms coreFlatten908_22
#print axioms coreCheck908_22
end Erdos883Verified
