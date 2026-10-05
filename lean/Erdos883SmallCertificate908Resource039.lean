import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_39 :
    (List.ofFn coreChunks908_39).flatten =
      (coreData908.take (coreResources908 39).q).drop 191 := by
  decide +kernel

theorem coreCheck908_39 :
    ∀ c : Fin 1, (coreChunks908_39 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 39)) = true := by
  decide +kernel
#print axioms coreFlatten908_39
#print axioms coreCheck908_39
end Erdos883Verified
