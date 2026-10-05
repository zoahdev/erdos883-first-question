import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_3 :
    (List.ofFn coreChunks908_3).flatten =
      (coreData908.take (coreResources908 3).q).drop 99 := by
  decide +kernel

theorem coreCheck908_3 :
    ∀ c : Fin 1, (coreChunks908_3 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 3)) = true := by
  decide +kernel
#print axioms coreFlatten908_3
#print axioms coreCheck908_3
end Erdos883Verified
