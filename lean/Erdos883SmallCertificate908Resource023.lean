import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_23 :
    (List.ofFn coreChunks908_23).flatten =
      (coreData908.take (coreResources908 23).q).drop 170 := by
  decide +kernel

theorem coreCheck908_23 :
    ∀ c : Fin 1, (coreChunks908_23 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 23)) = true := by
  decide +kernel
#print axioms coreFlatten908_23
#print axioms coreCheck908_23
end Erdos883Verified
