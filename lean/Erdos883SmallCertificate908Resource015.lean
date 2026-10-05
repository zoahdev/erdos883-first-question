import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_15 :
    (List.ofFn coreChunks908_15).flatten =
      (coreData908.take (coreResources908 15).q).drop 159 := by
  decide +kernel

theorem coreCheck908_15 :
    ∀ c : Fin 1, (coreChunks908_15 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 15)) = true := by
  decide +kernel
#print axioms coreFlatten908_15
#print axioms coreCheck908_15
end Erdos883Verified
