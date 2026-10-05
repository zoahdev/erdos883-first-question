import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_17 :
    (List.ofFn coreChunks908_17).flatten =
      (coreData908.take (coreResources908 17).q).drop 164 := by
  decide +kernel

theorem coreCheck908_17 :
    ∀ c : Fin 1, (coreChunks908_17 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 17)) = true := by
  decide +kernel
#print axioms coreFlatten908_17
#print axioms coreCheck908_17
end Erdos883Verified
