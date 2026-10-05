import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_95 :
    (List.ofFn coreChunks908_95).flatten =
      (coreData908.take (coreResources908 95).q).drop 168 := by
  decide +kernel

theorem coreCheck908_95 :
    ∀ c : Fin 1, (coreChunks908_95 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 95)) = true := by
  decide +kernel
#print axioms coreFlatten908_95
#print axioms coreCheck908_95
end Erdos883Verified
