import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_75 :
    (List.ofFn coreChunks908_75).flatten =
      (coreData908.take (coreResources908 75).q).drop 140 := by
  decide +kernel

theorem coreCheck908_75 :
    ∀ c : Fin 1, (coreChunks908_75 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 75)) = true := by
  decide +kernel
#print axioms coreFlatten908_75
#print axioms coreCheck908_75
end Erdos883Verified
