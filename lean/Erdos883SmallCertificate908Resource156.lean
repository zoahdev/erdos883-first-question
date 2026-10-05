import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_156 :
    (List.ofFn coreChunks908_156).flatten =
      (coreData908.take (coreResources908 156).q).drop 362 := by
  decide +kernel

theorem coreCheck908_156 :
    ∀ c : Fin 1, (coreChunks908_156 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 156)) = true := by
  decide +kernel
#print axioms coreFlatten908_156
#print axioms coreCheck908_156
end Erdos883Verified
