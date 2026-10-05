import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_118 :
    (List.ofFn coreChunks908_118).flatten =
      (coreData908.take (coreResources908 118).q).drop 202 := by
  decide +kernel

theorem coreCheck908_118 :
    ∀ c : Fin 1, (coreChunks908_118 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 118)) = true := by
  decide +kernel
#print axioms coreFlatten908_118
#print axioms coreCheck908_118
end Erdos883Verified
