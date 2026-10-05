import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_124 :
    (List.ofFn coreChunks908_124).flatten =
      (coreData908.take (coreResources908 124).q).drop 210 := by
  decide +kernel

theorem coreCheck908_124 :
    ∀ c : Fin 1, (coreChunks908_124 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 124)) = true := by
  decide +kernel
#print axioms coreFlatten908_124
#print axioms coreCheck908_124
end Erdos883Verified
