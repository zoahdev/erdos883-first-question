import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_87 :
    (List.ofFn coreChunks908_87).flatten =
      (coreData908.take (coreResources908 87).q).drop 156 := by
  decide +kernel

theorem coreCheck908_87 :
    ∀ c : Fin 1, (coreChunks908_87 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 87)) = true := by
  decide +kernel
#print axioms coreFlatten908_87
#print axioms coreCheck908_87
end Erdos883Verified
