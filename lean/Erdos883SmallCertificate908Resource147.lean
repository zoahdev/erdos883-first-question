import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_147 :
    (List.ofFn coreChunks908_147).flatten =
      (coreData908.take (coreResources908 147).q).drop 283 := by
  decide +kernel

theorem coreCheck908_147 :
    ∀ c : Fin 1, (coreChunks908_147 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 147)) = true := by
  decide +kernel
#print axioms coreFlatten908_147
#print axioms coreCheck908_147
end Erdos883Verified
