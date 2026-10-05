import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_161 :
    (List.ofFn coreChunks908_161).flatten =
      (coreData908.take (coreResources908 161).q).drop 378 := by
  decide +kernel

theorem coreCheck908_161 :
    ∀ c : Fin 1, (coreChunks908_161 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 161)) = true := by
  decide +kernel
#print axioms coreFlatten908_161
#print axioms coreCheck908_161
end Erdos883Verified
