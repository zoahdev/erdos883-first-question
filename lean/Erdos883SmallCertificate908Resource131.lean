import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_131 :
    (List.ofFn coreChunks908_131).flatten =
      (coreData908.take (coreResources908 131).q).drop 229 := by
  decide +kernel

theorem coreCheck908_131 :
    ∀ c : Fin 1, (coreChunks908_131 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 131)) = true := by
  decide +kernel
#print axioms coreFlatten908_131
#print axioms coreCheck908_131
end Erdos883Verified
