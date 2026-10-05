import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_94 :
    (List.ofFn coreChunks908_94).flatten =
      (coreData908.take (coreResources908 94).q).drop 167 := by
  decide +kernel

theorem coreCheck908_94 :
    ∀ c : Fin 1, (coreChunks908_94 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 94)) = true := by
  decide +kernel
#print axioms coreFlatten908_94
#print axioms coreCheck908_94
end Erdos883Verified
