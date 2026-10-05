import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_115 :
    (List.ofFn coreChunks908_115).flatten =
      (coreData908.take (coreResources908 115).q).drop 199 := by
  decide +kernel

theorem coreCheck908_115 :
    ∀ c : Fin 1, (coreChunks908_115 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 115)) = true := by
  decide +kernel
#print axioms coreFlatten908_115
#print axioms coreCheck908_115
end Erdos883Verified
