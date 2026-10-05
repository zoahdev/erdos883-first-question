import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_98 :
    (List.ofFn coreChunks908_98).flatten =
      (coreData908.take (coreResources908 98).q).drop 171 := by
  decide +kernel

theorem coreCheck908_98 :
    ∀ c : Fin 1, (coreChunks908_98 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 98)) = true := by
  decide +kernel
#print axioms coreFlatten908_98
#print axioms coreCheck908_98
end Erdos883Verified
