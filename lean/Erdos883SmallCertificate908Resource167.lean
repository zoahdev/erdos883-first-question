import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_167 :
    (List.ofFn coreChunks908_167).flatten =
      (coreData908.take (coreResources908 167).q).drop 399 := by
  decide +kernel

theorem coreCheck908_167 :
    ∀ c : Fin 1, (coreChunks908_167 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 167)) = true := by
  decide +kernel
#print axioms coreFlatten908_167
#print axioms coreCheck908_167
end Erdos883Verified
