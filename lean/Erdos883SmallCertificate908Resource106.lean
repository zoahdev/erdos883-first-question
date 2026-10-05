import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_106 :
    (List.ofFn coreChunks908_106).flatten =
      (coreData908.take (coreResources908 106).q).drop 184 := by
  decide +kernel

theorem coreCheck908_106 :
    ∀ c : Fin 1, (coreChunks908_106 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 106)) = true := by
  decide +kernel
#print axioms coreFlatten908_106
#print axioms coreCheck908_106
end Erdos883Verified
