import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_127 :
    (List.ofFn coreChunks908_127).flatten =
      (coreData908.take (coreResources908 127).q).drop 222 := by
  decide +kernel

theorem coreCheck908_127 :
    ∀ c : Fin 1, (coreChunks908_127 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 127)) = true := by
  decide +kernel
#print axioms coreFlatten908_127
#print axioms coreCheck908_127
end Erdos883Verified
