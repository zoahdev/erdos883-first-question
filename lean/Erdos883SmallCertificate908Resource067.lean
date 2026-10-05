import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_67 :
    (List.ofFn coreChunks908_67).flatten =
      (coreData908.take (coreResources908 67).q).drop 124 := by
  decide +kernel

theorem coreCheck908_67 :
    ∀ c : Fin 1, (coreChunks908_67 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 67)) = true := by
  decide +kernel
#print axioms coreFlatten908_67
#print axioms coreCheck908_67
end Erdos883Verified
