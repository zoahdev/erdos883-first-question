import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_58 :
    (List.ofFn coreChunks908_58).flatten =
      (coreData908.take (coreResources908 58).q).drop 219 := by
  decide +kernel

theorem coreCheck908_58 :
    ∀ c : Fin 1, (coreChunks908_58 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 58)) = true := by
  decide +kernel
#print axioms coreFlatten908_58
#print axioms coreCheck908_58
end Erdos883Verified
