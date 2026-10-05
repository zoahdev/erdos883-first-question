import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_70 :
    (List.ofFn coreChunks908_70).flatten =
      (coreData908.take (coreResources908 70).q).drop 134 := by
  decide +kernel

theorem coreCheck908_70 :
    ∀ c : Fin 1, (coreChunks908_70 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 70)) = true := by
  decide +kernel
#print axioms coreFlatten908_70
#print axioms coreCheck908_70
end Erdos883Verified
