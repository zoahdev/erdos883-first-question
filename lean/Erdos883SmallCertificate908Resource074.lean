import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_74 :
    (List.ofFn coreChunks908_74).flatten =
      (coreData908.take (coreResources908 74).q).drop 139 := by
  decide +kernel

theorem coreCheck908_74 :
    ∀ c : Fin 1, (coreChunks908_74 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 74)) = true := by
  decide +kernel
#print axioms coreFlatten908_74
#print axioms coreCheck908_74
end Erdos883Verified
