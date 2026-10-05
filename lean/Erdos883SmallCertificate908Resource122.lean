import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_122 :
    (List.ofFn coreChunks908_122).flatten =
      (coreData908.take (coreResources908 122).q).drop 206 := by
  decide +kernel

theorem coreCheck908_122 :
    ∀ c : Fin 1, (coreChunks908_122 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 122)) = true := by
  decide +kernel
#print axioms coreFlatten908_122
#print axioms coreCheck908_122
end Erdos883Verified
