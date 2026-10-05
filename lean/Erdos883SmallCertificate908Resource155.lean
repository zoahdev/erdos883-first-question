import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_155 :
    (List.ofFn coreChunks908_155).flatten =
      (coreData908.take (coreResources908 155).q).drop 355 := by
  decide +kernel

theorem coreCheck908_155 :
    ∀ c : Fin 1, (coreChunks908_155 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 155)) = true := by
  decide +kernel
#print axioms coreFlatten908_155
#print axioms coreCheck908_155
end Erdos883Verified
