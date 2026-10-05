import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_158 :
    (List.ofFn coreChunks908_158).flatten =
      (coreData908.take (coreResources908 158).q).drop 369 := by
  decide +kernel

theorem coreCheck908_158 :
    ∀ c : Fin 1, (coreChunks908_158 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 158)) = true := by
  decide +kernel
#print axioms coreFlatten908_158
#print axioms coreCheck908_158
end Erdos883Verified
