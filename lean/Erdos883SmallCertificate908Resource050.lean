import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_50 :
    (List.ofFn coreChunks908_50).flatten =
      (coreData908.take (coreResources908 50).q).drop 203 := by
  decide +kernel

theorem coreCheck908_50 :
    ∀ c : Fin 1, (coreChunks908_50 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 50)) = true := by
  decide +kernel
#print axioms coreFlatten908_50
#print axioms coreCheck908_50
end Erdos883Verified
