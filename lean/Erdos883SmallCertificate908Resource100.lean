import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_100 :
    (List.ofFn coreChunks908_100).flatten =
      (coreData908.take (coreResources908 100).q).drop 175 := by
  decide +kernel

theorem coreCheck908_100 :
    ∀ c : Fin 1, (coreChunks908_100 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 100)) = true := by
  decide +kernel
#print axioms coreFlatten908_100
#print axioms coreCheck908_100
end Erdos883Verified
