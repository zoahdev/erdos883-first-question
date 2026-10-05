import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_10 :
    (List.ofFn coreChunks908_10).flatten =
      (coreData908.take (coreResources908 10).q).drop 154 := by
  decide +kernel

theorem coreCheck908_10 :
    ∀ c : Fin 1, (coreChunks908_10 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 10)) = true := by
  decide +kernel
#print axioms coreFlatten908_10
#print axioms coreCheck908_10
end Erdos883Verified
