import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_7 :
    (List.ofFn coreChunks908_7).flatten =
      (coreData908.take (coreResources908 7).q).drop 119 := by
  decide +kernel

theorem coreCheck908_7 :
    ∀ c : Fin 1, (coreChunks908_7 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 7)) = true := by
  decide +kernel
#print axioms coreFlatten908_7
#print axioms coreCheck908_7
end Erdos883Verified
