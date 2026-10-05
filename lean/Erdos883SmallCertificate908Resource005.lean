import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_5 :
    (List.ofFn coreChunks908_5).flatten =
      (coreData908.take (coreResources908 5).q).drop 111 := by
  decide +kernel

theorem coreCheck908_5 :
    ∀ c : Fin 1, (coreChunks908_5 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 5)) = true := by
  decide +kernel
#print axioms coreFlatten908_5
#print axioms coreCheck908_5
end Erdos883Verified
