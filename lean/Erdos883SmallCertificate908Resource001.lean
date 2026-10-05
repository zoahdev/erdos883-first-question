import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_1 :
    (List.ofFn coreChunks908_1).flatten =
      (coreData908.take (coreResources908 1).q).drop 77 := by
  decide +kernel

theorem coreCheck908_1 :
    ∀ c : Fin 2, (coreChunks908_1 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 1)) = true := by
  decide +kernel
#print axioms coreFlatten908_1
#print axioms coreCheck908_1
end Erdos883Verified
