import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_2 :
    (List.ofFn coreChunks908_2).flatten =
      (coreData908.take (coreResources908 2).q).drop 98 := by
  decide +kernel

theorem coreCheck908_2 :
    ∀ c : Fin 1, (coreChunks908_2 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 2)) = true := by
  decide +kernel
#print axioms coreFlatten908_2
#print axioms coreCheck908_2
end Erdos883Verified
