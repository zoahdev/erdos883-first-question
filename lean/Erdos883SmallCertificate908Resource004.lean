import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_4 :
    (List.ofFn coreChunks908_4).flatten =
      (coreData908.take (coreResources908 4).q).drop 110 := by
  decide +kernel

theorem coreCheck908_4 :
    ∀ c : Fin 1, (coreChunks908_4 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 4)) = true := by
  decide +kernel
#print axioms coreFlatten908_4
#print axioms coreCheck908_4
end Erdos883Verified
