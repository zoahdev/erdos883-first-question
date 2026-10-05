import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_21 :
    (List.ofFn coreChunks908_21).flatten =
      (coreData908.take (coreResources908 21).q).drop 168 := by
  decide +kernel

theorem coreCheck908_21 :
    ∀ c : Fin 1, (coreChunks908_21 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 21)) = true := by
  decide +kernel
#print axioms coreFlatten908_21
#print axioms coreCheck908_21
end Erdos883Verified
