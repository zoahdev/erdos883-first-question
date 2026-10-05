import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_29 :
    (List.ofFn coreChunks908_29).flatten =
      (coreData908.take (coreResources908 29).q).drop 178 := by
  decide +kernel

theorem coreCheck908_29 :
    ∀ c : Fin 1, (coreChunks908_29 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 29)) = true := by
  decide +kernel
#print axioms coreFlatten908_29
#print axioms coreCheck908_29
end Erdos883Verified
