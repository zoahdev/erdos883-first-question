import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_59 :
    (List.ofFn coreChunks908_59).flatten =
      (coreData908.take (coreResources908 59).q).drop 222 := by
  decide +kernel

theorem coreCheck908_59 :
    ∀ c : Fin 1, (coreChunks908_59 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 59)) = true := by
  decide +kernel
#print axioms coreFlatten908_59
#print axioms coreCheck908_59
end Erdos883Verified
