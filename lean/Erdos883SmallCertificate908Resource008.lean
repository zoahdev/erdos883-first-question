import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_8 :
    (List.ofFn coreChunks908_8).flatten =
      (coreData908.take (coreResources908 8).q).drop 120 := by
  decide +kernel

theorem coreCheck908_8 :
    ∀ c : Fin 2, (coreChunks908_8 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 8)) = true := by
  decide +kernel
#print axioms coreFlatten908_8
#print axioms coreCheck908_8
end Erdos883Verified
