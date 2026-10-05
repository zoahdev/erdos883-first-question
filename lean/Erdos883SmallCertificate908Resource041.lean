import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_41 :
    (List.ofFn coreChunks908_41).flatten =
      (coreData908.take (coreResources908 41).q).drop 193 := by
  decide +kernel

theorem coreCheck908_41 :
    ∀ c : Fin 1, (coreChunks908_41 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 41)) = true := by
  decide +kernel
#print axioms coreFlatten908_41
#print axioms coreCheck908_41
end Erdos883Verified
