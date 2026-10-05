import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_36 :
    (List.ofFn coreChunks908_36).flatten =
      (coreData908.take (coreResources908 36).q).drop 185 := by
  decide +kernel

theorem coreCheck908_36 :
    ∀ c : Fin 1, (coreChunks908_36 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 36)) = true := by
  decide +kernel
#print axioms coreFlatten908_36
#print axioms coreCheck908_36
end Erdos883Verified
