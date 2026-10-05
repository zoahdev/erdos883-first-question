import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_31 :
    (List.ofFn coreChunks908_31).flatten =
      (coreData908.take (coreResources908 31).q).drop 180 := by
  decide +kernel

theorem coreCheck908_31 :
    ∀ c : Fin 1, (coreChunks908_31 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 31)) = true := by
  decide +kernel
#print axioms coreFlatten908_31
#print axioms coreCheck908_31
end Erdos883Verified
