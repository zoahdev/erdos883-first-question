import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_66 :
    (List.ofFn coreChunks908_66).flatten =
      (coreData908.take (coreResources908 66).q).drop 123 := by
  decide +kernel

theorem coreCheck908_66 :
    ∀ c : Fin 1, (coreChunks908_66 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 66)) = true := by
  decide +kernel
#print axioms coreFlatten908_66
#print axioms coreCheck908_66
end Erdos883Verified
