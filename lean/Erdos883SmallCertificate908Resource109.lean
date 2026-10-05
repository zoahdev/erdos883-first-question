import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_109 :
    (List.ofFn coreChunks908_109).flatten =
      (coreData908.take (coreResources908 109).q).drop 190 := by
  decide +kernel

theorem coreCheck908_109 :
    ∀ c : Fin 1, (coreChunks908_109 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 109)) = true := by
  decide +kernel
#print axioms coreFlatten908_109
#print axioms coreCheck908_109
end Erdos883Verified
