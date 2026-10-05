import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_80 :
    (List.ofFn coreChunks908_80).flatten =
      (coreData908.take (coreResources908 80).q).drop 145 := by
  decide +kernel

theorem coreCheck908_80 :
    ∀ c : Fin 1, (coreChunks908_80 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 80)) = true := by
  decide +kernel
#print axioms coreFlatten908_80
#print axioms coreCheck908_80
end Erdos883Verified
