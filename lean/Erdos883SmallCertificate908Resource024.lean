import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_24 :
    (List.ofFn coreChunks908_24).flatten =
      (coreData908.take (coreResources908 24).q).drop 171 := by
  decide +kernel

theorem coreCheck908_24 :
    ∀ c : Fin 1, (coreChunks908_24 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 24)) = true := by
  decide +kernel
#print axioms coreFlatten908_24
#print axioms coreCheck908_24
end Erdos883Verified
