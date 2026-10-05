import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_64 :
    (List.ofFn coreChunks908_64).flatten =
      (coreData908.take (coreResources908 64).q).drop 110 := by
  decide +kernel

theorem coreCheck908_64 :
    ∀ c : Fin 1, (coreChunks908_64 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 64)) = true := by
  decide +kernel
#print axioms coreFlatten908_64
#print axioms coreCheck908_64
end Erdos883Verified
