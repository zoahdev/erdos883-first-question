import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_160 :
    (List.ofFn coreChunks908_160).flatten =
      (coreData908.take (coreResources908 160).q).drop 372 := by
  decide +kernel

theorem coreCheck908_160 :
    ∀ c : Fin 1, (coreChunks908_160 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 160)) = true := by
  decide +kernel
#print axioms coreFlatten908_160
#print axioms coreCheck908_160
end Erdos883Verified
