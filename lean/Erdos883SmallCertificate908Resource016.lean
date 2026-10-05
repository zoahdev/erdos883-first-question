import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_16 :
    (List.ofFn coreChunks908_16).flatten =
      (coreData908.take (coreResources908 16).q).drop 160 := by
  decide +kernel

theorem coreCheck908_16 :
    ∀ c : Fin 1, (coreChunks908_16 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 16)) = true := by
  decide +kernel
#print axioms coreFlatten908_16
#print axioms coreCheck908_16
end Erdos883Verified
