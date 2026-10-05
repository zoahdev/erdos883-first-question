import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_40 :
    (List.ofFn coreChunks908_40).flatten =
      (coreData908.take (coreResources908 40).q).drop 192 := by
  decide +kernel

theorem coreCheck908_40 :
    ∀ c : Fin 1, (coreChunks908_40 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 40)) = true := by
  decide +kernel
#print axioms coreFlatten908_40
#print axioms coreCheck908_40
end Erdos883Verified
