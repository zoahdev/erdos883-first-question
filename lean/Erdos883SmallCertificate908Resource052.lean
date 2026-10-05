import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_52 :
    (List.ofFn coreChunks908_52).flatten =
      (coreData908.take (coreResources908 52).q).drop 205 := by
  decide +kernel

theorem coreCheck908_52 :
    ∀ c : Fin 1, (coreChunks908_52 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 52)) = true := by
  decide +kernel
#print axioms coreFlatten908_52
#print axioms coreCheck908_52
end Erdos883Verified
