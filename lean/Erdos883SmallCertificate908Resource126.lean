import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_126 :
    (List.ofFn coreChunks908_126).flatten =
      (coreData908.take (coreResources908 126).q).drop 219 := by
  decide +kernel

theorem coreCheck908_126 :
    ∀ c : Fin 1, (coreChunks908_126 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 126)) = true := by
  decide +kernel
#print axioms coreFlatten908_126
#print axioms coreCheck908_126
end Erdos883Verified
