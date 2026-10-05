import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_157 :
    (List.ofFn coreChunks908_157).flatten =
      (coreData908.take (coreResources908 157).q).drop 368 := by
  decide +kernel

theorem coreCheck908_157 :
    ∀ c : Fin 1, (coreChunks908_157 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 157)) = true := by
  decide +kernel
#print axioms coreFlatten908_157
#print axioms coreCheck908_157
end Erdos883Verified
