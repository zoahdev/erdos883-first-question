import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_19 :
    (List.ofFn coreChunks908_19).flatten =
      (coreData908.take (coreResources908 19).q).drop 166 := by
  decide +kernel

theorem coreCheck908_19 :
    ∀ c : Fin 1, (coreChunks908_19 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 19)) = true := by
  decide +kernel
#print axioms coreFlatten908_19
#print axioms coreCheck908_19
end Erdos883Verified
