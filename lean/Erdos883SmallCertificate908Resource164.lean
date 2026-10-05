import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_164 :
    (List.ofFn coreChunks908_164).flatten =
      (coreData908.take (coreResources908 164).q).drop 385 := by
  decide +kernel

theorem coreCheck908_164 :
    ∀ c : Fin 1, (coreChunks908_164 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 164)) = true := by
  decide +kernel
#print axioms coreFlatten908_164
#print axioms coreCheck908_164
end Erdos883Verified
