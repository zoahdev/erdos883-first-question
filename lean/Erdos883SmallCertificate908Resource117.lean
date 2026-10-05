import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_117 :
    (List.ofFn coreChunks908_117).flatten =
      (coreData908.take (coreResources908 117).q).drop 201 := by
  decide +kernel

theorem coreCheck908_117 :
    ∀ c : Fin 1, (coreChunks908_117 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 117)) = true := by
  decide +kernel
#print axioms coreFlatten908_117
#print axioms coreCheck908_117
end Erdos883Verified
