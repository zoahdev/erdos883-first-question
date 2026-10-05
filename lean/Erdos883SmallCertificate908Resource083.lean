import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_83 :
    (List.ofFn coreChunks908_83).flatten =
      (coreData908.take (coreResources908 83).q).drop 150 := by
  decide +kernel

theorem coreCheck908_83 :
    ∀ c : Fin 1, (coreChunks908_83 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 83)) = true := by
  decide +kernel
#print axioms coreFlatten908_83
#print axioms coreCheck908_83
end Erdos883Verified
