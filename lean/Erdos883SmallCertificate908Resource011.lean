import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_11 :
    (List.ofFn coreChunks908_11).flatten =
      (coreData908.take (coreResources908 11).q).drop 155 := by
  decide +kernel

theorem coreCheck908_11 :
    ∀ c : Fin 1, (coreChunks908_11 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 11)) = true := by
  decide +kernel
#print axioms coreFlatten908_11
#print axioms coreCheck908_11
end Erdos883Verified
