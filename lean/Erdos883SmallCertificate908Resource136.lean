import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_136 :
    (List.ofFn coreChunks908_136).flatten =
      (coreData908.take (coreResources908 136).q).drop 237 := by
  decide +kernel

theorem coreCheck908_136 :
    ∀ c : Fin 1, (coreChunks908_136 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 136)) = true := by
  decide +kernel
#print axioms coreFlatten908_136
#print axioms coreCheck908_136
end Erdos883Verified
