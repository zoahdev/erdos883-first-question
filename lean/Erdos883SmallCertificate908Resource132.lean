import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_132 :
    (List.ofFn coreChunks908_132).flatten =
      (coreData908.take (coreResources908 132).q).drop 231 := by
  decide +kernel

theorem coreCheck908_132 :
    ∀ c : Fin 1, (coreChunks908_132 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 132)) = true := by
  decide +kernel
#print axioms coreFlatten908_132
#print axioms coreCheck908_132
end Erdos883Verified
