import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_79 :
    (List.ofFn coreChunks908_79).flatten =
      (coreData908.take (coreResources908 79).q).drop 144 := by
  decide +kernel

theorem coreCheck908_79 :
    ∀ c : Fin 1, (coreChunks908_79 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 79)) = true := by
  decide +kernel
#print axioms coreFlatten908_79
#print axioms coreCheck908_79
end Erdos883Verified
