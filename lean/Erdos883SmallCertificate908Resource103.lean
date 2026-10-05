import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_103 :
    (List.ofFn coreChunks908_103).flatten =
      (coreData908.take (coreResources908 103).q).drop 181 := by
  decide +kernel

theorem coreCheck908_103 :
    ∀ c : Fin 1, (coreChunks908_103 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 103)) = true := by
  decide +kernel
#print axioms coreFlatten908_103
#print axioms coreCheck908_103
end Erdos883Verified
