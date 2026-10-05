import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_56 :
    (List.ofFn coreChunks908_56).flatten =
      (coreData908.take (coreResources908 56).q).drop 214 := by
  decide +kernel

theorem coreCheck908_56 :
    ∀ c : Fin 1, (coreChunks908_56 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 56)) = true := by
  decide +kernel
#print axioms coreFlatten908_56
#print axioms coreCheck908_56
end Erdos883Verified
