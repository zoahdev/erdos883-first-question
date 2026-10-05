import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_81 :
    (List.ofFn coreChunks908_81).flatten =
      (coreData908.take (coreResources908 81).q).drop 146 := by
  decide +kernel

theorem coreCheck908_81 :
    ∀ c : Fin 1, (coreChunks908_81 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 81)) = true := by
  decide +kernel
#print axioms coreFlatten908_81
#print axioms coreCheck908_81
end Erdos883Verified
