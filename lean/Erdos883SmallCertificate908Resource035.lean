import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_35 :
    (List.ofFn coreChunks908_35).flatten =
      (coreData908.take (coreResources908 35).q).drop 184 := by
  decide +kernel

theorem coreCheck908_35 :
    ∀ c : Fin 1, (coreChunks908_35 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 35)) = true := by
  decide +kernel
#print axioms coreFlatten908_35
#print axioms coreCheck908_35
end Erdos883Verified
