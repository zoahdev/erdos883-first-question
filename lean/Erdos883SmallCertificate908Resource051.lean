import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_51 :
    (List.ofFn coreChunks908_51).flatten =
      (coreData908.take (coreResources908 51).q).drop 204 := by
  decide +kernel

theorem coreCheck908_51 :
    ∀ c : Fin 1, (coreChunks908_51 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 51)) = true := by
  decide +kernel
#print axioms coreFlatten908_51
#print axioms coreCheck908_51
end Erdos883Verified
