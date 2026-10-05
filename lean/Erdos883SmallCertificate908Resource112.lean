import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_112 :
    (List.ofFn coreChunks908_112).flatten =
      (coreData908.take (coreResources908 112).q).drop 194 := by
  decide +kernel

theorem coreCheck908_112 :
    ∀ c : Fin 1, (coreChunks908_112 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 112)) = true := by
  decide +kernel
#print axioms coreFlatten908_112
#print axioms coreCheck908_112
end Erdos883Verified
