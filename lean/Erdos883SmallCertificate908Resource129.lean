import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_129 :
    (List.ofFn coreChunks908_129).flatten =
      (coreData908.take (coreResources908 129).q).drop 227 := by
  decide +kernel

theorem coreCheck908_129 :
    ∀ c : Fin 1, (coreChunks908_129 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 129)) = true := by
  decide +kernel
#print axioms coreFlatten908_129
#print axioms coreCheck908_129
end Erdos883Verified
